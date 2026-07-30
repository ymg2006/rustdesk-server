use crate::common::*;
use crate::peer::*;
use hbb_common::{
    allow_err, bail,
    bytes::{Bytes, BytesMut},
    bytes_codec::BytesCodec,
    config,
    futures::future::join_all,
    futures_util::{
        sink::SinkExt,
        stream::{SplitSink, StreamExt},
    },
    log,
    protobuf::{Message as _, MessageField},
    rendezvous_proto::{
        register_pk_response::Result::{INVALID_ID_FORMAT, TOO_FREQUENT, UUID_MISMATCH},
        *,
    },
    sodiumoxide::crypto::{box_, box_::PublicKey, box_::SecretKey, secretbox, sign},
    sodiumoxide::hex,
    tcp::Encrypt,
    tcp::FramedStream,
    timeout,
    tokio::{
        self,
        io::{AsyncReadExt, AsyncWriteExt},
        net::{TcpListener, TcpStream},
        sync::{mpsc, Mutex},
        time::{interval, Duration},
    },
    tokio_util::codec::Framed,
    try_into_v4,
    udp::FramedSocket,
    AddrMangle, ResultType,
};
use ipnetwork::Ipv4Network;

use crate::jwt;
use std::{
    collections::HashMap,
    net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr},
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
    sync::Arc,
    time::Instant,
};

#[derive(Clone, Debug)]
enum Data {
    Msg(Box<RendezvousMessage>, SocketAddr),
    RelayServers0(String),
    RelayLoads(HashMap<String, i32>),
    RelayServers(RelayServers),
}

const REG_TIMEOUT: i64 = 30_000;
type TcpStreamSink = SplitSink<Framed<TcpStream, BytesCodec>, Bytes>;
type WsSink = SplitSink<tokio_tungstenite::WebSocketStream<TcpStream>, tungstenite::Message>;
struct SafeWsSink {
    sink: WsSink,
    encrypt: Option<Encrypt>,
}

struct SafeTcpStreamSink {
    sink: TcpStreamSink,
    encrypt: Option<Encrypt>,
}
enum Sink {
    // TcpStream(TcpStreamSink),
    // Ws(WsSink),
    Wss(SafeWsSink),
    Tss(SafeTcpStreamSink),
}

impl Sink {
    async fn send(&mut self, msg: &RendezvousMessage) {
        if let Ok(mut bytes) = msg.write_to_bytes() {
            match self {
                // Sink::TcpStream(mut s) => allow_err!(s.send(Bytes::from(bytes)).await),
                // Sink::Ws(mut s) => allow_err!(s.send(tungstenite::Message::Binary(bytes)).await),
                Sink::Wss(s) => {
                    if let Some(key) = s.encrypt.as_mut() {
                        bytes = key.enc(&bytes);
                    }
                    allow_err!(s.sink.send(tungstenite::Message::Binary(bytes)).await)
                }
                Sink::Tss(s) => {
                    if let Some(key) = s.encrypt.as_mut() {
                        bytes = key.enc(&bytes);
                    }
                    allow_err!(s.sink.send(Bytes::from(bytes)).await)
                }
            }
        }
    }
}
type Sender = mpsc::UnboundedSender<Data>;
type Receiver = mpsc::UnboundedReceiver<Data>;
static ROTATION_RELAY_SERVER: AtomicUsize = AtomicUsize::new(0);
type RelayServers = Vec<String>;
#[derive(Clone, Debug, PartialEq, Eq)]
struct RelayInfo {
    address: String,
    capacity: i32,
}
type RelayInfos = Vec<RelayInfo>;
/// Cached load: (host_with_port, connections)
type RelayLoads = Arc<Mutex<HashMap<String, i32>>>;
const CHECK_RELAY_TIMEOUT: u64 = 3_000;
static ALWAYS_USE_RELAY: AtomicBool = AtomicBool::new(false);

fn set_always_use_relay(value: &str) -> Result<(), ()> {
    match value.to_ascii_uppercase().as_str() {
        "Y" => {
            ALWAYS_USE_RELAY.store(true, Ordering::SeqCst);
            Ok(())
        }
        "N" => {
            ALWAYS_USE_RELAY.store(false, Ordering::SeqCst);
            Ok(())
        }
        _ => Err(()),
    }
}

fn parse_relay_entry(value: &str) -> Option<RelayInfo> {
    let value = value.trim();
    if value.is_empty() {
        return None;
    }
    let (address, capacity) = if value.starts_with('[') {
        let bracket = value.find(']')?;
        let ip = &value[1..bracket];
        ip.parse::<Ipv6Addr>().ok()?;
        let suffix = &value[bracket + 1..];
        let parts: Vec<&str> = suffix.strip_prefix(':')?.split(':').collect();
        match parts.as_slice() {
            [port] => {
                port.parse::<u16>().ok()?;
                (value.to_owned(), 100)
            }
            [port, capacity] => {
                port.parse::<u16>().ok()?;
                (format!("[{}]:{}", ip, port), capacity.parse::<i32>().ok()?)
            }
            _ => return None,
        }
    } else {
        let colon_count = value.bytes().filter(|byte| *byte == b':').count();
        match colon_count {
            0 => (value.to_owned(), 100),
            1 => {
                let (host, port) = value.rsplit_once(':')?;
                if host.is_empty() {
                    return None;
                }
                port.parse::<u16>().ok()?;
                (value.to_owned(), 100)
            }
            2 => {
                let (address, capacity) = value.rsplit_once(':')?;
                let (host, port) = address.rsplit_once(':')?;
                if host.is_empty() {
                    return None;
                }
                port.parse::<u16>().ok()?;
                (address.to_owned(), capacity.parse::<i32>().ok()?)
            }
            _ => return None,
        }
    };
    if capacity <= 0 {
        return None;
    }
    Some(RelayInfo { address, capacity })
}

fn relay_connect_address(address: &str) -> String {
    if address.starts_with('[') || address.matches(':').count() == 1 {
        address.to_owned()
    } else {
        format!("{}:{}", address, config::RELAY_PORT)
    }
}

fn normalize_relay_entries(relay_servers: &str) -> RelayInfos {
    let mut infos = Vec::new();
    for entry in relay_servers.split(',') {
        match parse_relay_entry(entry) {
            Some(info)
                if !infos
                    .iter()
                    .any(|item: &RelayInfo| item.address == info.address) =>
            {
                infos.push(info);
            }
            Some(_) => {}
            None if !entry.trim().is_empty() => {
                log::warn!("Ignoring malformed relay server entry");
            }
            None => {}
        }
    }
    infos
}

// Store punch hole requests
use once_cell::sync::Lazy;
use tokio::sync::Mutex as TokioMutex; // differentiate if needed
#[derive(Clone)]
struct PunchReqEntry {
    tm: Instant,
    from_ip: String,
    to_ip: String,
    to_id: String,
}
static PUNCH_REQS: Lazy<TokioMutex<Vec<PunchReqEntry>>> = Lazy::new(|| TokioMutex::new(Vec::new()));
const PUNCH_REQ_DEDUPE_SEC: u64 = 60;
static MUST_LOGIN: AtomicBool = AtomicBool::new(false);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConnectionAuthError {
    LicenseMismatch,
    LoginRequired,
    InvalidToken,
    ServerMisconfigured,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KeyExchangeError {
    InvalidKeyCount,
    InvalidPublicKeyLength,
    InvalidCiphertextLength,
    DecryptionFailed,
    InvalidSymmetricKeyLength,
}

fn validate_connection_auth(
    supplied_licence_key: &str,
    supplied_token: &str,
    configured_licence_key: &str,
    must_login: bool,
) -> Result<(), ConnectionAuthError> {
    validate_connection_auth_with(
        supplied_licence_key,
        supplied_token,
        configured_licence_key,
        must_login,
        jwt::is_configured(),
        |token| jwt::verify_token(token).is_ok(),
    )
}

fn validate_connection_auth_with(
    supplied_licence_key: &str,
    supplied_token: &str,
    configured_licence_key: &str,
    must_login: bool,
    jwt_configured: bool,
    verify_token: impl FnOnce(&str) -> bool,
) -> Result<(), ConnectionAuthError> {
    if !configured_licence_key.is_empty() && supplied_licence_key != configured_licence_key {
        return Err(ConnectionAuthError::LicenseMismatch);
    }
    if !must_login {
        return Ok(());
    }
    if !jwt_configured {
        return Err(ConnectionAuthError::ServerMisconfigured);
    }
    if supplied_token.is_empty() {
        return Err(ConnectionAuthError::LoginRequired);
    }
    if verify_token(supplied_token) {
        Ok(())
    } else {
        Err(ConnectionAuthError::InvalidToken)
    }
}

#[derive(Clone)]
struct Inner {
    serial: i32,
    version: String,
    software_url: String,
    mask: Vec<Ipv4Network>,
    local_ip: String,
    sk: Option<sign::SecretKey>,
    secure_tcp_pk_b: PublicKey,
    secure_tcp_sk_b: SecretKey,
}

#[derive(Clone)]
pub struct RendezvousServer {
    tcp_punch: Arc<Mutex<HashMap<SocketAddr, Sink>>>,
    pm: PeerMap,
    tx: Sender,
    relay_servers: Arc<RelayServers>,
    relay_servers0: Arc<RelayServers>,
    relay_infos: RelayInfos,
    relay_loads: RelayLoads,
    rendezvous_servers: Arc<Vec<String>>,
    inner: Arc<Inner>,
    ws_map: Arc<Mutex<HashMap<SocketAddr, Sink>>>,
}

enum LoopFailure {
    UdpSocket,
    Listener3,
    Listener2,
    Listener,
    ConsoleListener,
}

impl RendezvousServer {
    pub fn start(port: i32, serial: i32, key: &str, rmem: usize) -> ResultType<()> {
        Self::start_with_bind(None, port, serial, key, rmem)
    }

    #[tokio::main(flavor = "multi_thread")]
    pub async fn start_with_bind(
        bind_addr: Option<IpAddr>,
        port: i32,
        serial: i32,
        key: &str,
        rmem: usize,
    ) -> ResultType<()> {
        let (key, sk) = Self::get_server_sk(key);
        let nat_port = port - 1;
        let ws_port = port + 2;
        let pm = PeerMap::new().await?;
        log::info!("serial={}", serial);
        let rendezvous_servers = get_servers(&get_arg("rendezvous-servers"), "rendezvous-servers");
        let mut socket = create_udp_listener(bind_addr, port, rmem).await?;
        let (tx, mut rx) = mpsc::unbounded_channel::<Data>();
        let software_url = get_arg("software-url");
        let version = hbb_common::get_version_from_url(&software_url);
        if !version.is_empty() {
            log::info!("software_url: {}, version: {}", software_url, version);
        }
        let mask: Vec<Ipv4Network> = get_arg("mask")
            .split(',')
            .filter_map(|s| s.trim().parse().ok())
            .collect();
        let local_ip = if mask.is_empty() {
            "".to_owned()
        } else {
            get_arg_or(
                "local-ip",
                local_ip_address::local_ip()
                    .map(|x| x.to_string())
                    .unwrap_or_default(),
            )
        };
        // For privacy use per connection key pair
        let (secure_tcp_pk_b, secure_tcp_sk_b) = box_::gen_keypair();
        let mut rs = Self {
            tcp_punch: Arc::new(Mutex::new(HashMap::new())),
            pm,
            tx: tx.clone(),
            relay_servers: Default::default(),
            relay_servers0: Default::default(),
            relay_infos: Default::default(),
            relay_loads: Default::default(),
            rendezvous_servers: Arc::new(rendezvous_servers),
            inner: Arc::new(Inner {
                serial,
                version,
                software_url,
                sk,
                mask,
                local_ip,
                secure_tcp_pk_b,
                secure_tcp_sk_b,
            }),
            ws_map: Arc::new(Mutex::new(HashMap::new())),
        };
        log::info!("masks ({}): {:?}", rs.inner.mask.len(), rs.inner.mask);
        log::info!("local-ip: {:?}", rs.inner.local_ip);
        std::env::set_var("PORT_FOR_API", port.to_string());
        rs.parse_relay_servers(&get_arg("relay-servers"));
        let mut listener = create_tcp_listener(bind_addr, port).await?;
        let mut listener2 = create_tcp_listener(bind_addr, nat_port).await?;
        let mut listener3 = create_tcp_listener(bind_addr, ws_port).await?;
        let mut listener_console = listen_console(bind_addr, nat_port as _).await?;
        log::info!("Listening on tcp/udp {}", listener.local_addr()?);
        log::info!(
            "Listening on tcp {}, extra port for NAT test",
            listener2.local_addr()?
        );
        log::info!("Listening on websocket {}", listener3.local_addr()?);
        let test_addr = get_arg("TEST_HBBS");
        if get_arg("ALWAYS_USE_RELAY").to_uppercase() == "Y" {
            ALWAYS_USE_RELAY.store(true, Ordering::SeqCst);
        }
        log::info!(
            "ALWAYS_USE_RELAY={}",
            if ALWAYS_USE_RELAY.load(Ordering::SeqCst) {
                "Y"
            } else {
                "N"
            }
        );

        let must_login = get_arg("must-login");
        log::debug!("must_login={}", must_login);
        if must_login.to_uppercase() == "Y"
            || (must_login == ""
                && std::env::var("MUST_LOGIN")
                    .unwrap_or_default()
                    .to_uppercase()
                    == "Y")
        {
            MUST_LOGIN.store(true, Ordering::SeqCst);
        }

        log::info!(
            "MUST_LOGIN={}",
            if MUST_LOGIN.load(Ordering::SeqCst) {
                "Y"
            } else {
                "N"
            }
        );
        if MUST_LOGIN.load(Ordering::SeqCst) && !jwt::is_configured() {
            bail!("MUST_LOGIN=Y requires a non-empty RUSTDESK_API_JWT_KEY");
        }
        if test_addr.to_lowercase() != "no" {
            let test_addr = if test_addr.is_empty() {
                listener.local_addr()?
            } else {
                test_addr.parse()?
            };
            tokio::spawn(async move {
                if let Err(err) = test_hbbs(test_addr).await {
                    if test_addr.is_ipv6() && test_addr.ip().is_unspecified() {
                        let mut test_addr = test_addr;
                        test_addr.set_ip(IpAddr::V4(Ipv4Addr::UNSPECIFIED));
                        if let Err(err) = test_hbbs(test_addr).await {
                            log::error!("Failed to run hbbs test with {test_addr}: {err}");
                            std::process::exit(1);
                        }
                    } else {
                        log::error!("Failed to run hbbs test with {test_addr}: {err}");
                        std::process::exit(1);
                    }
                }
            });
        };
        let main_task = async move {
            loop {
                log::info!("Start");
                match rs
                    .io_loop(
                        &mut rx,
                        &mut listener,
                        &mut listener2,
                        &mut listener3,
                        &mut listener_console,
                        &mut socket,
                        &key,
                    )
                    .await
                {
                    LoopFailure::UdpSocket => {
                        drop(socket);
                        socket = create_udp_listener(bind_addr, port, rmem).await?;
                    }
                    LoopFailure::Listener => {
                        drop(listener);
                        listener = create_tcp_listener(bind_addr, port).await?;
                    }
                    LoopFailure::Listener2 => {
                        drop(listener2);
                        listener2 = create_tcp_listener(bind_addr, nat_port).await?;
                    }
                    LoopFailure::ConsoleListener => {
                        drop(listener_console.take());
                        listener_console = listen_console(bind_addr, nat_port as _).await?;
                    }
                    LoopFailure::Listener3 => {
                        drop(listener3);
                        listener3 = create_tcp_listener(bind_addr, ws_port).await?;
                    }
                }
            }
        };
        let listen_signal = listen_signal();
        tokio::select!(
            res = main_task => res,
            res = listen_signal => res,
        )
    }

    async fn io_loop(
        &mut self,
        rx: &mut Receiver,
        listener: &mut TcpListener,
        listener2: &mut TcpListener,
        listener3: &mut TcpListener,
        listener_console: &mut Option<TcpListener>,
        socket: &mut FramedSocket,
        key: &str,
    ) -> LoopFailure {
        let mut timer_check_relay = interval(Duration::from_millis(CHECK_RELAY_TIMEOUT));
        loop {
            tokio::select! {
                _ = timer_check_relay.tick() => {
                    if self.relay_servers0.len() > 1 {
                        let rs = self.relay_servers0.clone();
                        let tx = self.tx.clone();
                        tokio::spawn(async move {
                            check_relay_servers(rs, tx).await;
                        });
                    }
                }
                Some(data) = rx.recv() => {
                    match data {
                        Data::Msg(msg, addr) => { allow_err!(socket.send(msg.as_ref(), addr).await); }
                        Data::RelayServers0(rs) => { self.parse_relay_servers(&rs); }
                        Data::RelayServers(rs) => { self.relay_servers = Arc::new(rs); }
                        Data::RelayLoads(loads) => { *self.relay_loads.lock().await = loads; }
                    }
                }
                res = socket.next() => {
                    match res {
                        Some(Ok((bytes, addr))) => {
                            if let Err(err) = self.handle_udp(&bytes, addr.into(), socket, key).await {
                                log::error!("udp failure: {}", err);
                                return LoopFailure::UdpSocket;
                            }
                        }
                        Some(Err(err)) => {
                            log::error!("udp failure: {}", err);
                            return LoopFailure::UdpSocket;
                        }
                        None => {
                            // unreachable!() ?
                        }
                    }
                }
                res = listener2.accept() => {
                    match res {
                        Ok((stream, addr))  => {
                            stream.set_nodelay(true).ok();
                            self.handle_listener2(stream, addr).await;
                        }
                        Err(err) => {
                           log::error!("listener2.accept failed: {}", err);
                           return LoopFailure::Listener2;
                        }
                    }
                }
                res = accept_or_pending(listener_console.as_ref()) => {
                    match res {
                        Ok((stream, addr))  => {
                            stream.set_nodelay(true).ok();
                            self.handle_listener2(stream, addr).await;
                        }
                        Err(err) => {
                           log::error!("console listener.accept failed: {}", err);
                           return LoopFailure::ConsoleListener;
                        }
                    }
                }
                res = listener3.accept() => {
                    match res {
                        Ok((stream, addr))  => {
                            stream.set_nodelay(true).ok();
                            self.handle_listener(stream, addr, key, true).await;
                        }
                        Err(err) => {
                           log::error!("listener3.accept failed: {}", err);
                           return LoopFailure::Listener3;
                        }
                    }
                }
                res = listener.accept() => {
                    match res {
                        Ok((stream, addr)) => {
                            stream.set_nodelay(true).ok();
                            self.handle_listener(stream, addr, key, false).await;
                        }
                       Err(err) => {
                           log::error!("listener.accept failed: {}", err);
                           return LoopFailure::Listener;
                       }
                    }
                }
            }
        }
    }

    #[inline]
    async fn handle_udp(
        &mut self,
        bytes: &BytesMut,
        addr: SocketAddr,
        socket: &mut FramedSocket,
        key: &str,
    ) -> ResultType<()> {
        if let Ok(msg_in) = RendezvousMessage::parse_from_bytes(bytes) {
            match msg_in.union {
                Some(rendezvous_message::Union::RegisterPeer(rp)) => {
                    // B registered
                    if !rp.id.is_empty() {
                        log::trace!("New peer registered: {:?} {:?}", &rp.id, &addr);
                        let request_pk = self.update_addr(rp.id, addr).await;
                        let mut msg_out = RendezvousMessage::new();
                        msg_out.set_register_peer_response(RegisterPeerResponse {
                            request_pk,
                            ..Default::default()
                        });
                        socket.send(&msg_out, addr).await?;
                        if self.inner.serial > rp.serial {
                            let mut msg_out = RendezvousMessage::new();
                            msg_out.set_configure_update(ConfigUpdate {
                                serial: self.inner.serial,
                                rendezvous_servers: (*self.rendezvous_servers).clone(),
                                ..Default::default()
                            });
                            socket.send(&msg_out, addr).await?;
                        }
                    }
                }
                Some(rendezvous_message::Union::RegisterPk(rk)) => {
                    let response = self.handle_register_pk(rk, addr, false).await;
                    match response {
                        Err(err) => {
                            let mut msg_out = RendezvousMessage::new();
                            msg_out.set_register_pk_response(RegisterPkResponse {
                                result: err.into(),
                                ..Default::default()
                            });
                            socket.send(&msg_out, addr).await?;
                        }
                        Ok(res) => {
                            let mut msg_out = RendezvousMessage::new();
                            msg_out.set_register_pk_response(RegisterPkResponse {
                                result: res.into(),
                                ..Default::default()
                            });
                            socket.send(&msg_out, addr).await?;
                        }
                    }
                }
                Some(rendezvous_message::Union::PunchHoleRequest(ph)) => {
                    if self.pm.is_in_memory(&ph.id).await {
                        self.handle_udp_punch_hole_request(addr, ph, key).await?;
                    } else {
                        // not in memory, fetch from db with spawn in case blocking me
                        let mut me = self.clone();
                        let key = key.to_owned();
                        tokio::spawn(async move {
                            allow_err!(me.handle_udp_punch_hole_request(addr, ph, &key).await);
                        });
                    }
                }
                Some(rendezvous_message::Union::PunchHoleSent(_phs)) => {
                    // UDP PunchHoleSent is intentionally unsupported to avoid UDP reflection/amplification
                }
                Some(rendezvous_message::Union::LocalAddr(_la)) => {
                    // UDP LocalAddr is intentionally unsupported to avoid UDP reflection/amplification
                }
                Some(rendezvous_message::Union::ConfigureUpdate(mut cu)) => {
                    if try_into_v4(addr).ip().is_loopback() && cu.serial > self.inner.serial {
                        let mut inner: Inner = (*self.inner).clone();
                        inner.serial = cu.serial;
                        self.inner = Arc::new(inner);
                        self.rendezvous_servers = Arc::new(
                            cu.rendezvous_servers
                                .drain(..)
                                .filter(|x| {
                                    !x.is_empty()
                                        && test_if_valid_server(x, "rendezvous-server").is_ok()
                                })
                                .collect(),
                        );
                        log::info!(
                            "configure updated: serial={} rendezvous-servers={:?}",
                            self.inner.serial,
                            self.rendezvous_servers
                        );
                    }
                }
                Some(rendezvous_message::Union::SoftwareUpdate(su)) => {
                    if !self.inner.version.is_empty() && su.url != self.inner.version {
                        let mut msg_out = RendezvousMessage::new();
                        msg_out.set_software_update(SoftwareUpdate {
                            url: self.inner.software_url.clone(),
                            ..Default::default()
                        });
                        socket.send(&msg_out, addr).await?;
                    }
                }
                Some(rendezvous_message::Union::TestNatRequest(tar)) => {
                    // CRITICAL: respond to TestNatRequest over UDP so the client
                    // can learn its NAT external port for the punch socket.
                    // Without this, the client's test_udp_uat always reports
                    // port=0, causing it to fall back to TCP punch and breaking
                    // Phase 3 relay upgrade (Phase 3 STUN reports a different
                    // port than the actual punch socket, so the peer's packets
                    // never reach us).
                    let mut res = TestNatResponse {
                        port: addr.port() as _,
                        ..Default::default()
                    };
                    if self.inner.serial > tar.serial {
                        let mut cu = ConfigUpdate::new();
                        cu.serial = self.inner.serial;
                        cu.rendezvous_servers = (*self.rendezvous_servers).clone();
                        res.cu = MessageField::from_option(Some(cu));
                    }
                    let mut msg_out = RendezvousMessage::new();
                    msg_out.set_test_nat_response(res);
                    socket.send(&msg_out, addr).await?;
                }
                _ => {}
            }
        }
        Ok(())
    }

    #[inline]
    async fn handle_tcp(
        &mut self,
        bytes: &[u8],
        sink: &mut Option<Sink>,
        addr: SocketAddr,
        key: &str,
        ws: bool,
    ) -> bool {
        if let Ok(msg_in) = RendezvousMessage::parse_from_bytes(bytes) {
            // log::debug!("Received TCP message from {}: {:?}", addr, msg_in);
            match msg_in.union {
                Some(rendezvous_message::Union::RegisterPeer(rp)) => {
                    // B registered
                    if !rp.id.is_empty() {
                        log::trace!("New peer registered: {:?} {:?}", &rp.id, &addr);
                        let request_pk = self.update_addr(rp.id, addr).await;
                        let mut msg_out = RendezvousMessage::new();
                        msg_out.set_register_peer_response(RegisterPeerResponse {
                            request_pk,
                            ..Default::default()
                        });
                        Self::send_to_sink(sink, msg_out).await;
                        if self.inner.serial > rp.serial {
                            let mut msg_out = RendezvousMessage::new();
                            msg_out.set_configure_update(ConfigUpdate {
                                serial: self.inner.serial,
                                rendezvous_servers: (*self.rendezvous_servers).clone(),
                                ..Default::default()
                            });
                            Self::send_to_sink(sink, msg_out).await;
                        }
                    }
                }
                Some(rendezvous_message::Union::PunchHoleRequest(ph)) => {
                    // there maybe several attempt, so sink can be none
                    if let Some(sink) = sink.take() {
                        self.tcp_punch.lock().await.insert(try_into_v4(addr), sink);
                    }
                    allow_err!(self.handle_tcp_punch_hole_request(addr, ph, key, ws).await);
                    return true;
                }
                Some(rendezvous_message::Union::RequestRelay(mut rf)) => {
                    if let Err(err) = validate_connection_auth(
                        &rf.licence_key,
                        &rf.token,
                        key,
                        MUST_LOGIN.load(Ordering::SeqCst),
                    ) {
                        self.tcp_punch.lock().await.remove(&try_into_v4(addr));
                        log::warn!(
                            "Relay request authorization failed from {} for peer {}: {:?}",
                            addr,
                            rf.id,
                            err
                        );
                        return false;
                    }
                    // there maybe several attempt, so sink can be none
                    if let Some(sink) = sink.take() {
                        self.tcp_punch.lock().await.insert(try_into_v4(addr), sink);
                    }
                    if let Some(peer) = self.pm.get_in_memory(&rf.id).await {
                        let mut msg_out = RendezvousMessage::new();
                        rf.socket_addr = AddrMangle::encode(addr).into();
                        msg_out.set_request_relay(rf);
                        let peer_addr = peer.read().await.socket_addr;
                        self.tx.send(Data::Msg(msg_out.into(), peer_addr)).ok();
                    }
                    return true;
                }
                Some(rendezvous_message::Union::RelayResponse(mut rr)) => {
                    let addr_b = AddrMangle::decode(&rr.socket_addr);
                    rr.socket_addr = Default::default();
                    let id = rr.id();
                    if !id.is_empty() {
                        let pk = self.get_pk(&rr.version, id.to_owned()).await;
                        rr.set_pk(pk);
                    }
                    let mut msg_out = RendezvousMessage::new();
                    if !rr.relay_server.is_empty() {
                        if self.is_lan(addr_b) {
                            // https://github.com/rustdesk/rustdesk-server/issues/24
                            rr.relay_server = self.inner.local_ip.clone();
                        } else if rr.relay_server == self.inner.local_ip {
                            rr.relay_server = self.get_relay_server(addr.ip(), addr_b.ip()).await;
                        }
                    }
                    msg_out.set_relay_response(rr);
                    allow_err!(self.send_to_tcp_sync(msg_out, addr_b).await);
                }
                Some(rendezvous_message::Union::PunchHoleSent(phs)) => {
                    allow_err!(self.handle_hole_sent(phs, addr, None).await);
                }
                Some(rendezvous_message::Union::LocalAddr(la)) => {
                    allow_err!(self.handle_local_addr(la, addr, None).await);
                }
                Some(rendezvous_message::Union::TestNatRequest(tar)) => {
                    let mut msg_out = RendezvousMessage::new();
                    let mut res = TestNatResponse {
                        port: addr.port() as _,
                        ..Default::default()
                    };
                    if self.inner.serial > tar.serial {
                        let mut cu = ConfigUpdate::new();
                        cu.serial = self.inner.serial;
                        cu.rendezvous_servers = (*self.rendezvous_servers).clone();
                        res.cu = MessageField::from_option(Some(cu));
                    }
                    msg_out.set_test_nat_response(res);
                    Self::send_to_sink(sink, msg_out).await;
                }
                Some(rendezvous_message::Union::RegisterPk(rk)) => {
                    let response = self.handle_register_pk(rk, addr, ws).await;
                    match response {
                        Err(err) => {
                            let mut msg_out = RendezvousMessage::new();
                            msg_out.set_register_pk_response(RegisterPkResponse {
                                result: err.into(),
                                ..Default::default()
                            });
                            Self::send_to_sink(sink, msg_out).await;
                            return false;
                        }
                        Ok(res) => {
                            let mut msg_out = RendezvousMessage::new();
                            msg_out.set_register_pk_response(RegisterPkResponse {
                                result: res.into(),
                                ..Default::default()
                            });
                            Self::send_to_sink(sink, msg_out).await;
                            if ws {
                                // for ws, we can only get addr when register_pk
                                if let Some(sink) = sink.take() {
                                    self.ws_map.lock().await.insert(try_into_v4(addr), sink);
                                }
                            }
                            return true;
                        }
                    }
                }
                Some(rendezvous_message::Union::KeyExchange(ex)) => {
                    if ws {
                        log::warn!(
                            "Rejecting KeyExchange received over WebSocket from {}",
                            addr
                        );
                        return false;
                    }
                    match derive_key_from_exchange(&ex, self.inner.secure_tcp_sk_b.0) {
                        Ok(key) => {
                            if let Some(Sink::Tss(s)) = sink.as_mut() {
                                s.encrypt = Some(Encrypt::new(key));
                                log::debug!("KeyExchange symmetric key successfully derived");
                                return true;
                            }
                            log::warn!("KeyExchange completed without a TCP sink for {}", addr);
                            return false;
                        }
                        Err(err) => {
                            log::warn!("Invalid KeyExchange from {}: {:?}", addr, err);
                            return false;
                        }
                    }
                }
                Some(rendezvous_message::Union::OnlineRequest(or)) => {
                    let states = self.peers_online_state(or.peers).await;
                    let mut msg_out = RendezvousMessage::new();
                    msg_out.set_online_response(OnlineResponse {
                        states: states.into(),
                        ..Default::default()
                    });
                    Self::send_to_sink(sink, msg_out).await;
                }
                _ => {}
            }
        }
        false
    }

    async fn peers_online_state(&mut self, peers: Vec<String>) -> BytesMut {
        let mut states = BytesMut::zeroed((peers.len() + 7) / 8);
        for (i, peer_id) in peers.iter().enumerate() {
            if let Some(peer) = self.pm.get_in_memory(peer_id).await {
                let elapsed = peer.read().await.last_reg_time.elapsed().as_millis() as i64;
                // bytes index from left to right
                let states_idx = i / 8;
                let bit_idx = 7 - i % 8;
                if elapsed < REG_TIMEOUT {
                    states[states_idx] |= 0x01 << bit_idx;
                }
            }
        }
        states
    }

    async fn handle_register_pk(
        &mut self,
        rk: RegisterPk,
        addr: SocketAddr,
        ws: bool,
    ) -> Result<register_pk_response::Result, register_pk_response::Result> {
        if rk.uuid.is_empty() || rk.pk.is_empty() {
            return Err(INVALID_ID_FORMAT);
        }
        let id = rk.id;
        let ip = addr.ip().to_string();
        if id.len() < 6 {
            return Err(UUID_MISMATCH);
            //return Err(send_rk_res(socket, addr, UUID_MISMATCH).await);
        } else if !self.check_ip_blocker(&ip, &id).await {
            return Err(TOO_FREQUENT);
            //return Err(send_rk_res(socket, addr, TOO_FREQUENT).await);
        }
        let peer = self.pm.get_or(&id).await;
        let (changed, ip_changed) = {
            let peer = peer.read().await;
            if peer.uuid.is_empty() {
                (true, false)
            } else {
                if peer.uuid == rk.uuid {
                    if peer.info.ip != ip && peer.pk != rk.pk {
                        log::warn!(
                            "Peer {} ip/pk mismatch: {}/{:?} vs {}/{:?}",
                            id,
                            ip,
                            rk.pk,
                            peer.info.ip,
                            peer.pk,
                        );
                        drop(peer);
                        return Err(UUID_MISMATCH);
                        //return Err(send_rk_res(socket, addr, UUID_MISMATCH).await);
                    }
                } else {
                    log::warn!(
                        "Peer {} uuid mismatch: {:?} vs {:?}",
                        id,
                        rk.uuid,
                        peer.uuid
                    );
                    drop(peer);
                    return Err(UUID_MISMATCH);
                    //return Err(send_rk_res(socket, addr, UUID_MISMATCH).await);
                }
                let ip_changed = peer.info.ip != ip;
                (
                    peer.uuid != rk.uuid || peer.pk != rk.pk || ip_changed,
                    ip_changed,
                )
            }
        };
        let mut req_pk = peer.read().await.reg_pk;
        if req_pk.1.elapsed().as_secs() > 6 {
            req_pk.0 = 0;
        } else if req_pk.0 > 2 {
            return Err(TOO_FREQUENT);
            //return Err(send_rk_res(socket, addr, TOO_FREQUENT).await);
        }
        req_pk.0 += 1;
        req_pk.1 = Instant::now();
        peer.write().await.reg_pk = req_pk;
        if ip_changed {
            let mut lock = IP_CHANGES.lock().await;
            if let Some((tm, ips)) = lock.get_mut(&id) {
                if tm.elapsed().as_secs() > IP_CHANGE_DUR {
                    *tm = Instant::now();
                    ips.clear();
                    ips.insert(ip.clone(), 1);
                } else if let Some(v) = ips.get_mut(&ip) {
                    *v += 1;
                } else {
                    ips.insert(ip.clone(), 1);
                }
            } else {
                lock.insert(
                    id.clone(),
                    (Instant::now(), HashMap::from([(ip.clone(), 1)])),
                );
            }
        }
        if changed || ws {
            // update peer info，解决tcp过程中不更新在线时间的问题
            self.pm.update_pk(id, peer, addr, rk.uuid, rk.pk, ip).await;
        }
        Ok(register_pk_response::Result::OK)
        // let mut msg_out = RendezvousMessage::new();
        // msg_out.set_register_pk_response(RegisterPkResponse {
        //     result: register_pk_response::Result::OK.into(),
        //     ..Default::default()
        // });
        // Ok(msg_out)
    }

    #[inline]
    async fn update_addr(&mut self, id: String, socket_addr: SocketAddr) -> bool {
        let (request_pk, ip_change) = if let Some(old) = self.pm.get_in_memory(&id).await {
            let mut old = old.write().await;
            let ip = socket_addr.ip();
            let ip_change = if old.socket_addr.port() != 0 {
                ip != old.socket_addr.ip()
            } else {
                ip.to_string() != old.info.ip
            } && !ip.is_loopback();
            let request_pk = old.pk.is_empty() || ip_change;
            if !request_pk {
                old.socket_addr = socket_addr;
                old.last_reg_time = Instant::now();
            }
            let ip_change = if ip_change && old.reg_pk.0 <= 2 {
                Some(if old.socket_addr.port() == 0 {
                    old.info.ip.clone()
                } else {
                    old.socket_addr.to_string()
                })
            } else {
                None
            };
            (request_pk, ip_change)
        } else {
            (true, None)
        };
        if let Some(old) = ip_change {
            log::info!("IP change of {} from {} to {}", id, old, socket_addr);
        }
        request_pk
        // let mut msg_out = RendezvousMessage::new();
        // msg_out.set_register_peer_response(RegisterPeerResponse {
        //     request_pk,
        //     ..Default::default()
        // });
        // socket.send(&msg_out, socket_addr).await
    }

    #[inline]
    async fn handle_hole_sent<'a>(
        &mut self,
        phs: PunchHoleSent,
        addr: SocketAddr,
        socket: Option<&'a mut FramedSocket>,
    ) -> ResultType<()> {
        // punch hole sent from B, tell A that B is ready to be connected
        let addr_a = AddrMangle::decode(&phs.socket_addr);
        log::debug!(
            "{} punch hole response to {:?} from {:?}",
            if socket.is_none() { "TCP" } else { "UDP" },
            &addr_a,
            &addr
        );
        let mut msg_out = RendezvousMessage::new();
        let mut p = PunchHoleResponse {
            socket_addr: AddrMangle::encode(addr).into(),
            pk: self.get_pk(&phs.version, phs.id).await,
            relay_server: phs.relay_server.clone(),
            is_udp: socket.is_some(),
            ..Default::default()
        };
        if let Ok(t) = phs.nat_type.enum_value() {
            p.set_nat_type(t);
        }
        msg_out.set_punch_hole_response(p);
        if let Some(socket) = socket {
            socket.send(&msg_out, addr_a).await?;
        } else {
            self.send_to_tcp(msg_out, addr_a).await;
        }
        Ok(())
    }

    #[inline]
    async fn handle_local_addr<'a>(
        &mut self,
        la: LocalAddr,
        addr: SocketAddr,
        socket: Option<&'a mut FramedSocket>,
    ) -> ResultType<()> {
        // relay local addrs of B to A
        let addr_a = AddrMangle::decode(&la.socket_addr);
        log::debug!(
            "{} local addrs response to {:?} from {:?}",
            if socket.is_none() { "TCP" } else { "UDP" },
            &addr_a,
            &addr
        );
        let mut msg_out = RendezvousMessage::new();
        let mut p = PunchHoleResponse {
            socket_addr: la.local_addr,
            pk: self.get_pk(&la.version, la.id).await,
            relay_server: la.relay_server,
            ..Default::default()
        };
        p.set_is_local(true);
        msg_out.set_punch_hole_response(p);
        if let Some(socket) = socket {
            socket.send(&msg_out, addr_a).await?;
        } else {
            self.send_to_tcp(msg_out, addr_a).await;
        }
        Ok(())
    }

    #[inline]
    async fn handle_punch_hole_request(
        &mut self,
        addr: SocketAddr,
        ph: PunchHoleRequest,
        key: &str,
        ws: bool,
    ) -> ResultType<(RendezvousMessage, Option<SocketAddr>)> {
        let mut ph = ph;
        match validate_connection_auth(
            &ph.licence_key,
            &ph.token,
            key,
            MUST_LOGIN.load(Ordering::SeqCst),
        ) {
            Ok(()) => {}
            Err(ConnectionAuthError::LicenseMismatch) => {
                log::warn!(
                    "Authentication failed from {} for peer {} - invalid key",
                    addr,
                    ph.id
                );
                let mut msg_out = RendezvousMessage::new();
                msg_out.set_punch_hole_response(PunchHoleResponse {
                    failure: punch_hole_response::Failure::LICENSE_MISMATCH.into(),
                    ..Default::default()
                });
                return Ok((msg_out, None));
            }
            Err(ConnectionAuthError::LoginRequired) => {
                let mut msg_out = RendezvousMessage::new();
                msg_out.set_punch_hole_response(PunchHoleResponse {
                    other_failure: String::from("Connection failed, please login!"),
                    ..Default::default()
                });
                return Ok((msg_out, None));
            }
            Err(ConnectionAuthError::InvalidToken) => {
                let mut msg_out = RendezvousMessage::new();
                msg_out.set_punch_hole_response(PunchHoleResponse {
                    other_failure: String::from("Token error, please log out and log back in!"),
                    ..Default::default()
                });
                return Ok((msg_out, None));
            }
            Err(ConnectionAuthError::ServerMisconfigured) => {
                log::error!("Connection authorization is enabled without a JWT secret");
                let mut msg_out = RendezvousMessage::new();
                msg_out.set_punch_hole_response(PunchHoleResponse {
                    other_failure: String::from("Connection authentication is unavailable"),
                    ..Default::default()
                });
                return Ok((msg_out, None));
            }
        }
        let id = ph.id;
        // punch hole request from A, relay to B,
        // check if in same intranet first,
        // fetch local addrs if in same intranet.
        // because punch hole won't work if in the same intranet,
        // all routers will drop such self-connections.
        if let Some(peer) = self.pm.get(&id).await {
            let (elapsed, peer_addr) = {
                let r = peer.read().await;
                (r.last_reg_time.elapsed().as_millis() as i64, r.socket_addr)
            };
            log::info!(
                "PunchHoleRequest for id={} forwarding to peer_addr={} (elapsed={}ms)",
                id,
                peer_addr,
                elapsed
            );
            if elapsed >= REG_TIMEOUT {
                let mut msg_out = RendezvousMessage::new();
                msg_out.set_punch_hole_response(PunchHoleResponse {
                    failure: punch_hole_response::Failure::OFFLINE.into(),
                    ..Default::default()
                });
                return Ok((msg_out, None));
            }

            // record punch hole request (from addr -> peer id/peer_addr)
            {
                let from_ip = try_into_v4(addr).ip().to_string();
                let to_ip = try_into_v4(peer_addr).ip().to_string();
                let to_id_clone = id.clone();
                let mut lock = PUNCH_REQS.lock().await;
                let mut dup = false;
                for e in lock.iter().rev().take(30) {
                    // only check recent tail subset for speed
                    if e.from_ip == from_ip && e.to_id == to_id_clone {
                        if e.tm.elapsed().as_secs() < PUNCH_REQ_DEDUPE_SEC {
                            dup = true;
                        }
                        break;
                    }
                }
                if !dup {
                    lock.push(PunchReqEntry {
                        tm: Instant::now(),
                        from_ip,
                        to_ip,
                        to_id: to_id_clone,
                    });
                }
            }

            let mut msg_out = RendezvousMessage::new();
            let is_lan = self.is_lan(addr);
            let peer_is_lan = self.is_lan(peer_addr);
            let mut relay_server = self.get_relay_server(addr.ip(), peer_addr.ip()).await;
            // If A reported local_addrs and is_lan became true via those, we
            // cannot trust peer_is_lan (which only checks B's connection IP).
            // B might be in the same VPN but behind a different public IP.
            // Only force relay when both is_lan values are based on connection IPs.
            if ALWAYS_USE_RELAY.load(Ordering::SeqCst) || (peer_is_lan ^ is_lan) {
                if peer_is_lan {
                    // https://github.com/rustdesk/rustdesk-server/issues/24
                    relay_server = self.inner.local_ip.clone()
                }
                ph.nat_type = NatType::SYMMETRIC.into(); // will force relay
            }
            let same_intranet: bool = !ws
                && (peer_is_lan && is_lan || {
                    match (peer_addr, addr) {
                        (SocketAddr::V4(a), SocketAddr::V4(b)) => a.ip() == b.ip(),
                        (SocketAddr::V6(a), SocketAddr::V6(b)) => a.ip() == b.ip(),
                        _ => false,
                    }
                });
            let socket_addr = AddrMangle::encode(addr).into();
            if same_intranet {
                log::debug!(
                    "Fetch local addr {:?} {:?} request from {:?}",
                    id,
                    peer_addr,
                    addr
                );
                msg_out.set_fetch_local_addr(FetchLocalAddr {
                    socket_addr,
                    relay_server,
                    ..Default::default()
                });
            } else {
                log::debug!(
                    "Punch hole {:?} {:?} request from {:?}",
                    id,
                    peer_addr,
                    addr
                );
                msg_out.set_punch_hole(PunchHole {
                    socket_addr,
                    nat_type: ph.nat_type,
                    relay_server,
                    udp_port: ph.udp_port,
                    force_relay: ph.force_relay,
                    upnp_port: ph.upnp_port,
                    ..Default::default()
                });
            }
            //
            Ok((msg_out, Some(peer_addr)))
        } else {
            let mut msg_out = RendezvousMessage::new();
            msg_out.set_punch_hole_response(PunchHoleResponse {
                failure: punch_hole_response::Failure::ID_NOT_EXIST.into(),
                ..Default::default()
            });
            Ok((msg_out, None))
        }
    }

    #[inline]
    async fn handle_online_request(
        &mut self,
        stream: &mut FramedStream,
        peers: Vec<String>,
    ) -> ResultType<()> {
        let states = self.peers_online_state(peers).await;

        let mut msg_out = RendezvousMessage::new();
        msg_out.set_online_response(OnlineResponse {
            states: states.into(),
            ..Default::default()
        });
        stream.send(&msg_out).await?;

        Ok(())
    }

    #[inline]
    async fn send_to_tcp(&mut self, msg: RendezvousMessage, addr: SocketAddr) {
        let mut tcp = self.tcp_punch.lock().await.remove(&try_into_v4(addr));
        tokio::spawn(async move {
            Self::send_to_sink(&mut tcp, msg).await;
        });
    }

    #[inline]
    async fn send_to_sink(sink: &mut Option<Sink>, msg: RendezvousMessage) {
        if let Some(sink) = sink.as_mut() {
            sink.send(&msg).await;
        }
    }

    #[inline]
    async fn send_to_tcp_sync(
        &mut self,
        msg: RendezvousMessage,
        addr: SocketAddr,
    ) -> ResultType<()> {
        let mut sink = self.tcp_punch.lock().await.remove(&try_into_v4(addr));
        Self::send_to_sink(&mut sink, msg).await;
        Ok(())
    }

    #[inline]
    async fn handle_tcp_punch_hole_request(
        &mut self,
        addr: SocketAddr,
        ph: PunchHoleRequest,
        key: &str,
        ws: bool,
    ) -> ResultType<()> {
        let (msg, to_addr) = self.handle_punch_hole_request(addr, ph, key, ws).await?;
        if let Some(addr) = to_addr {
            let mut sink = self.ws_map.lock().await.remove(&try_into_v4(addr));
            if let Some(s) = sink.as_mut() {
                s.send(&msg).await;
            } else {
                self.tx.send(Data::Msg(msg.into(), addr))?;
            }
        } else {
            self.send_to_tcp_sync(msg, addr).await?;
        }
        Ok(())
    }

    #[inline]
    async fn handle_udp_punch_hole_request(
        &mut self,
        addr: SocketAddr,
        ph: PunchHoleRequest,
        key: &str,
    ) -> ResultType<()> {
        let (msg, to_addr) = self.handle_punch_hole_request(addr, ph, key, false).await?;
        self.tx.send(Data::Msg(
            msg.into(),
            match to_addr {
                Some(addr) => addr,
                None => addr,
            },
        ))?;
        Ok(())
    }

    async fn check_ip_blocker(&self, ip: &str, id: &str) -> bool {
        let mut lock = IP_BLOCKER.lock().await;
        let now = Instant::now();
        if let Some(old) = lock.get_mut(ip) {
            let counter = &mut old.0;
            if counter.1.elapsed().as_secs() > IP_BLOCK_DUR {
                counter.0 = 0;
            } else if counter.0 > 30 {
                return false;
            }
            counter.0 += 1;
            counter.1 = now;

            let counter = &mut old.1;
            let is_new = counter.0.get(id).is_none();
            if counter.1.elapsed().as_secs() > DAY_SECONDS {
                counter.0.clear();
            } else if counter.0.len() > 300 {
                return !is_new;
            }
            if is_new {
                counter.0.insert(id.to_owned());
            }
            counter.1 = now;
        } else {
            lock.insert(ip.to_owned(), ((0, now), (Default::default(), now)));
        }
        true
    }

    fn parse_relay_servers(&mut self, relay_servers: &str) {
        let infos = normalize_relay_entries(relay_servers);
        let rs: Vec<String> = infos.iter().map(|info| info.address.clone()).collect();
        self.relay_servers0 = Arc::new(rs.clone());
        self.relay_servers = self.relay_servers0.clone();
        self.relay_infos = infos;
    }

    async fn get_relay_server(&self, _pa: IpAddr, _pb: IpAddr) -> String {
        if self.relay_servers.is_empty() {
            return "".to_owned();
        } else if self.relay_servers.len() == 1 {
            return self.relay_servers[0].clone();
        }
        let loads = self.relay_loads.lock().await.clone();
        let known: Vec<(&str, i32, i32)> = self
            .relay_servers
            .iter()
            .filter_map(|address| {
                let info = self
                    .relay_infos
                    .iter()
                    .find(|info| info.address == *address)?;
                loads
                    .get(&relay_connect_address(address))
                    .copied()
                    .map(|load| (address.as_str(), load, info.capacity))
            })
            .collect();
        let mut candidates: Vec<&str> = if known.is_empty() {
            self.relay_servers.iter().map(String::as_str).collect()
        } else {
            let under: Vec<_> = known
                .iter()
                .copied()
                .filter(|(_, load, capacity)| i64::from(*load) * 10 < i64::from(*capacity) * 8)
                .collect();
            let pool = if under.is_empty() { &known } else { &under };
            let best = pool
                .iter()
                .map(|(_, load, capacity)| (i64::from(*load), i64::from(*capacity)))
                .min_by(|(load_a, cap_a), (load_b, cap_b)| (load_a * cap_b).cmp(&(load_b * cap_a)));
            pool.iter()
                .filter(|(_, load, capacity)| {
                    best.is_some_and(|(best_load, best_capacity)| {
                        i64::from(*load) * best_capacity == best_load * i64::from(*capacity)
                    })
                })
                .map(|(address, _, _)| *address)
                .collect()
        };
        if candidates.is_empty() {
            return String::new();
        }
        let i = ROTATION_RELAY_SERVER.fetch_add(1, Ordering::SeqCst) % candidates.len();
        candidates.swap_remove(i).to_string()
    }

    async fn check_cmd(&self, cmd: &str) -> String {
        use std::fmt::Write as _;

        let mut res = "".to_owned();
        let mut fds = cmd.trim().split(' ');
        match fds.next() {
            Some("h") => {
                res = format!(
                    "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n",
                    "relay-servers(rs) <separated by ,>",
                    "reload-geo(rg)",
                    "ip-blocker(ib) [<ip>|<number>] [-]",
                    "ip-changes(ic) [<id>|<number>] [-]",
                    "punch-requests(pr) [<number>] [-]",
                    "always-use-relay(aur) [Y|N]",
                    "test-geo(tg) <ip1> <ip2>",
                    "must-login(ml) [Y|N]",
                )
            }
            Some("relay-servers" | "rs") => {
                if let Some(rs) = fds.next() {
                    self.tx.send(Data::RelayServers0(rs.to_owned())).ok();
                } else {
                    for ip in self.relay_servers.iter() {
                        let _ = writeln!(res, "{ip}");
                    }
                }
            }
            Some("ip-blocker" | "ib") => {
                let mut lock = IP_BLOCKER.lock().await;
                lock.retain(|&_, (a, b)| {
                    a.1.elapsed().as_secs() <= IP_BLOCK_DUR
                        || b.1.elapsed().as_secs() <= DAY_SECONDS
                });
                res = format!("{}\n", lock.len());
                let ip = fds.next();
                let mut start = ip.map(|x| x.parse::<i32>().unwrap_or(-1)).unwrap_or(-1);
                if start < 0 {
                    if let Some(ip) = ip {
                        if let Some((a, b)) = lock.get(ip) {
                            let _ = writeln!(
                                res,
                                "{}/{}s {}/{}s",
                                a.0,
                                a.1.elapsed().as_secs(),
                                b.0.len(),
                                b.1.elapsed().as_secs()
                            );
                        }
                        if fds.next() == Some("-") {
                            lock.remove(ip);
                        }
                    } else {
                        start = 0;
                    }
                }
                if start >= 0 {
                    let mut it = lock.iter();
                    for i in 0..(start + 10) {
                        let x = it.next();
                        if x.is_none() {
                            break;
                        }
                        if i < start {
                            continue;
                        }
                        if let Some((ip, (a, b))) = x {
                            let _ = writeln!(
                                res,
                                "{}: {}/{}s {}/{}s",
                                ip,
                                a.0,
                                a.1.elapsed().as_secs(),
                                b.0.len(),
                                b.1.elapsed().as_secs()
                            );
                        }
                    }
                }
            }
            Some("ip-changes" | "ic") => {
                let mut lock = IP_CHANGES.lock().await;
                lock.retain(|&_, v| v.0.elapsed().as_secs() < IP_CHANGE_DUR_X2 && v.1.len() > 1);
                res = format!("{}\n", lock.len());
                let id = fds.next();
                let mut start = id.map(|x| x.parse::<i32>().unwrap_or(-1)).unwrap_or(-1);
                if !(0..=10_000_000).contains(&start) {
                    if let Some(id) = id {
                        if let Some((tm, ips)) = lock.get(id) {
                            let _ = writeln!(res, "{}s {:?}", tm.elapsed().as_secs(), ips);
                        }
                        if fds.next() == Some("-") {
                            lock.remove(id);
                        }
                    } else {
                        start = 0;
                    }
                }
                if start >= 0 {
                    let mut it = lock.iter();
                    for i in 0..(start + 10) {
                        let x = it.next();
                        if x.is_none() {
                            break;
                        }
                        if i < start {
                            continue;
                        }
                        if let Some((id, (tm, ips))) = x {
                            let _ = writeln!(res, "{}: {}s {:?}", id, tm.elapsed().as_secs(), ips,);
                        }
                    }
                }
            }
            Some("punch-requests" | "pr") => {
                use std::fmt::Write as _;
                let mut lock = PUNCH_REQS.lock().await;
                let arg = fds.next();
                if let Some("-") = arg {
                    lock.clear();
                } else {
                    let start = arg.and_then(|x| x.parse::<usize>().ok()).unwrap_or(0);
                    let mut page_size = fds
                        .next()
                        .and_then(|x| x.parse::<usize>().ok())
                        .unwrap_or(10);
                    if page_size == 0 {
                        page_size = 10;
                    }
                    for (_, e) in lock.iter().enumerate().skip(start).take(page_size) {
                        let age = e.tm.elapsed();
                        let event_system = std::time::SystemTime::now() - age;
                        let event_iso = chrono::DateTime::<chrono::Utc>::from(event_system)
                            .to_rfc3339_opts(chrono::SecondsFormat::Secs, true);
                        let _ = writeln!(
                            res,
                            "{} {} -> {}@{}",
                            event_iso, e.from_ip, e.to_id, e.to_ip
                        );
                    }
                }
            }
            Some("always-use-relay" | "aur") => {
                if let Some(rs) = fds.next() {
                    if set_always_use_relay(rs).is_err() {
                        let _ = writeln!(res, "Usage: always-use-relay [Y|N]");
                    }
                } else {
                    let _ = writeln!(
                        res,
                        "ALWAYS_USE_RELAY: {:?}",
                        ALWAYS_USE_RELAY.load(Ordering::SeqCst)
                    );
                }
            }
            Some("test-geo" | "tg") => {
                if let Some(rs) = fds.next() {
                    if let Ok(a) = rs.parse::<IpAddr>() {
                        if let Some(rs) = fds.next() {
                            if let Ok(b) = rs.parse::<IpAddr>() {
                                res = format!("{:?}", self.get_relay_server(a, b).await);
                            }
                        } else {
                            res = format!("{:?}", self.get_relay_server(a, a).await);
                        }
                    }
                }
            }
            Some("must-login" | "ml") => {
                if let Some(rs) = fds.next() {
                    if rs.to_uppercase() == "Y" {
                        if jwt::is_configured() {
                            MUST_LOGIN.store(true, Ordering::SeqCst);
                        } else {
                            let _ = writeln!(
                                res,
                                "Cannot enable MUST_LOGIN: RUSTDESK_API_JWT_KEY is empty"
                            );
                        }
                    } else {
                        MUST_LOGIN.store(false, Ordering::SeqCst);
                    }
                } else {
                    let _ = writeln!(res, "MUST_LOGIN: {:?}", MUST_LOGIN.load(Ordering::SeqCst));
                }
            }
            _ => {}
        }
        res
    }

    async fn handle_listener2(&self, stream: TcpStream, addr: SocketAddr) {
        let mut rs = self.clone();
        let ip = try_into_v4(addr).ip();
        if ip.is_loopback() {
            tokio::spawn(async move {
                let mut stream = stream;
                let mut buffer = [0; 1024];
                if let Ok(Ok(n)) = timeout(1000, stream.read(&mut buffer[..])).await {
                    if let Ok(data) = std::str::from_utf8(&buffer[..n]) {
                        let res = rs.check_cmd(data).await;
                        stream.write(res.as_bytes()).await.ok();
                    }
                }
            });
            return;
        }
        let stream = FramedStream::from(stream, addr);
        tokio::spawn(async move {
            let mut stream = stream;
            if let Some(Ok(bytes)) = stream.next_timeout(30_000).await {
                if let Ok(msg_in) = RendezvousMessage::parse_from_bytes(&bytes) {
                    match msg_in.union {
                        Some(rendezvous_message::Union::TestNatRequest(_)) => {
                            let mut msg_out = RendezvousMessage::new();
                            msg_out.set_test_nat_response(TestNatResponse {
                                port: addr.port() as _,
                                ..Default::default()
                            });
                            stream.send(&msg_out).await.ok();
                        }
                        Some(rendezvous_message::Union::OnlineRequest(or)) => {
                            allow_err!(rs.handle_online_request(&mut stream, or.peers).await);
                        }
                        _ => {}
                    }
                }
            }
        });
    }

    async fn handle_listener(&self, stream: TcpStream, addr: SocketAddr, key: &str, ws: bool) {
        log::debug!("Tcp connection from {:?}, ws: {}", addr, ws);
        let mut rs = self.clone();
        let key = key.to_owned();
        tokio::spawn(async move {
            allow_err!(rs.handle_listener_inner(stream, addr, &key, ws).await);
        });
    }

    #[inline]
    async fn handle_listener_inner(
        &mut self,
        stream: TcpStream,
        mut addr: SocketAddr,
        key: &str,
        ws: bool,
    ) -> ResultType<()> {
        let mut sink;
        if ws {
            use tokio_tungstenite::tungstenite::handshake::server::{Request, Response};
            let callback = |req: &Request, response: Response| {
                let headers = req.headers();
                // X-Real-IP / X-Forwarded-For are trusted as-is so that the real
                // client IP is preserved when the WebSocket port runs behind a
                // reverse proxy (WSS). They are NOT validated: anyone who can reach
                // this port directly can spoof an arbitrary IP, bypassing IP-based
                // rate limiting / blocking and corrupting logged IPs. Do not expose
                // the WebSocket port directly to untrusted networks; only the
                // reverse proxy, which overwrites these headers, should be able to
                // connect to it.
                // https://github.com/rustdesk/rustdesk-server/issues/634
                let real_ip = headers
                    .get("X-Real-IP")
                    .or_else(|| headers.get("X-Forwarded-For"))
                    .and_then(|header_value| header_value.to_str().ok());
                if let Some(ip) = real_ip {
                    if ip.contains('.') {
                        addr = format!("{ip}:0").parse().unwrap_or(addr);
                    } else {
                        addr = format!("[{ip}]:0").parse().unwrap_or(addr);
                    }
                }
                Ok(response)
            };
            let ws_stream = tokio_tungstenite::accept_hdr_async(stream, callback).await?;
            let (a, mut b) = ws_stream.split();
            sink = Some(Sink::Wss(SafeWsSink {
                sink: a,
                encrypt: None,
            }));
            while let Ok(Some(Ok(msg))) = timeout(30_000, b.next()).await {
                if let tungstenite::Message::Binary(bytes) = msg {
                    if !self.handle_tcp(&bytes, &mut sink, addr, key, ws).await {
                        break;
                    }
                }
            }
        } else {
            let (a, mut b) = Framed::new(stream, BytesCodec::new()).split();
            sink = Some(Sink::Tss(SafeTcpStreamSink {
                sink: a,
                encrypt: None,
            }));
            // Avoid key exchange if answering on nat helper port
            if !key.is_empty() {
                self.key_exchange_phase1(addr, &mut sink).await;
            }
            while let Ok(Some(Ok(mut bytes))) = timeout(30_000, b.next()).await {
                // log::debug!("receive tcp data from {:?} {:?}", addr, bytes);
                if let Some(Sink::Tss(s)) = sink.as_mut() {
                    if let Some(key) = s.encrypt.as_mut() {
                        if let Err(err) = key.dec(&mut bytes) {
                            log::error!("dec tcp data from {:?} err: {:?}", addr, err);
                            break;
                        }
                    }
                }
                if !self.handle_tcp(&bytes, &mut sink, addr, key, ws).await {
                    break;
                }
            }
        }
        if sink.is_none() {
            self.tcp_punch.lock().await.remove(&try_into_v4(addr));
        }
        log::debug!("Tcp connection from {:?} closed", addr);
        Ok(())
    }

    #[inline]
    async fn get_pk(&mut self, version: &str, id: String) -> Bytes {
        if version.is_empty() || self.inner.sk.is_none() {
            Bytes::new()
        } else {
            match self.pm.get(&id).await {
                Some(peer) => {
                    let pk = peer.read().await.pk.clone();
                    sign::sign(
                        &hbb_common::message_proto::IdPk {
                            id,
                            pk,
                            ..Default::default()
                        }
                        .write_to_bytes()
                        .unwrap_or_default(),
                        self.inner.sk.as_ref().unwrap(),
                    )
                    .into()
                }
                _ => Bytes::new(),
            }
        }
    }

    #[inline]
    fn get_server_sk(key: &str) -> (String, Option<sign::SecretKey>) {
        let mut out_sk = None;
        let mut key = key.to_owned();
        if let Ok(sk) = base64::decode(&key) {
            if sk.len() == sign::SECRETKEYBYTES {
                log::info!("The key is a crypto private key");
                key = base64::encode(&sk[(sign::SECRETKEYBYTES / 2)..]);
                let mut tmp = [0u8; sign::SECRETKEYBYTES];
                tmp[..].copy_from_slice(&sk);
                out_sk = Some(sign::SecretKey(tmp));
            }
        }

        if key.is_empty() || key == "-" || key == "_" {
            let (pk, sk) = crate::common::gen_sk(0);
            out_sk = sk;
            if !key.is_empty() {
                key = pk;
            }
        }

        if !key.is_empty() {
            log::info!("Key: {}", key);
        }
        (key, out_sk)
    }

    #[inline]
    fn is_lan(&self, addr: SocketAddr) -> bool {
        match addr {
            SocketAddr::V4(v4) => {
                let ip = *v4.ip();
                self.inner.mask.iter().any(|network| network.contains(ip))
            }
            SocketAddr::V6(v6) => {
                if let Some(v4) = v6.ip().to_ipv4() {
                    self.inner.mask.iter().any(|network| network.contains(v4))
                } else {
                    false
                }
            }
        }
    }

    async fn key_exchange_phase1(&mut self, addr: SocketAddr, sink: &mut Option<Sink>) {
        let mut msg_out = RendezvousMessage::new();
        log::debug!("KeyExchange phase 1: send our pk for this tcp connection in a message signed with our server key");
        let sk = &self.inner.sk;
        match sk {
            Some(sk) => {
                let our_pk_b = self.inner.secure_tcp_pk_b.clone();
                let sm = sign::sign(&our_pk_b.0, &sk);

                let bytes_sm = Bytes::from(sm);
                msg_out.set_key_exchange(KeyExchange {
                    keys: vec![bytes_sm],
                    ..Default::default()
                });
                log::trace!(
                    "KeyExchange {:?} -> bytes: {:?}",
                    addr,
                    hex::encode(Bytes::from(msg_out.write_to_bytes().unwrap()))
                );
                Self::send_to_sink(sink, msg_out).await;
            }
            None => {}
        }
    }
}

async fn check_relay_servers(rs0: Arc<RelayServers>, tx: Sender) {
    let mut futs = Vec::new();
    let rs = Arc::new(Mutex::new(Vec::new()));
    let loads = Arc::new(Mutex::new(HashMap::new()));
    for x in rs0.iter() {
        let host = relay_connect_address(x);
        let rs = rs.clone();
        let loads = loads.clone();
        let x = x.clone();
        futs.push(tokio::spawn(async move {
            // Check relay liveness via FramedStream (existing behavior)
            let alive = FramedStream::new(&host, None, CHECK_RELAY_TIMEOUT)
                .await
                .is_ok();
            if alive {
                rs.lock().await.push(x);
                // Query load via raw TCP (send 0x00, read JSON response)
                // Use raw TcpStream because FramedStream adds length-delimited framing
                use hbb_common::tokio::io::AsyncReadExt;
                use hbb_common::tokio::io::AsyncWriteExt;
                if let Ok(mut raw) = hbb_common::tokio::net::TcpStream::connect(&host).await {
                    let _ = raw.write(&[0x00]).await;
                    let mut buf = [0u8; 128];
                    if let Ok(Ok(n)) = hbb_common::timeout(2000, raw.read(&mut buf)).await {
                        let text = String::from_utf8_lossy(&buf[..n]);
                        if let Some(start) = text.find("connections") {
                            let colon = text[start..].find(':').map(|i| start + i + 1).unwrap_or(0);
                            if colon > 0 {
                                let val_end = text[colon..]
                                    .find(|c: char| !c.is_digit(10))
                                    .map(|i| colon + i)
                                    .unwrap_or(n);
                                if let Ok(conns) = text[colon..val_end].trim().parse::<i32>() {
                                    loads.lock().await.insert(host, conns);
                                }
                            }
                        }
                    }
                }
            }
        }));
    }
    join_all(futs).await;
    log::debug!("check_relay_servers");
    let rs = std::mem::take(&mut *rs.lock().await);
    tx.send(Data::RelayServers(rs)).ok();
    let loads = std::mem::take(&mut *loads.lock().await);
    tx.send(Data::RelayLoads(loads)).ok();
}

// temp solution to solve udp socket failure
async fn test_hbbs(addr: SocketAddr) -> ResultType<()> {
    let mut addr = addr;
    if addr.ip().is_unspecified() {
        addr.set_ip(if addr.is_ipv4() {
            IpAddr::V4(Ipv4Addr::LOCALHOST)
        } else {
            IpAddr::V6(Ipv6Addr::LOCALHOST)
        });
    }

    let mut socket = FramedSocket::new(config::Config::get_any_listen_addr(addr.is_ipv4())).await?;
    let mut msg_out = RendezvousMessage::new();
    msg_out.set_register_peer(RegisterPeer {
        id: "(:test_hbbs:)".to_owned(),
        ..Default::default()
    });
    let mut last_time_recv = Instant::now();

    let mut timer = interval(Duration::from_secs(1));
    loop {
        tokio::select! {
          _ = timer.tick() => {
              if last_time_recv.elapsed().as_secs() > 12 {
                  bail!("Timeout of test_hbbs");
              }
              socket.send(&msg_out, addr).await?;
          }
          Some(Ok((bytes, _))) = socket.next() => {
              if let Ok(msg_in) = RendezvousMessage::parse_from_bytes(&bytes) {
                 log::trace!("Recv {:?} of test_hbbs", msg_in);
                 last_time_recv = Instant::now();
              }
          }
        }
    }
}

#[inline]
async fn send_rk_res(
    socket: &mut FramedSocket,
    addr: SocketAddr,
    res: register_pk_response::Result,
) -> ResultType<()> {
    let mut msg_out = RendezvousMessage::new();
    msg_out.set_register_pk_response(RegisterPkResponse {
        result: res.into(),
        ..Default::default()
    });
    socket.send(&msg_out, addr).await
}

async fn create_udp_listener(
    bind_addr: Option<IpAddr>,
    port: i32,
    rmem: usize,
) -> ResultType<FramedSocket> {
    if let Some(bind_addr) = bind_addr {
        let addr = SocketAddr::new(bind_addr, port as _);
        return FramedSocket::new_reuse(&addr, true, rmem).await;
    }
    let addr = SocketAddr::new(IpAddr::V6(Ipv6Addr::UNSPECIFIED), port as _);
    if let Ok(s) = FramedSocket::new_reuse(&addr, true, rmem).await {
        log::debug!("listen on udp {:?}", s.local_addr());
        return Ok(s);
    }
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), port as _);
    let s = FramedSocket::new_reuse(&addr, true, rmem).await?;
    log::debug!("listen on udp {:?}", s.local_addr());
    Ok(s)
}

#[inline]
async fn create_tcp_listener(bind_addr: Option<IpAddr>, port: i32) -> ResultType<TcpListener> {
    let s = listen_tcp(bind_addr, port as _).await?;
    log::debug!("listen on tcp {:?}", s.local_addr());
    Ok(s)
}

fn derive_key_from_exchange(
    ex: &KeyExchange,
    our_sk_b: [u8; 32],
) -> Result<secretbox::Key, KeyExchangeError> {
    if ex.keys.len() != 2 {
        return Err(KeyExchangeError::InvalidKeyCount);
    }
    if ex.keys[0].len() != 32 {
        log::warn!(
            "Invalid KeyExchange public key length: {}",
            ex.keys[0].len()
        );
        return Err(KeyExchangeError::InvalidPublicKeyLength);
    }
    if ex.keys[1].len() != 48 {
        log::warn!(
            "Invalid KeyExchange ciphertext length: {}",
            ex.keys[1].len()
        );
        return Err(KeyExchangeError::InvalidCiphertextLength);
    }
    let their_pk = ex.keys[0]
        .as_ref()
        .try_into()
        .map_err(|_| KeyExchangeError::InvalidPublicKeyLength)?;
    let encrypted_key = ex.keys[1]
        .as_ref()
        .try_into()
        .map_err(|_| KeyExchangeError::InvalidCiphertextLength)?;
    let symmetric_key = get_symmetric_key_from_msg(our_sk_b, their_pk, encrypted_key)?;
    secretbox::Key::from_slice(&symmetric_key).ok_or(KeyExchangeError::InvalidSymmetricKeyLength)
}

fn get_symmetric_key_from_msg(
    our_sk_b: [u8; 32],
    their_pk_b: [u8; 32],
    sealed_value: &[u8; 48],
) -> Result<[u8; 32], KeyExchangeError> {
    let their_pk_b = box_::PublicKey(their_pk_b);
    let nonce = box_::Nonce([0u8; box_::NONCEBYTES]);
    let sk = box_::SecretKey(our_sk_b);
    let key = box_::open(sealed_value, &nonce, &their_pk_b, &sk)
        .map_err(|_| KeyExchangeError::DecryptionFailed)?;
    if key.len() != secretbox::KEYBYTES {
        return Err(KeyExchangeError::InvalidSymmetricKeyLength);
    }
    key.as_slice()
        .try_into()
        .map_err(|_| KeyExchangeError::InvalidSymmetricKeyLength)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn validate_auth(
        supplied_licence_key: &str,
        supplied_token: &str,
        configured_licence_key: &str,
        must_login: bool,
        jwt_configured: bool,
        valid_token: bool,
    ) -> Result<(), ConnectionAuthError> {
        validate_connection_auth_with(
            supplied_licence_key,
            supplied_token,
            configured_licence_key,
            must_login,
            jwt_configured,
            |_| valid_token,
        )
    }

    #[test]
    fn connection_auth_rules_are_consistent() {
        assert_eq!(validate_auth("", "", "", false, false, false), Ok(()));
        assert_eq!(
            validate_auth("", "", "", true, true, false),
            Err(ConnectionAuthError::LoginRequired)
        );
        assert_eq!(
            validate_auth("", "bad", "", true, true, false),
            Err(ConnectionAuthError::InvalidToken)
        );
        assert_eq!(validate_auth("", "valid", "", true, true, true), Ok(()));
        assert_eq!(
            validate_auth("wrong", "", "configured", false, false, false),
            Err(ConnectionAuthError::LicenseMismatch)
        );
        assert_eq!(
            validate_auth("anything", "", "", false, false, false),
            Ok(())
        );
        assert_eq!(
            validate_auth("", "token", "", true, false, true),
            Err(ConnectionAuthError::ServerMisconfigured)
        );
    }

    #[test]
    fn malformed_key_exchange_is_rejected_without_panicking() {
        let server_sk = [0u8; 32];
        for key_count in [0, 1, 3] {
            let ex = KeyExchange {
                keys: vec![Default::default(); key_count],
                ..Default::default()
            };
            assert_eq!(
                derive_key_from_exchange(&ex, server_sk),
                Err(KeyExchangeError::InvalidKeyCount)
            );
        }

        for public_key_len in [31, 33] {
            let ex = KeyExchange {
                keys: vec![vec![0; public_key_len].into(), vec![0; 48].into()],
                ..Default::default()
            };
            assert_eq!(
                derive_key_from_exchange(&ex, server_sk),
                Err(KeyExchangeError::InvalidPublicKeyLength)
            );
        }

        for ciphertext_len in [47, 49] {
            let ex = KeyExchange {
                keys: vec![vec![0; 32].into(), vec![0; ciphertext_len].into()],
                ..Default::default()
            };
            assert_eq!(
                derive_key_from_exchange(&ex, server_sk),
                Err(KeyExchangeError::InvalidCiphertextLength)
            );
        }

        let ex = KeyExchange {
            keys: vec![vec![0; 32].into(), vec![0; 48].into()],
            ..Default::default()
        };
        assert_eq!(
            derive_key_from_exchange(&ex, server_sk),
            Err(KeyExchangeError::DecryptionFailed)
        );
    }

    #[test]
    fn valid_key_exchange_derives_symmetric_key() {
        assert!(hbb_common::sodiumoxide::init().is_ok());
        let (server_pk, server_sk) = box_::gen_keypair();
        let (client_pk, client_sk) = box_::gen_keypair();
        let expected = secretbox::gen_key();
        let nonce = box_::Nonce([0u8; box_::NONCEBYTES]);
        let encrypted = box_::seal(expected.as_ref(), &nonce, &server_pk, &client_sk);
        let ex = KeyExchange {
            keys: vec![client_pk.as_ref().to_vec().into(), encrypted.into()],
            ..Default::default()
        };

        let derived = derive_key_from_exchange(&ex, server_sk.0);
        assert_eq!(
            derived.as_ref().map(|key| key.as_ref()),
            Ok(expected.as_ref())
        );
    }

    #[test]
    fn always_use_relay_toggle_accepts_only_y_or_n() {
        ALWAYS_USE_RELAY.store(false, Ordering::SeqCst);
        assert_eq!(set_always_use_relay("y"), Ok(()));
        assert!(ALWAYS_USE_RELAY.load(Ordering::SeqCst));
        assert_eq!(set_always_use_relay("N"), Ok(()));
        assert!(!ALWAYS_USE_RELAY.load(Ordering::SeqCst));

        ALWAYS_USE_RELAY.store(true, Ordering::SeqCst);
        assert_eq!(set_always_use_relay("invalid"), Err(()));
        assert!(ALWAYS_USE_RELAY.load(Ordering::SeqCst));
    }

    #[test]
    fn relay_entries_are_normalized_without_capacity_suffixes() {
        let cases = [
            ("relay.example.com", "relay.example.com", 100),
            ("relay.example.com:21117", "relay.example.com:21117", 100),
            ("relay.example.com:21117:25", "relay.example.com:21117", 25),
            ("192.0.2.10", "192.0.2.10", 100),
            ("192.0.2.10:21117", "192.0.2.10:21117", 100),
            ("192.0.2.10:21117:50", "192.0.2.10:21117", 50),
            ("[2001:db8::1]:21117", "[2001:db8::1]:21117", 100),
            ("[2001:db8::1]:21117:75", "[2001:db8::1]:21117", 75),
        ];
        for (input, address, capacity) in cases {
            assert_eq!(
                parse_relay_entry(input),
                Some(RelayInfo {
                    address: address.to_owned(),
                    capacity,
                })
            );
        }
        for invalid in ["", "host:21117:bad", "host:21117:0", "host:21117:-1"] {
            assert_eq!(parse_relay_entry(invalid), None);
        }
        assert_eq!(
            normalize_relay_entries("relay.example.com:21117:10,relay.example.com:21117:20"),
            vec![RelayInfo {
                address: "relay.example.com:21117".to_owned(),
                capacity: 10,
            }]
        );
    }

    #[hbb_common::tokio::test]
    async fn udp_listener_uses_bind_address() {
        let bind_addr = IpAddr::V4(Ipv4Addr::LOCALHOST);
        let socket = create_udp_listener(Some(bind_addr), 0, 0).await.unwrap();
        assert_eq!(socket.local_addr().unwrap().ip(), bind_addr);
    }
}
