mod connect;
mod extension;
mod http;
mod murmur;
#[cfg(target_os = "linux")]
mod route;
mod socks5;

use self::connect::Connector;
use crate::{AuthMode, BootArgs, Proxy};
pub use crate::error::Error;
use std::net::{IpAddr, SocketAddr};
use tracing::Level;
use tracing_subscriber::{EnvFilter, FmtSubscriber};

struct ProxyContext {
    /// Bind address
    pub bind: SocketAddr,
    /// Number of concurrent connections
    pub concurrent: usize,
    /// Authentication type
    pub auth: AuthMode,
    /// Ip whitelist
    pub whitelist: Vec<IpAddr>,
    /// Connector
    pub connector: Connector,
}

impl ProxyContext {
    fn new(args: &BootArgs, auth: AuthMode) -> Self {
        ProxyContext {
            bind: args.bind,
            concurrent: args.concurrent,
            auth,
            whitelist: args.whitelist.clone(),
            connector: Connector::new(
                args.cidr.clone(),
                args.fallback,
                args.connect_timeout,
                args.fixed_subnet_48.clone(),
            ),
        }
    }
}

pub fn run(args: BootArgs) -> Result<(), Box<dyn std::error::Error>> {
    // Initialize the logger with a filter that ignores WARN level logs for netlink_proto
    let filter = EnvFilter::from_default_env()
        .add_directive(
            if args.debug {
                Level::DEBUG
            } else {
                Level::INFO
            }
            .into(),
        )
        .add_directive(
            "netlink_proto=error"
                .parse()
                .expect("failed to parse directive"),
        );

    tracing::subscriber::set_global_default(
        FmtSubscriber::builder().with_env_filter(filter).finish(),
    )
    .expect("setting default subscriber failed");

    tracing::info!("OS: {}", std::env::consts::OS);
    tracing::info!("Arch: {}", std::env::consts::ARCH);
    tracing::info!("Version: {}", env!("CARGO_PKG_VERSION"));
    tracing::info!("Concurrent: {}", args.concurrent);
    tracing::info!("Connect timeout: {:?}s", args.connect_timeout);

    #[cfg(target_family = "unix")]
    {
        use nix::sys::resource::{setrlimit, Resource};
        let soft_limit = (args.concurrent * 3) as u64;
        let hard_limit = 1048576;
        setrlimit(Resource::RLIMIT_NOFILE, soft_limit.into(), hard_limit)?;
    }

    let ctx = ProxyContext::new(&args, match args.proxy {
        Proxy::Http { ref auth } | Proxy::Socks5 { ref auth } => auth.clone(),
    });

    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .max_blocking_threads(args.concurrent)
        .build()
        .map_err(|e| {
            tracing::error!("Failed to build Tokio runtime: {:?}", e);
            Box::new(e) as Box<dyn std::error::Error>
        })?
        .block_on(async {
            #[cfg(target_os = "linux")]
            if let Some(cidr) = &args.cidr {
                route::sysctl_ipv6_no_local_bind();
                route::sysctl_route_add_cidr(&cidr).await;
            }
            match args.proxy {
                Proxy::Http { .. } => http::proxy(ctx).await,
                Proxy::Socks5 { .. } => socks5::proxy(ctx).await,
            }
        })
        .map_err(|e| {
            tracing::error!("Runtime block error: {:?}", e);
            Box::new(e) as Box<dyn std::error::Error>
        })?;

    Ok(())
}
