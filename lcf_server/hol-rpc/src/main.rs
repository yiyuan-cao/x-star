//! RPC Server.

#![deny(missing_docs)]

use std::{
    net::{IpAddr, SocketAddr},
    path::PathBuf,
};

use envconfig::Envconfig;
use futures::stream::StreamExt;
use hol_rpc::Interface;
use tarpc::{
    server::{incoming::Incoming, BaseChannel, Channel},
    tokio_serde::formats::Bincode,
};
use hol_rpc::caml_dyn_call;

#[macro_use]
mod session;
mod interface_server;

/// Configuration.
#[derive(Envconfig)]
pub struct Config {
    /// Path to the HOL Light directory.
    #[envconfig(from = "HOLLIGHT_DIR")]
    pub hol_dir: PathBuf,

    /// Address to listen on.
    #[envconfig(from = "LCF_SERVER_LISTEN", default = "0.0.0.0")]
    pub listen: IpAddr,

    /// Port to listen on.
    #[envconfig(from = "LCF_SERVER_PORT", default = "5000")]
    pub port: u16,
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let config = Config::init_from_env().expect("Failed to load configuration");

    let hol_dir = std::env::var("HOLLIGHT_DIR").expect("HOLLIGHT_DIR not set");
    caml_dyn_call::init(&[
        format!("#directory \"{hol_dir}\";;"),
        "#use \"hol.ml\";;".to_string(),
    ])
    .expect("OCaml initialization failed");

    let server_addr = SocketAddr::new(config.listen, config.port);

    let mut listener = tarpc::serde_transport::tcp::listen(&server_addr, Bincode::default)
        .await
        .expect("Failed to bind");
    listener.config_mut().max_frame_length(usize::MAX);
    let listener = listener
        .filter_map(|r| async { r.ok() })
        .map(BaseChannel::with_defaults)
        .max_channels_per_key(1, |t| t.transport().peer_addr().unwrap().ip());
    let mut listener = std::pin::pin!(listener);

    let local = tokio::task::LocalSet::new();
    local
        .run_until(async {
            while let Some(channel) = listener.next().await {
                tokio::task::spawn_local(async move {
                    let session = session::Session::new();
                    channel.execute(session.serve()).for_each(|r| r).await;
                });
            }
        })
        .await
}
