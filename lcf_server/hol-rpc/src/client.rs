//! RPC Client.

use std::sync::Arc;

use tarpc::{context, tokio_serde::formats::Bincode};

use crate::{InterfaceClient, Result};

/// RPC Client.
#[derive(Debug, Clone)]
pub struct Client(Arc<ClientImpl>);

#[derive(Debug)]
struct ClientImpl {
    interface: InterfaceClient,
    runtime: tokio::runtime::Runtime,
}

impl Client {
    /// Create a new client and connect to the server.
    pub fn new(addr: impl tokio::net::ToSocketAddrs) -> Result<Self> {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()?;

        let interface = runtime.block_on(async {
            let transport = tarpc::serde_transport::tcp::connect(addr, Bincode::default).await?;
            let client = InterfaceClient::new(tarpc::client::Config::default(), transport).spawn();
            Ok(client) as Result<_>
        })?;

        Ok(Self(Arc::new(ClientImpl { interface, runtime })))
    }

    pub(crate) fn execute<F>(&self, fut: F) -> F::Output
    where
        F: std::future::Future,
    {
        self.0.runtime.block_on(fut)
    }

    pub(crate) fn interface(&self) -> &InterfaceClient {
        &self.0.interface
    }

    /// Dispose a term.
    pub(crate) fn dispose_term(&self, key: crate::TermKey) -> Result<()> {
        self.execute(self.0.interface.dispose_term(context::current(), key))?
    }

    /// Dispose a theorem.
    pub(crate) fn dispose_theorem(&self, key: crate::TheoremKey) -> Result<()> {
        self.execute(self.0.interface.dispose_theorem(context::current(), key))?
    }

    /// Dispose a type.
    pub(crate) fn dispose_type(&self, key: crate::TypeKey) -> Result<()> {
        self.execute(self.0.interface.dispose_type(context::current(), key))?
    }

    /// Dispose a conversion.
    pub(crate) fn dispose_conversion(&self, key: crate::ConversionKey) -> Result<()> {
        self.execute(self.0.interface.dispose_conversion(context::current(), key))?
    }
}

/// Term.
pub struct Term {
    pub(crate) key: crate::TermKey,
    client: Client,
}

impl Term {
    pub(crate) fn new(key: crate::TermKey, client: Client) -> Self {
        Self { key, client }
    }
}

impl Drop for Term {
    fn drop(&mut self) {
        let _ = self.client.dispose_term(self.key);
    }
}

/// Theorem.
pub struct Theorem {
    pub(crate) key: crate::TheoremKey,
    client: Client,
}

impl Theorem {
    pub(crate) fn new(key: crate::TheoremKey, client: Client) -> Self {
        Self { key, client }
    }
}

impl Drop for Theorem {
    fn drop(&mut self) {
        let _ = self.client.dispose_theorem(self.key);
    }
}

/// Type.
pub struct Type {
    pub(crate) key: crate::TypeKey,
    client: Client,
}

impl Type {
    pub(crate) fn new(key: crate::TypeKey, client: Client) -> Self {
        Self { key, client }
    }
}

impl Drop for Type {
    fn drop(&mut self) {
        let _ = self.client.dispose_type(self.key);
    }
}

/// Conversion.
pub struct Conversion {
  pub(crate) key: crate::ConversionKey,
  client: Client,
}

impl Conversion {
  pub(crate) fn new(key: crate::ConversionKey, client: Client) -> Self {
    Self { key, client }
  }
}

impl Drop for Conversion {
  fn drop(&mut self) {
    let _ = self.client.dispose_conversion(self.key);
  }
}

/// Inductive type.
pub struct IndType {
    /// The inductive theorem.
    pub ind: Theorem,
    /// The recursion theorem.
    pub rec: Theorem,
}

/// Inductive Relation.
pub struct IndDef {
  /// definition.
  pub def: Theorem, 
  /// inductive rule.
  pub ind: Theorem,
  /// cases rule.
  pub cases: Theorem,
}
