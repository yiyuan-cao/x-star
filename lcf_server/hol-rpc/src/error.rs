//! Error handling for the RPC server and client.

use serde::{Deserialize, Serialize};

/// RPC error.
#[derive(Debug, Serialize, Deserialize)]
pub struct RpcError {
    /// Description of the error.
    pub description: String,
    /// Source of the error.
    pub source: Option<Box<RpcError>>,
}

impl RpcError {
    /// Create a new RPC error from an error.
    pub fn new(error: impl std::error::Error) -> Self {
        Self {
            description: error.to_string(),
            source: error.source().map(|source| Box::new(Self::new(source))),
        }
    }

    /// Create a new RPC error from an error report.
    pub fn from_report(report: eyre::Report) -> Self {
        let description = report.to_string();
        let source = report.source().map(|source| Box::new(Self::new(source)));
        Self {
            description,
            source,
        }
    }

    /// Create a new RPC error from a description.
    pub fn from_string(description: String) -> Self {
        Self {
            description,
            source: None,
        }
    }
}

macro_rules! impl_into_rpc_error {
    ($($ty:ty),*) => {
        $(
            impl From<$ty> for RpcError {
                fn from(err: $ty) -> Self {
                    Self::new(err)
                }
            }
        )*
    };
}

impl_into_rpc_error!(std::io::Error, tarpc::client::RpcError);

impl From<String> for RpcError {
    fn from(description: String) -> Self {
        Self::from_string(description)
    }
}

impl From<&str> for RpcError {
    fn from(description: &str) -> Self {
        Self::from_string(description.to_string())
    }
}

impl From<eyre::Report> for RpcError {
    fn from(report: eyre::Report) -> Self {
        Self::from_report(report)
    }
}

impl std::fmt::Display for RpcError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description)
    }
}

impl std::error::Error for RpcError {
    fn description(&self) -> &str {
        &self.description
    }

    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.source
            .as_ref()
            .map(|source| &**source as &dyn std::error::Error)
    }
}

/// Result type for RPC operations.
pub type Result<T> = std::result::Result<T, RpcError>;
