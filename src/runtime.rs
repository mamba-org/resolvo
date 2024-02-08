//! Solving in resolvo is a compute heavy operation. However, while computing the solver will
//! request additional information from the [`crate::DependencyProvider`] and a dependency provider
//! might want to perform multiple requests concurrently. To that end the
//! [`crate::DependencyProvider`]s methods are async. The implementer can implement the async
//! operations in any way they choose including with any runtime they choose.
//! However, the solver itself is completely single threaded, but it still has to await the calls to
//! the dependency provider. Using the [`AsyncRuntime`] allows the caller of the solver to choose
//! how to await the futures.
//!
//! By default, the solver uses the [`NowOrNeverRuntime`] runtime which polls any future once. If
//! the future yields (thus requiring an additional poll) the runtime panics. If the methods of
//! [`crate::DependencyProvider`] do not yield (e.g. do not `.await`) this will suffice.
//!
//! Only if the [`crate::DependencyProvider`] implementation yields you will need to provide a
//! [`AsyncRuntime`] to the solver.
//!
//! ## `tokio`
//!
//! The solver uses tokio to await the results of async methods in [`crate::DependencyProvider`]. It
//! will run them concurrently, but blocking the main thread. That means that a single-threaded
//! tokio runtime is usually enough. It is also possible to use a different runtime, as long as you
//! avoid mixing incompatible futures.
//!
//! The [`AsyncRuntime`] trait is implemented both for [`tokio::runtime::Handle`] and for
//! [`tokio::runtime::Runtime`].
//!
//! ## `async-std`
//!
//! Use the [`AsyncStdRuntime`] struct to block on async methods from the
//! [`crate::DependencyProvider`] using the `async-std` executor.

use futures::FutureExt;
use std::future::Future;

/// A trait to wrap an async runtime.
pub trait AsyncRuntime {
    /// Runs the given future on the current thread, blocking until it is complete, and yielding its
    /// resolved result.
    fn block_on<F: Future>(&self, f: F) -> F::Output;
}

/// The simplest runtime possible evaluates and consumes the future, returning the resulting
/// output if the future is ready after the first call to [`Future::poll`]. If the future does
/// yield the runtime panics.
///
/// This assumes that the passed in future never yields. For purely blocking computations this
/// is the preferred method since it also incurs very little overhead and doesn't require the
/// inclusion of a heavy-weight runtime.
#[derive(Default, Copy, Clone)]
pub struct NowOrNeverRuntime;

impl AsyncRuntime for NowOrNeverRuntime {
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        f.now_or_never()
            .expect("can only use non-yielding futures with the NowOrNeverRuntime")
    }
}

#[cfg(feature = "tokio")]
impl AsyncRuntime for tokio::runtime::Handle {
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        self.block_on(f)
    }
}

#[cfg(feature = "tokio")]
impl AsyncRuntime for tokio::runtime::Runtime {
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        self.block_on(f)
    }
}

/// An implementation of [`AsyncRuntime`] that spawns and awaits any passed future on the current
/// thread.
#[cfg(feature = "async-std")]
pub struct AsyncStdRuntime;

#[cfg(feature = "async-std")]
impl AsyncRuntime for AsyncStdRuntime {
    fn block_on<F: Future>(&self, f: F) -> F::Output {
        async_std::task::block_on(f)
    }
}
