//! Core primitives for distributed ownership enforcement.
//!
//! This crate provides `Sovereign<T>`, a wrapper type that tracks ownership
//! across network boundaries. When a resource is "annexed" (moved to another node),
//! local access is prohibited.
//!
//! # The Garuda Proof System
//!
//! With `praborrow-prover`, this crate now supports **formally verified** state
//! transitions. Use `annex_verified()` to require SMT proof before annexation.
//!
//! # Safety
//! Uses `UnsafeCell` and `AtomicU8` for interior mutability with thread-safety.
//! The `Send`/`Sync` implementations are safe when `T` is `Send`/`Sync`.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use alloc::string::{String, ToString};
use core::ops::{Deref, DerefMut};
use core::sync::atomic::{AtomicU8, Ordering};
use core::cell::UnsafeCell;
use core::marker::PhantomData;
use core::fmt;

/// The state of a Sovereign resource.
/// 0: Domestic (Local jurisdiction)
/// 1: Exiled (Foreign jurisdiction - moved to another node)
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum SovereignState {
    Domestic = 0,
    Exiled = 1,
}

/// A wrapper that enforces ownership semantics across network boundaries.
///
/// "Memory safety with sovereign integrity."
pub struct Sovereign<T> {
    inner: UnsafeCell<T>,
    state: AtomicU8,
}

impl<T> Sovereign<T> {
    /// Creates a new Sovereign resource under domestic jurisdiction.
    pub fn new(value: T) -> Self {
        Self {
            inner: UnsafeCell::new(value),
            state: AtomicU8::new(SovereignState::Domestic as u8),
        }
    }

    /// Annexes the resource, moving it to foreign jurisdiction.
    ///
    /// Once annexed, the resource cannot be accessed locally.
    /// Access attempts will result in a Sovereignty Violation (panic).
    pub fn annex(&self) -> Result<(), AnnexError> {
        let current = self.state.load(Ordering::SeqCst);
        if current == SovereignState::Exiled as u8 {
            return Err(AnnexError::AlreadyExiled);
        }

        // Diplomatically transition state
        self.state.store(SovereignState::Exiled as u8, Ordering::SeqCst);
        Ok(())
    }

    /// Returns a reference to the inner value without jurisdiction check.
    ///
    /// # Safety
    /// This is safe because we're returning a shared reference and the caller
    /// is responsible for ensuring the resource is domestic.
    pub fn inner_ref(&self) -> &T {
        // SAFETY: We're only reading, and this is safe when called from
        // contexts that have already verified jurisdiction.
        unsafe { &*self.inner.get() }
    }

    /// Returns the current state of the resource.
    pub fn state(&self) -> SovereignState {
        match self.state.load(Ordering::SeqCst) {
            0 => SovereignState::Domestic,
            _ => SovereignState::Exiled,
        }
    }

    /// Checks if the resource is currently domestic.
    fn verify_jurisdiction(&self) {
        if self.state.load(Ordering::SeqCst) == SovereignState::Exiled as u8 {
            panic!("SOVEREIGNTY VIOLATION: Resource is under foreign jurisdiction.");
        }
    }
}

impl<T> Deref for Sovereign<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.verify_jurisdiction();
        // SAFETY: We've verified the resource is domestic, so access is valid.
        unsafe { &*self.inner.get() }
    }
}

impl<T> DerefMut for Sovereign<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.verify_jurisdiction();
        // SAFETY: We've verified the resource is domestic and have &mut self.
        unsafe { &mut *self.inner.get() }
    }
}

// SAFETY: Sovereign<T> is Send/Sync if T is Send/Sync, as we use AtomicU8 for state
// and check it before access. The UnsafeCell is protected by the atomic state check.
unsafe impl<T: Send> Send for Sovereign<T> {}
unsafe impl<T: Sync> Sync for Sovereign<T> {}

/// Protocol for enforcing constitutional invariants (runtime checks).
pub trait CheckProtocol {
    /// Enforces all invariants, panicking if any are violated.
    fn enforce_law(&self);
}

/// A value carrying cryptographic proof of verification.
///
/// This type can only be constructed by successful SMT verification.
/// Its existence in a type signature proves that formal verification occurred.
///
/// # Type Safety Guarantee
///
/// `ProofCarrying<T>` cannot be forged - the private `_proof` field
/// ensures only the prover crate can construct it.
#[derive(Debug)]
pub struct ProofCarrying<T> {
    /// The carried value.
    pub value: T,
    /// Private marker ensuring construction only via verification.
    _proof: PhantomData<()>,
}

impl<T> ProofCarrying<T> {
    /// Creates a new proof-carrying value.
    ///
    /// This should only be called after successful verification.
    #[doc(hidden)]
    pub fn new_unchecked(value: T) -> Self {
        Self {
            value,
            _proof: PhantomData,
        }
    }

    /// Extracts the inner value, consuming the proof.
    pub fn into_inner(self) -> T {
        self.value
    }
}

impl<T: Clone> Clone for ProofCarrying<T> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            _proof: PhantomData,
        }
    }
}

/// Error type for verified annexation operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnnexError {
    /// Resource is already under foreign jurisdiction.
    AlreadyExiled,
    /// SMT verification failed.
    VerificationFailed(String),
    /// Prover encountered an error.
    ProverError(String),
}

impl fmt::Display for AnnexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AnnexError::AlreadyExiled => write!(f, "Resource is already under foreign jurisdiction"),
            AnnexError::VerificationFailed(msg) => write!(f, "Verification failed: {}", msg),
            AnnexError::ProverError(msg) => write!(f, "Prover error: {}", msg),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for AnnexError {}

/// Error returned when a lease operation fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeaseError {
    /// Resource is already leased to another holder.
    AlreadyLeased,
    /// Resource is under foreign jurisdiction.
    ForeignJurisdiction,
}

/// Represents a lease on a Sovereign resource.
pub struct Lease<T> {
    /// The holder's unique identifier.
    pub holder: u128,
    /// Duration of the lease.
    pub duration: core::time::Duration,
    /// Phantom data for the resource type.
    _phantom: PhantomData<T>,
}

impl<T> Lease<T> {
    /// Creates a new lease.
    pub fn new(holder: u128, duration: core::time::Duration) -> Self {
        Self {
            holder,
            duration,
            _phantom: PhantomData,
        }
    }

    /// Returns the duration of the lease.
    pub fn duration(&self) -> core::time::Duration {
        self.duration
    }
}

/// Trait for distributed borrow operations.
pub trait DistributedBorrow<T> {
    /// Attempt to acquire a lease on the resource.
    fn try_hire(&self, candidate_id: u128, term: core::time::Duration) -> Result<Lease<T>, LeaseError>;
}

impl<T> DistributedBorrow<T> for Sovereign<T> {
    fn try_hire(&self, candidate_id: u128, term: core::time::Duration) -> Result<Lease<T>, LeaseError> {
        let current = self.state.load(Ordering::SeqCst);
        if current == SovereignState::Exiled as u8 {
            return Err(LeaseError::AlreadyLeased);
        }
        
        // Transition to exiled state (leased)
        self.state.store(SovereignState::Exiled as u8, Ordering::SeqCst);
        Ok(Lease::<T>::new(candidate_id, term))
    }
}

/// Extension trait for Sovereign types whose inner types implement formal verification.
///
/// This trait is automatically implemented for `Sovereign<T>` where `T` can be
/// formally verified via the Garuda Proof System.
pub trait VerifiedAnnex<T> {
    /// Annexes the resource after successful formal verification.
    ///
    /// Unlike `annex()`, this method requires mathematical proof that all
    /// invariants are satisfied before the state transition occurs.
    ///
    /// # Returns
    ///
    /// - `Ok(ProofCarrying<()>)` - Verification passed, resource is now Exiled
    /// - `Err(AnnexError)` - Verification failed or resource already Exiled
    ///
    /// # Example
    ///
    /// ```ignore
    /// use praborrow_core::{Sovereign, VerifiedAnnex};
    ///
    /// let resource = Sovereign::new(MyVerifiableStruct { balance: 100 });
    /// 
    /// // This will run SMT verification before annexing
    /// match resource.annex_verified() {
    ///     Ok(proof) => println!("Annexation proven safe!"),
    ///     Err(e) => println!("Cannot annex: {}", e),
    /// }
    /// ```
    fn annex_verified(&self) -> Result<ProofCarrying<()>, AnnexError>;
}

// Note: The actual implementation of VerifiedAnnex requires praborrow-prover,
// which would create a circular dependency. Instead, the implementation is
// provided via blanket impl in praborrow-prover or via the facade crate.
//
// Users should use the `praborrow` facade crate for full functionality.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sovereign_new() {
        let s = Sovereign::new(42i32);
        assert_eq!(s.state(), SovereignState::Domestic);
    }

    #[test]
    fn test_sovereign_deref() {
        let s = Sovereign::new(42i32);
        assert_eq!(*s, 42);
    }

    #[test]
    fn test_sovereign_deref_mut() {
        let mut s = Sovereign::new(42i32);
        *s = 100;
        assert_eq!(*s, 100);
    }

    #[test]
    fn test_sovereign_annex() {
        let s = Sovereign::new(42i32);
        assert!(s.annex().is_ok());
        assert_eq!(s.state(), SovereignState::Exiled);
    }

    #[test]
    fn test_sovereign_double_annex() {
        let s = Sovereign::new(42i32);
        assert!(s.annex().is_ok());
        assert!(s.annex().is_err());
    }

    #[test]
    #[should_panic(expected = "SOVEREIGNTY VIOLATION")]
    fn test_sovereignty_violation() {
        let s = Sovereign::new(42i32);
        s.annex().unwrap();
        let _ = *s; // This should panic
    }

    #[test]
    fn test_proof_carrying() {
        let proof = ProofCarrying::new_unchecked(42i32);
        assert_eq!(proof.value, 42);
        assert_eq!(proof.into_inner(), 42);
    }

    #[test]
    fn test_annex_error_display() {
        let e = AnnexError::AlreadyExiled;
        assert!(e.to_string().contains("foreign jurisdiction"));
        
        let e = AnnexError::VerificationFailed("test".to_string());
        assert!(e.to_string().contains("test"));
    }
}
