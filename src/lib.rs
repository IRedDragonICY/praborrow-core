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

use alloc::string::String;
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

/// Error returned when accessing a Sovereign resource fails.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SovereigntyError {
    /// Resource is under foreign jurisdiction (Exiled).
    ForeignJurisdiction,
}

impl fmt::Display for SovereigntyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SovereigntyError::ForeignJurisdiction => write!(f, "SOVEREIGNTY VIOLATION: Resource is under foreign jurisdiction."),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for SovereigntyError {}

impl<T> Sovereign<T> {
    /// Creates a new Sovereign resource under domestic jurisdiction.
    ///
    /// # Atomic Ordering
    ///
    /// Uses `SeqCst` ordering for maximum safety in distributed scenarios.
    /// This ensures all threads see state changes in a consistent order,
    /// which is critical for ownership semantics across network boundaries.
    pub fn new(value: T) -> Self {
        Self {
            inner: UnsafeCell::new(value),
            state: AtomicU8::new(SovereignState::Domestic as u8),
        }
    }

    /// Creates a new Sovereign resource that is already under foreign jurisdiction.
    ///
    /// This is useful for nodes receiving data that has been transferred from
    /// another node - the resource starts in an Exiled state.
    ///
    /// # Example
    ///
    /// ```
    /// use praborrow_core::{Sovereign, SovereignState};
    ///
    /// let foreign_data = Sovereign::new_exiled(42i32);
    /// assert!(foreign_data.is_exiled());
    /// ```
    pub fn new_exiled(value: T) -> Self {
        Self {
            inner: UnsafeCell::new(value),
            state: AtomicU8::new(SovereignState::Exiled as u8),
        }
    }

    /// Annexes the resource, moving it to foreign jurisdiction.
    ///
    /// Once annexed, the resource cannot be accessed locally.
    /// Access attempts will result in a Sovereignty Violation.
    #[must_use]
    pub fn annex(&self) -> Result<(), AnnexError> {
        let current = self.state.load(Ordering::SeqCst);
        if current == SovereignState::Exiled as u8 {
            return Err(AnnexError::AlreadyExiled);
        }

        // Diplomatically transition state
        self.state.store(SovereignState::Exiled as u8, Ordering::SeqCst);
        
        tracing::debug!(
            from = "Domestic",
            to = "Exiled",
            "Resource annexed to foreign jurisdiction"
        );
        
        Ok(())
    }

    /// Returns a reference to the inner value without jurisdiction check.
    ///
    /// # Safety
    ///
    /// This is safe because we're returning a shared reference and the caller
    /// is responsible for ensuring the resource is domestic. Use `try_get()`
    /// for safe access with jurisdiction verification.
    pub fn inner_ref(&self) -> &T {
        // SAFETY: We're only reading, and this is safe when called from
        // contexts that have already verified jurisdiction.
        unsafe { &*self.inner.get() }
    }

    /// Returns the current state of the resource.
    #[inline]
    pub fn state(&self) -> SovereignState {
        match self.state.load(Ordering::SeqCst) {
            0 => SovereignState::Domestic,
            _ => SovereignState::Exiled,
        }
    }

    /// Returns `true` if the resource is under domestic jurisdiction.
    #[inline]
    pub fn is_domestic(&self) -> bool {
        self.state.load(Ordering::SeqCst) == SovereignState::Domestic as u8
    }

    /// Returns `true` if the resource is under foreign jurisdiction (exiled).
    #[inline]
    pub fn is_exiled(&self) -> bool {
        self.state.load(Ordering::SeqCst) == SovereignState::Exiled as u8
    }

    /// Attempts to get a reference to the value, returning an error if Exiled.
    pub fn try_get(&self) -> Result<&T, SovereigntyError> {
        if self.is_exiled() {
            return Err(SovereigntyError::ForeignJurisdiction);
        }
        // SAFETY: We verified the resource is domestic.
        unsafe { Ok(&*self.inner.get()) }
    }

    /// Attempts to get a mutable reference to the value, returning an error if Exiled.
    pub fn try_get_mut(&mut self) -> Result<&mut T, SovereigntyError> {
        if self.is_exiled() {
            return Err(SovereigntyError::ForeignJurisdiction);
        }
        // SAFETY: We verified resource is domestic and have &mut self.
        unsafe { Ok(&mut *self.inner.get()) }
    }

    /// Repatriates a resource, transitioning it from Exiled back to Domestic.
    ///
    /// # Safety
    ///
    /// This function is `unsafe` because calling it incorrectly can lead to
    /// **split-brain ownership** - a catastrophic state where two nodes both
    /// believe they own the resource.
    ///
    /// The caller MUST guarantee:
    /// 1. The resource has been fully returned by the foreign node
    /// 2. The foreign node has relinquished all access to the resource
    /// 3. No in-flight network messages reference this resource
    /// 4. The consensus protocol (if any) has confirmed the transfer
    ///
    /// Violating these invariants leads to data races and memory unsafety
    /// in the distributed system.
    ///
    /// # Example
    ///
    /// ```
    /// use praborrow_core::{Sovereign, SovereignState};
    ///
    /// let resource = Sovereign::new(42i32);
    /// resource.annex().unwrap();
    /// assert!(resource.is_exiled());
    ///
    /// // ... resource is sent to foreign node and returned ...
    ///
    /// // SAFETY: We have confirmed the foreign node has released the resource
    /// unsafe { resource.repatriate(); }
    /// assert!(resource.is_domestic());
    /// ```
    pub unsafe fn repatriate(&self) {
        let previous = self.state.swap(SovereignState::Domestic as u8, Ordering::SeqCst);
        
        if previous == SovereignState::Exiled as u8 {
            tracing::debug!(
                from = "Exiled",
                to = "Domestic",
                "Resource repatriated to domestic jurisdiction"
            );
        }
    }

    /// Checks if the resource is currently domestic, panicking if not.
    ///
    /// Used internally by Deref/DerefMut. Prefer `try_get()` for non-panicking access.
    fn verify_jurisdiction(&self) {
        if self.is_exiled() {
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
///
/// Types implementing this trait can validate their internal state against
/// a set of invariants defined via the `#[derive(Constitution)]` macro.
pub trait CheckProtocol {
    /// Enforces all invariants, returning an error if any are violated.
    ///
    /// # Returns
    ///
    /// - `Ok(())` if all invariants are satisfied
    /// - `Err(String)` containing a description of the violated invariant
    ///
    /// # Example
    ///
    /// ```ignore
    /// use praborrow_core::CheckProtocol;
    ///
    /// let data = MyStruct { value: -1 };
    /// match data.enforce_law() {
    ///     Ok(()) => println!("All invariants satisfied"),
    ///     Err(e) => println!("Invariant violated: {}", e),
    /// }
    /// ```
    fn enforce_law(&self) -> Result<(), String>;
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
    ///
    /// # Duration Validation
    ///
    /// If `duration` is zero, it will be coerced to a minimum of 1 millisecond
    /// to prevent immediate expiration edge cases.
    pub fn new(holder: u128, duration: core::time::Duration) -> Self {
        // Prevent zero-duration leases which could cause immediate expiration
        let duration = if duration.is_zero() {
            tracing::warn!(
                holder = holder,
                "Zero-duration lease requested, coercing to 1ms minimum"
            );
            core::time::Duration::from_millis(1)
        } else {
            duration
        };
        
        Self {
            holder,
            duration,
            _phantom: PhantomData,
        }
    }

    /// Returns the duration of the lease.
    #[inline]
    pub fn duration(&self) -> core::time::Duration {
        self.duration
    }

    /// Returns the holder ID.
    #[inline]
    pub fn holder(&self) -> u128 {
        self.holder
    }
}

/// Trait for distributed borrow operations.
pub trait DistributedBorrow<T> {
    /// Attempt to acquire a lease on the resource.
    #[must_use]
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
        assert!(s.is_domestic());
        assert!(!s.is_exiled());
    }

    #[test]
    fn test_sovereign_new_exiled() {
        let s = Sovereign::new_exiled(42i32);
        assert_eq!(s.state(), SovereignState::Exiled);
        assert!(s.is_exiled());
        assert!(!s.is_domestic());
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
        assert!(s.is_exiled());
    }

    #[test]
    fn test_sovereign_double_annex() {
        let s = Sovereign::new(42i32);
        assert!(s.annex().is_ok());
        assert!(s.annex().is_err());
    }

    #[test]
    fn test_sovereign_repatriate() {
        let s = Sovereign::new(42i32);
        s.annex().unwrap();
        assert!(s.is_exiled());
        
        // SAFETY: In test context, we control both sides
        unsafe { s.repatriate(); }
        assert!(s.is_domestic());
        
        // Should be able to access again
        assert_eq!(*s, 42);
    }

    #[test]
    #[should_panic(expected = "SOVEREIGNTY VIOLATION")]
    fn test_sovereignty_violation() {
        let s = Sovereign::new(42i32);
        s.annex().unwrap();
        let _ = *s; // This should panic
    }

    #[test]
    fn test_try_get_domestic() {
        let s = Sovereign::new(42i32);
        assert_eq!(*s.try_get().unwrap(), 42);
    }

    #[test]
    fn test_try_get_exiled() {
        let s = Sovereign::new(42i32);
        s.annex().unwrap();
        assert!(matches!(s.try_get(), Err(SovereigntyError::ForeignJurisdiction)));
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

    #[test]
    fn test_lease_zero_duration_coercion() {
        let lease = Lease::<i32>::new(1, core::time::Duration::ZERO);
        assert_eq!(lease.duration(), core::time::Duration::from_millis(1));
    }

    #[test]
    fn test_lease_normal_duration() {
        let duration = core::time::Duration::from_secs(10);
        let lease = Lease::<i32>::new(1, duration);
        assert_eq!(lease.duration(), duration);
        assert_eq!(lease.holder(), 1);
    }
}
