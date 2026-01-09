use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicU8, Ordering};
use std::cell::UnsafeCell;

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
    pub fn annex(&self) -> Result<(), String> {
        let current = self.state.load(Ordering::SeqCst);
        if current == SovereignState::Exiled as u8 {
            return Err("Resource is already under foreign jurisdiction.".to_string());
        }

        // Diplomatically transition state
        self.state.store(SovereignState::Exiled as u8, Ordering::SeqCst);
        Ok(())
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
        unsafe { &*self.inner.get() }
    }
}

impl<T> DerefMut for Sovereign<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.verify_jurisdiction();
        unsafe { &mut *self.inner.get() }
    }
}

// Safety: Sovereign<T> is Send/Sync if T is Send/Sync, as we use AtomicU8 for state
// and check it before access.
unsafe impl<T: Send> Send for Sovereign<T> {}
unsafe impl<T: Sync> Sync for Sovereign<T> {}

/// Protocol for enforcing constitutional invariants.
/// Defined in Core to ensure universal application.
pub trait CheckProtocol {
    fn enforce_law(&self);
}
