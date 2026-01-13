# Praborrow Core

English | [Indonesia](./README_ID.md)

Core primitives for the PraBorrow distributed systems framework. This crate provides the foundational types for enforcing sovereign ownership semantics across network boundaries.

## Sovereign<T>

The `Sovereign<T>` wrapper implements a distinct state machine for data ownership:
- **Domestic**: Data is local and accessible via `Deref`.
- **Exiled**: Data has been moved to a remote node. Access attempts trigger a panic (or return `Err` with `try_get`).

### Usage

```rust
use praborrow_core::{Sovereign, SovereigntyError};

let data = Sovereign::new(42);

// Access allowed (Domestic)
assert_eq!(*data, 42);

// Safe access with error handling (v0.5+)
assert!(data.try_get().is_ok());

// Transition state
data.annex().expect("Failed to annex resource");

// Graceful error handling instead of panic
match data.try_get() {
    Ok(_) => unreachable!(),
    Err(SovereigntyError::ForeignJurisdiction) => println!("Exiled!"),
}
```

### Thread Safety

Uses `AtomicU8` for state tracking, ensuring `Send + Sync` compliance where `T: Send + Sync`.


