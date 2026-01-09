# Praborrow Core

Core primitives for the PraBorrow distributed systems framework. This crate provides the foundational types for enforcing sovereign ownership semantics across network boundaries.

## Sovereign<T>

The `Sovereign<T>` wrapper implements a distinct state machine for data ownership:
- **Domestic**: Data is local and accessible via `Deref`.
- **Exiled**: Data has been moved to a remote node. Access attempts trigger a panic.

### Usage

```rust
use praborrow_core::Sovereign;

let data = Sovereign::new(42);

// Access allowed (Domestic)
assert_eq!(*data, 42);

// Transition state
data.annex().expect("Failed to annex resource");

// Access denied (Exiled)
// *data // Panics: "SOVEREIGNTY VIOLATION"
```

### Thread Safety

Uses `AtomicU8` for state tracking, ensuring `Send + Sync` compliance where `T: Send + Sync`.
