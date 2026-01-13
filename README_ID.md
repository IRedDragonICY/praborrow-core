# Praborrow Core (Bahasa Indonesia)

[English](./README.md) | Indonesia

Primitif inti untuk framework sistem terdistribusi PraBorrow. Crate ini menyediakan tipe dasar untuk menegakkan semantik kepemilikan kedaulatan (sovereign ownership) lintas batas jaringan.

## Sovereign<T>

Wrapper `Sovereign<T>` mengimplementasikan state machine yang berbeda untuk kepemilikan data:
- **Domestic (Domestik)**: Data bersifat lokal dan dapat diakses melalui `Deref`.
- **Exiled (Diasingkan)**: Data telah dipindahkan ke node jarak jauh (remote). Upaya akses akan memicu panic (atau mengembalikan `Err` dengan `try_get`).

### Penggunaan (Usage)

```rust
use praborrow_core::{Sovereign, SovereigntyError};

let data = Sovereign::new(42);

// Akses diizinkan (Domestic)
assert_eq!(*data, 42);

// Akses aman dengan penanganan error (v0.5+)
assert!(data.try_get().is_ok());

// Transisi status
data.annex().expect("Gagal melakukan aneksasi sumber daya");

// Penanganan error yang anggun alih-alih panic
match data.try_get() {
    Ok(_) => unreachable!(),
    Err(SovereigntyError::ForeignJurisdiction) => println!("Diasingkan (Exiled)!"),
}
```

### Keamanan Thread (Thread Safety)

Menggunakan `AtomicU8` untuk pelacakan status, memastikan kepatuhan `Send + Sync` di mana `T: Send + Sync`.
