#[test]
fn test_sovereign_debug() {
    use crate::Sovereign;
    let s = Sovereign::new(42);
    let debug_str = format!("{:?}", s);
    assert!(debug_str.contains("Domestic"));
    assert!(debug_str.contains("42"));
    
    s.annex().unwrap();
    let debug_str_exiled = format!("{:?}", s);
    assert!(debug_str_exiled.contains("Exiled"));
    assert!(debug_str_exiled.contains("Inaccessible"));
}
