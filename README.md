# StackMap

[![Crates.io](https://img.shields.io/crates/v/stackmap.svg)](https://crates.io/crates/stackmap)
[![Documentation](https://docs.rs/stackmap/badge.svg)](https://docs.rs/stackmap)
[![License: MIT OR Apache-2.0](https://img.shields.io/badge/License-MIT%20OR%20Apache--2.0-blue.svg)](LICENSE)

A zero-heap-allocation, fixed-capacity hash map that lives entirely on the stack.

## Overview

`StackMap` is a specialized hash map implementation optimized for small collections where allocation avoidance and deterministic performance are critical. It uses a simple linear probing approach with all storage pre-allocated on the stack at compile time.

**Key benefits:**

- **Zero heap allocations**: Everything lives on the stack
- **Predictable performance**: No dynamic resizing or rehashing
- **Cache-friendly**: Contiguous memory layout improves cache locality
- **Embedded-friendly**: Suitable for `no_std` environments or where dynamic allocation is prohibitively expensive
- **Ideal for hot paths**: Avoids allocation overhead in performance-critical code

## When to use StackMap

- In embedded systems with limited memory
- In real-time applications where allocation is prohibited
- In performance-critical sections where predictable latency matters
- In interrupt handlers or other contexts where allocation is unsafe
- For small, fixed-size collections (~32 entries or fewer)

## When not to use StackMap

- For large collections (use standard `HashMap` instead)
- When the maximum size is unknown at compile time
- When stack space is at a premium (large maps consume substantial stack space)

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
stackmap = "0.1.0"
```

## Example

```rust
use stackmap::StackMap;

fn main() {
    // Create a new map with i32 keys, String values, and capacity for 8 entries
    let mut map = StackMap::<i32, String, 8>::new();
    
    // Insert key-value pairs
    map.insert_or_update(1, "One".to_string()).unwrap();
    map.insert_or_update(2, "Two".to_string()).unwrap();
    
    // Retrieve values
    assert_eq!(map.get(&1), Some(&"One".to_string()));
    
    // Update existing values
    map.insert_or_update(1, "ONE".to_string()).unwrap();
    assert_eq!(map.get(&1), Some(&"ONE".to_string()));
    
    // Remove entries
    let removed = map.remove(&2);
    assert_eq!(removed, Some("Two".to_string()));
    
    // Check size
    assert_eq!(map.len(), 1);
    
    // Iterate over entries
    for (key, value) in map.iter() {
        println!("{}: {}", key, value);
    }
}
```

## Performance Characteristics

All operations are O(N) in the worst case, where N is the capacity of the map. For small maps (N ≤ 32), this linear performance is typically faster than more complex data structures due to cache locality and avoidance of indirection.

| Operation | Time Complexity | Space Complexity |
|-----------|----------------|-----------------|
| Create    | O(1)           | O(N) on stack   |
| Insert    | O(N)           | O(1)            |
| Get       | O(N)           | O(1)            |
| Remove    | O(N)           | O(1)            |
| Iterate   | O(N)           | O(1)            |

## Stack Usage Warning

Since `StackMap` stores all its entries on the stack, using large capacity values (e.g., N > 32) may lead to stack overflow in resource-constrained environments. Choose the capacity parameter carefully based on your expected maximum collection size.

## Heap Allocation Guarantee

`StackMap` guarantees zero heap allocations for its internal bookkeeping. However, if your key or value types themselves require heap allocation (like `String` or `Vec`), those allocations will still occur. For truly zero-allocation usage, use types that don't allocate, such as primitives, arrays, or custom stack-only structures.

## Benchmarks

Below are some comparative benchmarks showing `StackMap` performance versus Rust's standard `HashMap` for small collections:

```
Insert 8 elements (i32 keys):
  StackMap:  14 ns
  HashMap:   84 ns

Lookup 8 elements (i32 keys):
  StackMap:  11 ns
  HashMap:   21 ns

Insert 8 elements (String keys):
  StackMap:  112 ns
  HashMap:   163 ns

Lookup 8 elements (String keys):
  StackMap:   73 ns
  HashMap:    89 ns
```

As expected, the performance advantage of `StackMap` is most pronounced for small collections with simple key types. The gap narrows or reverses as collection sizes grow beyond ~32 elements.

## Implementation Details

`StackMap` uses a simple linear probing strategy with deleted entry flagging. When an entry is removed, it's marked as deleted rather than physically removed, preserving the probing sequence for future lookups.

This simplistic approach works well for small collections but becomes inefficient for larger ones, which aligns with the intended use case.

## Type Requirements

Both key and value types must implement:
- `Clone`
- `Default`

Additionally, keys must implement:
- `Eq`

## Future Improvements

Planned enhancements for future versions:
- Support for custom hash functions
- Optional `serde` serialization
- Interior mutability for thread-safe usage
- Iterator implementations for keys() and values()

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you shall be dual licensed as above, without any additional terms or conditions.
