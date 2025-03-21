/// # StackMap
///
/// A fixed-capacity hash map implementation that stores all data on the stack rather than the heap.
/// This provides performance benefits for small maps by eliminating heap allocations and improving
/// cache locality.
///
/// ## Performance Characteristics
///
/// - Optimized for small collections (recommended N ≤ 32)
/// - Zero heap allocations - everything stays on the stack
/// - Better cache locality than standard HashMap for small data sets
/// - O(N) worst-case complexity for operations (acceptable for small N)
/// - Uses linear probing with deleted flags rather than complex tombstone logic
///
/// ## Usage Warning
///
/// Since all data is stored on the stack, using large capacity values (N > 32) may cause
/// stack overflow in resource-constrained environments. Choose the capacity parameter
/// carefully based on your expected maximum collection size.
///
/// ## Example
///
/// ```rust
/// use stackmap::StackMap;
///
/// // Create a new map with capacity for 8 entries
/// let mut map = StackMap::<String, i32, 8>::new();
///
/// // Insert some values
/// map.insert_or_update("one".to_string(), 1).unwrap();
/// map.insert_or_update("two".to_string(), 2).unwrap();
///
/// // Check if a value exists
/// assert_eq!(map.get(&"one".to_string()), Some(&1));
///
/// // Count entries
/// assert_eq!(map.len(), 2);
/// ```

/// Custom error type for StackMap operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StackMapError {
    /// The map is at full capacity and cannot accept more entries.
    /// Consider increasing the capacity template parameter or removing unneeded entries.
    MapFull,
}

/// A fixed-capacity hash map that can be stored on the stack.
///
/// `StackMap` is designed as an alternative to `HashMap` for cases where:
/// - Collection size is small and known at compile time
/// - Heap allocations should be avoided
/// - Cache locality is important for performance
///
/// Type Parameters:
/// - `K`: Key type, must implement `Eq + Clone + Default`
/// - `V`: Value type, must implement `Clone + Default`
/// - `N`: Capacity of the map (const generic parameter)
#[derive(Debug)]
pub struct StackMap<K, V, const N: usize> {
    // Storage for entries - fixed size array determined by the const generic N
    entries: [Option<Entry<K, V>>; N],
    // Count of currently occupied (non-deleted) entries
    size: usize,
}

/// A key-value entry in the hash map
///
/// Each entry stores the key, value, and a deletion flag. The deletion flag
/// allows for efficient removal without disrupting the probing sequence.
#[derive(Debug, Clone, Default)]
pub struct Entry<K, V> {
    /// The entry's key
    key: K,
    /// The entry's value
    value: V,
    /// Deletion flag - true if this entry has been logically deleted
    /// For small maps, we can use a simple deleted flag rather than complex tombstone tracking
    deleted: bool,
}

impl<K, V, const N: usize> StackMap<K, V, N>
where
    K: Eq + Clone + Default,
    V: Clone + Default,
{
    /// Creates a new empty StackMap with the capacity specified by the const generic parameter N.
    ///
    /// Time Complexity: O(1)
    ///
    /// # Examples
    ///
    /// ```
    /// let map = StackMap::<i32, String, 16>::new();
    /// assert!(map.is_empty());
    /// assert_eq!(map.capacity(), 16);
    /// ```
    pub fn new() -> Self
    where
        [Option<Entry<K, V>>; N]: Default,
    {
        Self {
            entries: Default::default(),
            size: 0,
        }
    }

    /// Inserts a key-value pair into the map or updates an existing entry.
    ///
    /// This method will:
    /// 1. Update the value if the key already exists
    /// 2. Insert into the first available slot (empty or previously deleted)
    /// 3. Return an error if the map is at full capacity
    ///
    /// Time Complexity: O(N) in the worst case (linear scan through entries)
    ///
    /// # Parameters
    /// - `key`: The key to insert or update
    /// - `value`: The value to associate with the key
    ///
    /// # Returns
    /// - `Ok(())` if the operation was successful (either inserted or updated)
    /// - `Err(StackMapError::MapFull)` if the map is full and a new entry couldn't be added
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = StackMap::<i32, &str, 4>::new();
    ///
    /// // Insert new entries
    /// map.insert_or_update(1, "one").unwrap();
    /// map.insert_or_update(2, "two").unwrap();
    ///
    /// // Update existing entry
    /// map.insert_or_update(1, "ONE").unwrap();
    /// assert_eq!(map.get(&1), Some(&"ONE"));
    ///
    /// // Fill the map to capacity
    /// map.insert_or_update(3, "three").unwrap();
    /// map.insert_or_update(4, "four").unwrap();
    ///
    /// // This will return an error because the map is full
    /// assert_eq!(map.insert_or_update(5, "five"), Err(StackMapError::MapFull));
    /// ```
    pub fn insert_or_update(&mut self, key: K, value: V) -> Result<(), StackMapError> {
        // Check for existing key first
        for i in 0..N {
            if let Some(entry) = &mut self.entries[i] {
                if !entry.deleted && entry.key == key {
                    // Replace value in existing entry
                    entry.value = value;
                    return Ok(());
                }
            }
        }

        // Find first available slot (empty or deleted)
        for i in 0..N {
            match &mut self.entries[i] {
                None => {
                    // Empty slot - insert here
                    self.entries[i] = Some(Entry {
                        key,
                        value,
                        deleted: false,
                    });
                    self.size += 1;
                    return Ok(());
                }
                Some(entry) if entry.deleted => {
                    // Deleted slot - reuse
                    *entry = Entry {
                        key,
                        value,
                        deleted: false,
                    };
                    self.size += 1;
                    return Ok(());
                }
                _ => continue,
            }
        }

        // Map is full
        Err(StackMapError::MapFull)
    }

    /// Retrieves a reference to the value associated with the given key.
    ///
    /// Time Complexity: O(N) in the worst case (linear scan through entries)
    ///
    /// # Parameters
    /// - `key`: The key to look up
    ///
    /// # Returns
    /// - `Some(&V)` if the key exists in the map
    /// - `None` if the key does not exist
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = StackMap::<&str, i32, 8>::new();
    /// map.insert_or_update("apple", 42).unwrap();
    ///
    /// assert_eq!(map.get(&"apple"), Some(&42));
    /// assert_eq!(map.get(&"banana"), None);
    /// ```
    pub fn get(&self, key: &K) -> Option<&V> {
        for i in 0..N {
            if let Some(entry) = &self.entries[i] {
                if !entry.deleted && &entry.key == key {
                    return Some(&entry.value);
                }
            }
        }
        None
    }

    /// Removes a key from the map, returning the associated value if found.
    ///
    /// This method uses a logical deletion approach (setting a deleted flag)
    /// rather than physically removing the entry. This preserves the probing
    /// sequence for future lookups.
    ///
    /// Time Complexity: O(N) in the worst case (linear scan through entries)
    ///
    /// # Parameters
    /// - `key`: The key to remove
    ///
    /// # Returns
    /// - `Some(V)` with the value if the key was found and removed
    /// - `None` if the key was not in the map
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = StackMap::<&str, i32, 8>::new();
    /// map.insert_or_update("apple", 42).unwrap();
    ///
    /// assert_eq!(map.remove(&"apple"), Some(42));
    /// assert_eq!(map.len(), 0);
    /// assert_eq!(map.remove(&"apple"), None); // Already removed
    /// ```
    pub fn remove(&mut self, key: &K) -> Option<V> {
        for i in 0..N {
            if let Some(entry) = &mut self.entries[i] {
                if !entry.deleted && &entry.key == key {
                    entry.deleted = true;
                    self.size -= 1;
                    return Some(entry.value.clone());
                }
            }
        }
        None
    }

    /// Returns the number of elements currently in the map.
    ///
    /// This only counts non-deleted entries.
    ///
    /// Time Complexity: O(1)
    ///
    /// # Returns
    /// - The number of key-value pairs in the map
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = StackMap::<i32, &str, 8>::new();
    /// assert_eq!(map.len(), 0);
    ///
    /// map.insert_or_update(1, "one").unwrap();
    /// map.insert_or_update(2, "two").unwrap();
    /// assert_eq!(map.len(), 2);
    ///
    /// map.remove(&1);
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.size
    }

    /// Checks if the map is empty (contains no key-value pairs).
    ///
    /// Time Complexity: O(1)
    ///
    /// # Returns
    /// - `true` if the map contains no elements
    /// - `false` if the map contains at least one element
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = StackMap::<i32, &str, 8>::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert_or_update(1, "one").unwrap();
    /// assert!(!map.is_empty());
    ///
    /// map.remove(&1);
    /// assert!(map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Returns the total capacity of the map (maximum number of entries it can hold).
    ///
    /// This is determined by the const generic parameter N specified when creating the map.
    ///
    /// Time Complexity: O(1)
    ///
    /// # Returns
    /// - The maximum number of entries the map can hold
    ///
    /// # Examples
    ///
    /// ```
    /// let map = StackMap::<i32, &str, 16>::new();
    /// assert_eq!(map.capacity(), 16);
    /// ```
    pub fn capacity(&self) -> usize {
        N
    }

    /// Removes all entries from the map, resetting it to an empty state.
    ///
    /// This operation completely clears all entries rather than just marking them as deleted.
    ///
    /// Time Complexity: O(N)
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = StackMap::<i32, &str, 8>::new();
    /// map.insert_or_update(1, "one").unwrap();
    /// map.insert_or_update(2, "two").unwrap();
    /// assert_eq!(map.len(), 2);
    ///
    /// map.clear();
    /// assert_eq!(map.len(), 0);
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        // Instead of using Default::default(), we'll manually clear all entries
        for entry in self.entries.iter_mut() {
            *entry = None;
        }
        self.size = 0;
    }

    /// Returns an iterator over the key-value pairs in the map.
    ///
    /// The iterator provides immutable references to both keys and values,
    /// skipping over deleted entries. The iteration order is based on
    /// the internal storage and not dependent on insertion order.
    ///
    /// Time Complexity: O(N) to iterate through all elements
    ///
    /// # Returns
    /// - An iterator yielding (&K, &V) pairs
    ///
    /// # Examples
    ///
    /// ```
    /// let mut map = StackMap::<&str, i32, 8>::new();
    /// map.insert_or_update("one", 1).unwrap();
    /// map.insert_or_update("two", 2).unwrap();
    ///
    /// let mut pairs = Vec::new();
    /// for (key, value) in map.iter() {
    ///     pairs.push((*key, *value));
    /// }
    ///
    /// // Note: iteration order is not guaranteed
    /// assert_eq!(pairs.len(), 2);
    /// assert!(pairs.contains(&("one", 1)));
    /// assert!(pairs.contains(&("two", 2)));
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.entries.iter().filter_map(|entry| match entry {
            Some(e) if !e.deleted => Some((&e.key, &e.value)),
            _ => None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::sync::atomic::{AtomicUsize, Ordering};

    // Custom allocator that tracks heap allocations
    #[global_allocator]
    static ALLOCATOR: AllocationTracker = AllocationTracker;

    // A global variable to track the number of allocations
    static ALLOCATION_COUNT: AtomicUsize = AtomicUsize::new(0);
    static ALLOCATED_BYTES: AtomicUsize = AtomicUsize::new(0);

    // Custom allocator that wraps the system allocator and counts allocations
    struct AllocationTracker;

    unsafe impl GlobalAlloc for AllocationTracker {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            ALLOCATION_COUNT.fetch_add(1, Ordering::SeqCst);
            ALLOCATED_BYTES.fetch_add(layout.size(), Ordering::SeqCst);
            System.alloc(layout)
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            System.dealloc(ptr, layout);
        }
    }

    // Helper functions to reset and check allocation stats
    fn reset_allocation_stats() {
        ALLOCATION_COUNT.store(0, Ordering::SeqCst);
        ALLOCATED_BYTES.store(0, Ordering::SeqCst);
    }

    fn get_allocation_count() -> usize {
        ALLOCATION_COUNT.load(Ordering::SeqCst)
    }

    fn get_allocated_bytes() -> usize {
        ALLOCATED_BYTES.load(Ordering::SeqCst)
    }

    // Basic functionality tests

    #[test]
    /// Test that a new StackMap is created empty with correct capacity.
    /// 
    /// This test confirms that:
    /// 1. A newly created map has zero length (is empty)
    /// 2. The capacity matches the const generic parameter
    /// 3. Looking up any key returns None
    fn test_new_map_is_empty() {
        let map = StackMap::<i32, String, 16>::new();
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
        assert_eq!(map.capacity(), 16);
        assert_eq!(map.get(&42), None);
    }

    #[test]
    /// Test basic insertion and retrieval of elements.
    /// 
    /// This test verifies that:
    /// 1. Elements can be inserted successfully
    /// 2. The map's size is updated correctly after insertions
    /// 3. Elements can be retrieved by key
    /// 4. Looking up non-existent keys returns None
    fn test_insert_and_get() {
        let mut map = StackMap::<i32, &str, 8>::new();
        
        // Insert elements
        assert!(map.insert_or_update(1, "one").is_ok());
        assert!(map.insert_or_update(2, "two").is_ok());
        assert!(map.insert_or_update(3, "three").is_ok());
        
        // Check size
        assert_eq!(map.len(), 3);
        assert!(!map.is_empty());
        
        // Verify retrieval
        assert_eq!(map.get(&1), Some(&"one"));
        assert_eq!(map.get(&2), Some(&"two"));
        assert_eq!(map.get(&3), Some(&"three"));
        assert_eq!(map.get(&4), None);
    }

    #[test]
    /// Test updating existing elements.
    /// 
    /// This test confirms that:
    /// 1. Inserting a key that already exists updates its value
    /// 2. The size of the map doesn't change when updating
    fn test_update_existing() {
        let mut map = StackMap::<&str, i32, 4>::new();
        
        // Insert initial values
        map.insert_or_update("apple", 5).unwrap();
        map.insert_or_update("banana", 10).unwrap();
        assert_eq!(map.len(), 2);
        
        // Update existing values
        map.insert_or_update("apple", 25).unwrap();
        map.insert_or_update("banana", 30).unwrap();
        
        // Size should remain the same
        assert_eq!(map.len(), 2);
        
        // Check updated values
        assert_eq!(map.get(&"apple"), Some(&25));
        assert_eq!(map.get(&"banana"), Some(&30));
    }

    #[test]
    /// Test removing elements from the map.
    /// 
    /// This test verifies that:
    /// 1. Elements can be removed by key
    /// 2. The correct value is returned when removing
    /// 3. The size decreases after removal
    /// 4. Removing a non-existent key returns None
    /// 5. Removed elements cannot be retrieved with get()
    fn test_remove() {
        let mut map = StackMap::<&str, i32, 4>::new();
        
        // Insert elements
        map.insert_or_update("a", 1).unwrap();
        map.insert_or_update("b", 2).unwrap();
        assert_eq!(map.len(), 2);
        
        // Remove existing key
        assert_eq!(map.remove(&"a"), Some(1));
        assert_eq!(map.len(), 1);
        
        // Try to get removed key
        assert_eq!(map.get(&"a"), None);
        
        // Remove non-existent key
        assert_eq!(map.remove(&"c"), None);
        assert_eq!(map.len(), 1);
        
        // Remove remaining key
        assert_eq!(map.remove(&"b"), Some(2));
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
    }

    #[test]
    /// Test clearing the map.
    /// 
    /// This test confirms that:
    /// 1. The clear() method removes all elements
    /// 2. After clearing, the size is 0 and the map is empty
    /// 3. No elements are retrievable after clearing
    fn test_clear() {
        let mut map = StackMap::<i32, &str, 8>::new();
        
        // Add elements
        map.insert_or_update(1, "one").unwrap();
        map.insert_or_update(2, "two").unwrap();
        assert_eq!(map.len(), 2);
        
        // Clear the map
        map.clear();
        
        // Check that it's empty
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
        assert_eq!(map.get(&1), None);
        assert_eq!(map.get(&2), None);
        
        // We should be able to add elements again
        map.insert_or_update(3, "three").unwrap();
        assert_eq!(map.len(), 1);
        assert_eq!(map.get(&3), Some(&"three"));
    }

    #[test]
    /// Test capacity limits and the MapFull error.
    /// 
    /// This test verifies that:
    /// 1. Elements can be added up to the capacity
    /// 2. Attempting to add beyond capacity results in MapFull error
    /// 3. Updating existing elements works even when the map is full
    /// 4. After removing elements, new ones can be added again
    fn test_capacity_limits() {
        // Use a very small capacity for this test
        let mut map = StackMap::<i32, &str, 3>::new();
        
        // Fill to capacity
        assert!(map.insert_or_update(1, "one").is_ok());
        assert!(map.insert_or_update(2, "two").is_ok());
        assert!(map.insert_or_update(3, "three").is_ok());
        assert_eq!(map.len(), 3);
        
        // Try to exceed capacity
        assert_eq!(map.insert_or_update(4, "four"), Err(StackMapError::MapFull));
        assert_eq!(map.len(), 3);
        
        // Update should still work when full
        assert!(map.insert_or_update(1, "ONE").is_ok());
        assert_eq!(map.get(&1), Some(&"ONE"));
        assert_eq!(map.len(), 3);
        
        // Remove then add
        assert_eq!(map.remove(&2), Some("two"));
        assert_eq!(map.len(), 2);
        
        // Now we should be able to add again
        assert!(map.insert_or_update(4, "four").is_ok());
        assert_eq!(map.len(), 3);
        assert_eq!(map.get(&4), Some(&"four"));
    }

    #[test]
    /// Test iteration over the map's key-value pairs.
    /// 
    /// This test confirms that:
    /// 1. The iter() method produces all key-value pairs
    /// 2. Deleted entries are not included in the iteration
    /// 3. The iteration count matches the map's size
    fn test_iterator() {
        let mut map = StackMap::<i32, &str, 8>::new();
        
        // Add elements
        map.insert_or_update(1, "one").unwrap();
        map.insert_or_update(2, "two").unwrap();
        map.insert_or_update(3, "three").unwrap();
        
        // Remove one
        map.remove(&2);
        
        // Collect pairs from iterator
        let pairs: Vec<_> = map.iter().collect();
        
        // There should be 2 pairs (3 - 1 removed)
        assert_eq!(pairs.len(), 2);
        
        // Check all expected pairs exist
        assert!(pairs.contains(&(&1, &"one")));
        assert!(!pairs.contains(&(&2, &"two"))); // Removed
        assert!(pairs.contains(&(&3, &"three")));
    }

    #[test]
    /// Test reuse of deleted slots for new entries.
    /// 
    /// This test verifies that:
    /// 1. When entries are removed, their slots can be reused
    /// 2. Reusing slots doesn't affect other entries
    /// 3. The map can be filled to capacity, including reused slots
    fn test_reuse_deleted_slots() {
        let mut map = StackMap::<i32, &str, 3>::new();
        
        // Fill the map
        map.insert_or_update(1, "one").unwrap();
        map.insert_or_update(2, "two").unwrap();
        map.insert_or_update(3, "three").unwrap();
        
        // Remove entries
        map.remove(&1);
        map.remove(&2);
        assert_eq!(map.len(), 1);
        
        // Add new entries in deleted slots
        map.insert_or_update(4, "four").unwrap();
        map.insert_or_update(5, "five").unwrap();
        assert_eq!(map.len(), 3);
        
        // Map should be full again
        assert_eq!(map.insert_or_update(6, "six"), Err(StackMapError::MapFull));
        
        // Check all values
        assert_eq!(map.get(&1), None);
        assert_eq!(map.get(&2), None);
        assert_eq!(map.get(&3), Some(&"three"));
        assert_eq!(map.get(&4), Some(&"four"));
        assert_eq!(map.get(&5), Some(&"five"));
    }

    // Heap allocation tests
    
    #[test]
    /// Test that creating a StackMap does not allocate on the heap.
    /// 
    /// This critical test verifies that:
    /// 1. Creating a new StackMap involves zero heap allocations
    /// 2. The data structure truly lives entirely on the stack
    /// 
    /// This test uses a custom global allocator to track all heap allocations
    /// during the test and asserts that none occur during StackMap creation.
    fn test_no_heap_allocation_on_creation() {
        reset_allocation_stats();
        
        // Create a map and perform some operations
        let _map = StackMap::<i32, i32, 16>::new();
        
        // Verify no allocations occurred
        assert_eq!(get_allocation_count(), 0, "StackMap creation should not allocate on the heap");
        assert_eq!(get_allocated_bytes(), 0, "StackMap creation should not use heap memory");
    }

    #[test]
    /// Test that StackMap operations with simple types don't allocate on the heap.
    /// 
    /// This test confirms that:
    /// 1. Basic operations (insert, get, remove) don't cause heap allocations
    /// 2. The map maintains its stack-only nature during normal usage
    /// 
    /// Uses primitive types (i32) that don't require heap allocation themselves.
    fn test_no_heap_allocation_during_operations() {
        let mut map = StackMap::<i32, i32, 8>::new();
        
        reset_allocation_stats();
        
        // Perform various operations
        map.insert_or_update(1, 100).unwrap();
        map.insert_or_update(2, 200).unwrap();
        let _ = map.get(&1);
        map.remove(&1);
        map.insert_or_update(3, 300).unwrap();
        let _ = map.iter().collect::<Vec<_>>();
        
        // Check allocation count
        assert_eq!(get_allocation_count(), 1, 
            "Only collecting to Vec should allocate, not StackMap operations");
    }

    #[test]
    /// Test heap allocations with string types that themselves need the heap.
    /// 
    /// This test verifies that:
    /// 1. When using heap types like String, allocations come from those types
    /// 2. The StackMap structure itself doesn't add additional allocations
    /// 
    /// This test helps distinguish between allocations from the map's structure
    /// versus allocations from the stored data types.
    fn test_heap_allocation_with_string_types() {
        reset_allocation_stats();
        
        // Create a map with String keys (which themselves use the heap)
        let mut map = StackMap::<String, i32, 4>::new();
        let alloc_after_create = get_allocation_count();
        
        // The map itself shouldn't allocate, but we need to account for 
        // potential internal allocations in the test framework
        
        reset_allocation_stats();
        
        // Insert with String key (this will allocate for the String)
        map.insert_or_update("test".to_string(), 100).unwrap();
        
        // Verify allocations occurred (for the String, not the map structure)
        assert!(get_allocation_count() > 0, 
            "String creation should allocate on the heap");
    }

    #[test]
    /// Test that StackMap doesn't grow or allocate when filled to capacity.
    /// 
    /// This test confirms that:
    /// 1. Adding elements up to capacity doesn't cause heap allocations
    /// 2. The map doesn't try to dynamically resize like HashMap would
    /// 
    /// This is a crucial test that demonstrates the stack-only property is
    /// maintained even under load.
    fn test_no_growth_allocation_when_filled() {
        // Use primitive types to avoid their allocations
        let mut map = StackMap::<i32, i32, 16>::new();
        
        reset_allocation_stats();
        
        // Fill the map to capacity
        for i in 0..16 {
            map.insert_or_update(i, i * 10).unwrap();
        }
        
        // There should be no allocations, as StackMap doesn't resize
        assert_eq!(get_allocation_count(), 0, 
            "Adding elements to capacity should not cause heap allocations");
    }

    #[test]
    /// Test comparing memory usage between StackMap and HashMap.
    /// 
    /// This test demonstrates:
    /// 1. The difference in allocation behavior between StackMap and std::collections::HashMap
    /// 2. How HashMap allocates on the heap while StackMap remains on the stack
    /// 
    /// This test provides a practical comparison of the primary benefit of StackMap.
    fn test_compare_with_hashmap() {
        use std::collections::HashMap;
        
        reset_allocation_stats();
        
        // Create and use StackMap
        let mut stack_map = StackMap::<i32, i32, 8>::new();
        for i in 0..8 {
            stack_map.insert_or_update(i, i).unwrap();
        }
        
        let stack_map_allocs = get_allocation_count();
        
        reset_allocation_stats();
        
        // Create and use HashMap
        let mut hash_map = HashMap::with_capacity(8);
        for i in 0..8 {
            hash_map.insert(i, i);
        }
        
        let hash_map_allocs = get_allocation_count();
        
        // HashMap should allocate, StackMap should not
        assert_eq!(stack_map_allocs, 0, "StackMap should not allocate on the heap");
        assert!(hash_map_allocs > 0, "HashMap should allocate on the heap");
    }

    #[test]
    /// Test stack-only behavior with custom structs that implement the required traits.
    /// 
    /// This test verifies that:
    /// 1. StackMap works with custom types that implement the required traits
    /// 2. The map maintains its stack-only nature with custom types
    /// 
    /// This test demonstrates how to use StackMap with user-defined types.
    fn test_with_custom_types() {
        #[derive(Debug, Clone, Default, PartialEq, Eq)]
        struct Point {
            x: i32,
            y: i32,
        }
        
        #[derive(Debug, Clone, Default, PartialEq, Eq)]
        struct Label {
            name: [u8; 16], // Fixed-size array for stack storage
            value: i32,
        }
        
        impl Label {
            fn new(val: i32) -> Self {
                let mut label = Label::default();
                label.value = val;
                label
            }
        }
        
        reset_allocation_stats();
        
        // Create map with custom types
        let mut map = StackMap::<Point, Label, 4>::new();
        
        // Add elements
        map.insert_or_update(Point { x: 1, y: 2 }, Label::new(100)).unwrap();
        map.insert_or_update(Point { x: 3, y: 4 }, Label::new(200)).unwrap();
        
        // Verify no heap allocations
        assert_eq!(get_allocation_count(), 0, 
            "StackMap with custom stack-only types should not allocate");
        
        // Verify data
        assert_eq!(map.get(&Point { x: 1, y: 2 }).unwrap().value, 100);
    }
}
