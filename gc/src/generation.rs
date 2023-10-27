use std::collections::{HashMap, HashSet};

use super::{Pointer, Value};
use std::result::Result;

pub trait Generation {
    /// Allocates a new pointer to an array of value of the given size.
    /// Returns the pointer to the first element of the array or
    /// an error if there is not enough space.
    ///
    /// Does not perform collection.
    fn alloc(&mut self, amount: usize) -> Result<Pointer, ()>;
    /// Moves the given data into this generation.
    /// Returns a pointer to the first element of the data or
    fn memmove(&mut self, data: &[Value]) -> Result<Pointer, ()>;
    /// Returns true if the given pointer is contained in this generation.
    fn contains(&self, key: &Pointer) -> bool;
    /// Returns the amount of free space (in # values) in this generation.
    fn free_space(&self) -> usize;
    /// Returns true if this generation should be collected.
    fn should_collect(&self) -> bool;
    /// Performs a collection of this generation.
    fn collect(
        &mut self,
        roots: &[Pointer],
        masks: &[usize],
    ) -> Vec<(Pointer, &[Value])>;
    /// Writes the given value to the given pointer.
    /// Returns an error if the pointer is not contained in this generation.
    fn write(&mut self, key: &Pointer, val: Value) -> Result<(), ()>;
    /// Reads the value at the given pointer.
    /// Returns an error if the pointer is not contained in this generation.
    fn read(&self, key: &Pointer) -> Result<&Value, ()>;

    /// Returns masks of pointers' bases that are not managed by this generation but are
    /// pointed to by pointers in this generation.
    fn remembered_masks(&self, heap_idx: u8) -> Vec<usize>;

    /// Updates the pointer at `old_ptr` to `new_ptr` where
    /// `old_ptr` is a pointer that is managed by another generation.
    fn update_ptr(&mut self, old_ptr: &Pointer, new_ptr: Pointer);

    /// Returns true if this generation is empty.
    fn is_empty(&self) -> bool;

    /// Returns a tuple of the number of allocations and number of values
    /// allocated in this generation.
    fn len(&self) -> (usize, usize);

    /// Returns the number of collections this generation has undergone.
    fn num_collections(&self) -> usize;

    /// Returns the number of promotions this generation has undergone.
    fn num_promotions(&self) -> usize;

    /// Returns the number of pointers stored in this generation that point to
    /// a different generation
    fn num_remembered(&self) -> usize;
}

const WB_CACHE_SIZE: usize = 256;
const WB_CACHE_MASK: usize = WB_CACHE_SIZE - 1;
/// A generational write barrier which keeps track of the remembered set, the
/// set of pointers in this generation that point to other generations.
struct WriteBarrier {
    /// map heap index to direct mapped cache of reference counts
    /// The index in the cache is mask of all base pointers the reference count belongs to
    remembered_sets: HashMap<u8, [usize; WB_CACHE_SIZE]>,
    cur_idx: u8,
}

impl WriteBarrier {
    /// Updates the write barrier with the given write.
    fn on_write(&mut self, old_val: Option<&Value>, val: &Value) {
        if let Some(old_val) = old_val {
            self.dec(old_val);
        }
        self.inc(val);
    }

    /// Decrements the refcount for a value, `v`, outside this generation.
    fn dec(&mut self, v: &Value) {
        if let Value::Pointer(p) = v {
            if p.heap_id != self.cur_idx {
                if let Some(cache) = self.remembered_sets.get_mut(&p.heap_id) {
                    cache[p.base & WB_CACHE_MASK] -= 1;
                }
            }
        }
    }

    /// Increments the refcount for a value, `v`, outside this generation.
    fn inc(&mut self, v: &Value) {
        if let Value::Pointer(p) = v {
            if p.heap_id != self.cur_idx {
                self.remembered_sets
                    .entry(p.heap_id)
                    .or_insert_with(|| [0; WB_CACHE_SIZE])
                    [p.base & WB_CACHE_MASK] += 1;
            }
        }
    }

    /// Increments the refcount for all values in `data` outside this generation.
    fn inc_all(&mut self, data: &[Value]) {
        for v in data {
            self.inc(v);
        }
    }

    /// Decrements the refcount for all values in `data` outside this generation.
    fn dec_all(&mut self, data: &[Value]) {
        for v in data {
            self.dec(v);
        }
    }

    /// Returns the masks of alive pointers in `heap_idx` which are pointed to by
    /// pointers in this generation.
    fn remembered_masks(&self, heap_idx: u8) -> Vec<usize> {
        let mut res = vec![];
        if let Some(cache) = self.remembered_sets.get(&heap_idx) {
            for (i, &count) in cache.iter().enumerate() {
                if count > 0 {
                    res.push(i);
                }
            }
        }
        res
    }

    fn num_refs(&self) -> usize {
        let mut refs = 0;
        for cache in self.remembered_sets.values() {
            refs += cache.iter().sum::<usize>();
        }
        refs
    }

    fn new(cur_idx: u8) -> Self {
        Self {
            remembered_sets: HashMap::new(),
            cur_idx,
        }
    }

    /// Clears the remembered set.
    fn clear_all(&mut self) {
        self.remembered_sets.clear();
    }
}

/// A copying collection generation
pub struct CopyingGen {
    space: Box<[Value]>,
    cur_idx: usize,
    heap_id: u8,
    wb: WriteBarrier,
    /// Map from pointer bases to the amount of space allocated for that pointer.
    allocated: HashMap<usize, usize>,
    num_collections: usize,
    num_promotions: usize,
}

impl CopyingGen {
    pub fn new(size: usize, heap_id: u8) -> Self {
        Self {
            space: vec![Value::Uninitialized; size].into_boxed_slice(),
            cur_idx: 0,
            heap_id,
            wb: WriteBarrier::new(heap_id),
            allocated: HashMap::new(),
            num_collections: 0,
            num_promotions: 0,
        }
    }
}

impl Generation for CopyingGen {
    fn len(&self) -> (usize, usize) {
        (self.allocated.len(), self.cur_idx)
    }

    fn num_promotions(&self) -> usize {
        self.num_promotions
    }

    fn num_collections(&self) -> usize {
        self.num_collections
    }

    fn alloc(&mut self, amount: usize) -> Result<Pointer, ()> {
        if amount < self.free_space() {
            let ptr = Pointer {
                heap_id: self.heap_id,
                base: self.cur_idx,
                offset: 0,
            };
            self.allocated.insert(self.cur_idx, amount);
            self.cur_idx += amount;
            Ok(ptr)
        } else {
            Err(())
        }
    }

    fn memmove(&mut self, data: &[Value]) -> Result<Pointer, ()> {
        let ptr = self.alloc(data.len())?;
        self.space[ptr.base..ptr.base + data.len()].copy_from_slice(data);
        self.wb.inc_all(data);
        Ok(ptr)
    }

    fn contains(&self, key: &Pointer) -> bool {
        key.heap_id == self.heap_id
    }

    fn free_space(&self) -> usize {
        self.space.len() - self.cur_idx
    }

    fn should_collect(&self) -> bool {
        self.free_space() == 0
    }

    fn is_empty(&self) -> bool {
        self.cur_idx == 0
    }

    fn collect(
        &mut self,
        roots: &[Pointer],
        masks: &[usize],
    ) -> Vec<(Pointer, &[Value])> {
        let mut to_visit = roots.to_vec();
        for base_ptr in self.allocated.keys() {
            for mask in masks {
                if mask & base_ptr == *mask {
                    to_visit.push(Pointer {
                        heap_id: self.heap_id,
                        base: *base_ptr,
                        offset: 0,
                    });
                    break;
                }
            }
        }
        let mut visited = HashSet::new();
        self.num_collections += 1;
        while let Some(ptr) = to_visit.pop() {
            if !visited.contains(&ptr) {
                visited.insert(ptr);
                if let Some(sz) = self.allocated.get(&ptr.base) {
                    #[allow(
                        clippy::cast_possible_truncation,
                        clippy::cast_sign_loss
                    )]
                    for v in ptr.base..ptr.base + sz {
                        let val = &self.space[v];
                        if let Value::Pointer(p) = val {
                            if p.heap_id == self.heap_id {
                                to_visit.push(*p);
                            }
                        }
                    }
                }
            }
        }
        let res = visited
            .iter()
            .filter(|p| p.heap_id == self.heap_id)
            .map(|p| {
                (*p, {
                    let sz = self.allocated.get(&p.base).unwrap();
                    &self.space[p.base..p.base + sz]
                })
            })
            .collect();
        self.cur_idx = 0;
        self.wb.clear_all();
        self.allocated.clear();
        self.num_promotions += visited.len();
        res
    }

    fn write(&mut self, key: &Pointer, val: Value) -> Result<(), ()> {
        let idx: usize =
            (key.base as i64 + key.offset).try_into().map_err(|_| ())?;
        if key.heap_id == self.heap_id
            && key.base as i64 + key.offset >= 0
            && idx < self.space.len()
        {
            self.wb.on_write(
                if self.cur_idx > idx {
                    Some(&self.space[idx])
                } else {
                    None
                },
                &val,
            );
            self.space[idx] = val;
            Ok(())
        } else {
            Err(())
        }
    }

    fn read(&self, key: &Pointer) -> Result<&Value, ()> {
        let idx: usize =
            (key.base as i64 + key.offset).try_into().map_err(|_| ())?;
        if key.heap_id == self.heap_id
            && key.base as i64 + key.offset >= 0
            && idx < self.space.len()
        {
            Ok(&self.space[idx])
        } else {
            Err(())
        }
    }

    fn remembered_masks(&self, heap_idx: u8) -> Vec<usize> {
        self.wb.remembered_masks(heap_idx)
    }

    fn num_remembered(&self) -> usize {
        self.wb.num_refs()
    }

    fn update_ptr(&mut self, old_ptr: &Pointer, new_ptr: Pointer) {
        for i in 0..self.cur_idx {
            if matches!(self.space[i], Value::Pointer(old_p) if old_p == *old_ptr)
            {
                self.space[i] = Value::Pointer(new_ptr);
                self.wb.on_write(
                    Some(&Value::Pointer(*old_ptr)),
                    &Value::Pointer(new_ptr),
                );
            }
        }
    }
}

/// A generation which does not promote pointers to the next generation.
pub struct ElderGen {
    allocations: HashMap<usize, Box<[Value]>>,
    heap_id: u8,
    collection_thresh: usize,
    wb: WriteBarrier,
    num_collections: usize,
}

impl ElderGen {
    pub fn new(collection_thresh: usize, heap_id: u8) -> Self {
        Self {
            allocations: HashMap::new(),
            heap_id,
            collection_thresh,
            wb: WriteBarrier::new(heap_id),
            num_collections: 0,
        }
    }
}

impl Generation for ElderGen {
    fn alloc(&mut self, amount: usize) -> Result<Pointer, ()> {
        let p = Pointer {
            heap_id: self.heap_id,
            base: self.allocations.len(),
            offset: 0,
        };
        self.allocations.insert(
            p.base,
            vec![Value::Uninitialized; amount].into_boxed_slice(),
        );
        Ok(p)
    }

    fn num_promotions(&self) -> usize {
        0
    }

    fn num_remembered(&self) -> usize {
        self.wb.num_refs()
    }

    fn num_collections(&self) -> usize {
        self.num_collections
    }

    fn len(&self) -> (usize, usize) {
        (
            self.allocations.len(),
            self.allocations.values().map(|v| v.len()).sum(),
        )
    }

    fn memmove(&mut self, data: &[Value]) -> Result<Pointer, ()> {
        let new_p = Pointer {
            heap_id: self.heap_id,
            base: self.allocations.len(),
            offset: 0,
        };
        self.allocations
            .insert(self.allocations.len(), data.to_vec().into_boxed_slice());
        self.wb.inc_all(data);
        Ok(new_p)
    }

    fn contains(&self, key: &Pointer) -> bool {
        key.heap_id == self.heap_id
    }

    fn free_space(&self) -> usize {
        usize::MAX
    }

    fn should_collect(&self) -> bool {
        self.allocations.len() >= self.collection_thresh
    }

    fn collect(
        &mut self,
        roots: &[Pointer],
        masks: &[usize],
    ) -> Vec<(Pointer, &[Value])> {
        let mut to_visit = roots.to_vec();
        let mut visited = HashSet::new();
        for base_ptr in self.allocations.keys() {
            for mask in masks {
                if mask & base_ptr == *mask {
                    to_visit.push(Pointer {
                        heap_id: self.heap_id,
                        base: *base_ptr,
                        offset: 0,
                    });
                    break;
                }
            }
        }
        self.num_collections += 1;
        while let Some(ptr) = to_visit.pop() {
            if !visited.contains(&ptr) {
                visited.insert(ptr);
                if let Some(val) = self.allocations.get(&ptr.base) {
                    for v in val.iter() {
                        if let Value::Pointer(p) = v {
                            if p.heap_id == self.heap_id {
                                to_visit.push(*p);
                            }
                        }
                    }
                }
            }
        }
        let mut to_delete = HashSet::new();
        for b in self.allocations.keys() {
            if !visited.contains(&Pointer {
                heap_id: self.heap_id,
                base: *b,
                offset: 0,
            }) {
                to_delete.insert(*b);
                self.wb.dec_all(&self.allocations[b]);
            }
        }
        self.allocations.retain(|b, _| !to_delete.contains(b));
        vec![]
    }

    fn write(&mut self, key: &Pointer, val: Value) -> Result<(), ()> {
        let offset: usize = key.offset.try_into().map_err(|_| ())?;
        if key.heap_id == self.heap_id
            && self.allocations.contains_key(&key.base)
            && key.offset >= 0
            && self.allocations[&key.base].len() > offset
        {
            self.wb.on_write(
                self.allocations.get(&key.base).map(|a| &a[offset]),
                &val,
            );
            self.allocations.get_mut(&key.base).unwrap()[offset] = val;
            Ok(())
        } else {
            Err(())
        }
    }

    fn read(&self, key: &Pointer) -> Result<&Value, ()> {
        let offset: usize = key.offset.try_into().map_err(|_| ())?;
        if key.heap_id == self.heap_id
            && self.allocations.contains_key(&key.base)
            && key.offset >= 0
            && self.allocations[&key.base].len() > offset
        {
            Ok(&self.allocations[&key.base][offset])
        } else {
            Err(())
        }
    }

    fn remembered_masks(&self, heap_idx: u8) -> Vec<usize> {
        self.wb.remembered_masks(heap_idx)
    }

    fn update_ptr(&mut self, old_ptr: &Pointer, new_ptr: Pointer) {
        for alloc in self.allocations.values_mut() {
            for old_val in alloc.iter_mut() {
                if matches!(old_val, Value::Pointer(p) if p == old_ptr) {
                    self.wb.on_write(
                        Some(&Value::Pointer(*old_ptr)),
                        &Value::Pointer(new_ptr),
                    );
                    *old_val = Value::Pointer(new_ptr);
                }
            }
        }
    }

    fn is_empty(&self) -> bool {
        self.allocations.is_empty()
    }
}
