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
    fn collect(&mut self, roots: &[Pointer]) -> Vec<(Pointer, &[Value])>;
    /// Writes the given value to the given pointer.
    /// Returns an error if the pointer is not contained in this generation.
    fn write(&mut self, key: &Pointer, val: Value) -> Result<(), ()>;
    /// Reads the value at the given pointer.
    /// Returns an error if the pointer is not contained in this generation.
    fn read(&self, key: &Pointer) -> Result<&Value, ()>;

    /// Returns pointers that are not managed by this generation but are
    /// pointed to by pointers in this generation.
    fn remembered_set(&self) -> Vec<Pointer>;

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
}

/// A generational write barrier which keeps track of the remembered set, the
/// set of pointers in this generation that point to other generations.
struct WriteBarrier {
    /// map from pointers in this generation to pointers in other generations
    remembered_sets: HashMap<Pointer, Pointer>,
}

impl WriteBarrier {
    /// Updates the write barrier with the given write.
    fn on_write(&mut self, key: &Pointer, val: Value) {
        match &val {
            Value::Pointer(p) => {
                if p.heap_id != key.heap_id {
                    self.remembered_sets.insert(*key, *p);
                }
            }
            _ => {
                self.remembered_sets.remove(key);
            }
        }
    }

    /// Returns pointers that are part of the current generation that point to `old_ptr`.
    fn stored_ptrs(&self, old_ptr: &Pointer) -> Vec<Pointer> {
        let mut vc = vec![];
        for (k, v) in &self.remembered_sets {
            if v == old_ptr {
                vc.push(*k);
            }
        }
        vc
    }

    fn new() -> Self {
        Self {
            remembered_sets: HashMap::new(),
        }
    }

    /// Clears the remembered set.
    fn clear_all(&mut self) {
        self.remembered_sets.clear();
    }

    /// Clears the given pointers from the remembered set.
    fn clear(&mut self, p: &Pointer) {
        self.remembered_sets.remove(p);
    }

    /// Returns pointers in the remembered set that point to pointers of the given heap id.
    /// This will return a vec of pointers in `heap_idx` that are pointed to by
    /// pointers in this generation.
    fn remembered_set(&self) -> Vec<Pointer> {
        self.remembered_sets.values().copied().collect()
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
            wb: WriteBarrier::new(),
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

    fn collect(&mut self, roots: &[Pointer]) -> Vec<(Pointer, &[Value])> {
        let mut promotions = self.allocated.clone();
        let mut to_visit = roots.to_vec();
        let mut visited = HashSet::new();
        self.num_collections += 1;
        while let Some(ptr) = to_visit.pop() {
            if !visited.contains(&ptr) {
                visited.insert(ptr);
                promotions.remove(&ptr.base);
                if let Some(val) = self.allocated.get(&ptr.base) {
                    #[allow(
                        clippy::cast_possible_truncation,
                        clippy::cast_sign_loss
                    )]
                    for v in *val..(*val as i64 + ptr.offset) as usize {
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
        self.cur_idx = 0;
        self.wb.clear_all();
        self.allocated.clear();
        self.num_promotions += promotions.len();
        promotions
            .iter()
            .map(|(&base, &size)| {
                (
                    Pointer {
                        heap_id: self.heap_id,
                        base,
                        offset: 0,
                    },
                    &self.space[base..base + size],
                )
            })
            .collect()
    }

    fn write(&mut self, key: &Pointer, val: Value) -> Result<(), ()> {
        let idx: usize =
            (key.base as i64 + key.offset).try_into().map_err(|_| ())?;
        if key.heap_id == self.heap_id
            && key.base as i64 + key.offset >= 0
            && idx < self.space.len()
        {
            self.wb.on_write(key, val);
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

    fn remembered_set(&self) -> Vec<Pointer> {
        self.wb.remembered_set()
    }

    fn update_ptr(&mut self, old_ptr: &Pointer, new_ptr: Pointer) {
        for ptr in self.wb.stored_ptrs(old_ptr) {
            self.write(&ptr, Value::Pointer(new_ptr)).unwrap();
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
            wb: WriteBarrier::new(),
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
        let p = Pointer {
            heap_id: self.heap_id,
            base: self.allocations.len(),
            offset: 0,
        };
        self.allocations
            .insert(self.allocations.len(), data.to_vec().into_boxed_slice());
        Ok(p)
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

    fn collect(&mut self, roots: &[Pointer]) -> Vec<(Pointer, &[Value])> {
        let mut to_visit = roots.to_vec();
        let mut visited = HashSet::new();
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
                self.wb.clear(&Pointer {
                    heap_id: self.heap_id,
                    base: *b,
                    offset: 0,
                });
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
            self.wb.on_write(key, val);
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

    fn remembered_set(&self) -> Vec<Pointer> {
        self.wb.remembered_set()
    }

    fn update_ptr(&mut self, old_ptr: &Pointer, new_ptr: Pointer) {
        for ptr in self.wb.stored_ptrs(old_ptr) {
            self.write(&ptr, Value::Pointer(new_ptr)).unwrap();
        }
    }

    fn is_empty(&self) -> bool {
        self.allocations.is_empty()
    }
}
