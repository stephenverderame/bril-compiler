#![warn(clippy::all, clippy::pedantic, clippy::nursery)]

use std::{collections::HashSet, fmt, slice};
pub mod error;

mod generation;
use error::InterpError;
use generation::{CopyingGen, ElderGen, Generation};

#[derive(Default, Debug)]
pub struct GenStats {
    pub num_collections: usize,
    pub num_size: usize,
    pub num_remembered_set: usize,
    pub free_space: usize,
    pub values_allocated: usize,
    pub num_promotions: usize,
}

impl std::fmt::Display for GenStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "[")?;
        writeln!(f, "\tNumber of collections: {}", self.num_collections)?;
        writeln!(f, "\tNumber of values: {}", self.num_size)?;
        writeln!(f, "\tRemembered Set: {}", self.num_remembered_set)?;
        writeln!(f, "\tFree space: {}", self.free_space)?;
        writeln!(f, "\tValues allocated: {}", self.values_allocated)?;
        writeln!(f, "\tNumber of promotions: {}", self.num_promotions)?;
        writeln!(f, "]")
    }
}

#[derive(Default, Debug)]
pub struct MemStats {
    pub gen_stats: Vec<GenStats>,
    pub memory_leak: bool,
}

impl std::fmt::Display for MemStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, gs) in self.gen_stats.iter().enumerate() {
            write!(f, "g{i}: {gs}")?;
        }
        Ok(())
    }
}

/// An object which manages the interpreter heap
pub trait MemoryManager {
    /// Allocates the given amount of memory and returns a pointer to it
    /// # Errors
    /// Returns an error if the memory manager cannot allocate the given amount
    fn alloc(
        &mut self,
        amount: i64,
        roots: &mut [Value],
    ) -> Result<Value, InterpError>;
    /// Marks the given memory as able to be freed. A memory manager need not do
    /// anything with this information.
    /// # Errors
    /// Can return an error if the pointer is invalid or already freed
    fn free(&mut self, key: &Pointer) -> Result<(), InterpError>;
    /// Writes the given value to the given pointer
    /// # Errors
    /// Returns an error if the pointer is invalid
    fn write(&mut self, key: &Pointer, val: Value) -> Result<(), InterpError>;
    /// Returns a reference to the value stored at the given pointer
    /// or an error if the pointer is invalid
    /// # Errors
    /// Returns an error if the pointer is invalid
    fn read(&self, key: &Pointer) -> Result<&Value, InterpError>;
    /// Testing function to check for memory leaks
    fn test(&mut self) -> MemStats;
}

const NUM_GENS: usize = 1;

/// The generational collector
pub struct Collector {
    /// Array of generations, from youngest to oldest
    gens: [Box<dyn Generation>; NUM_GENS],
}

/// An allocation is either a new allocation or an allocation caused by promoting
/// data from a younger generation
enum Allocation<'a> {
    New(usize),
    Move(Pointer, &'a [Value]),
}

/// The result of an allocation
enum AllocationResult {
    /// A brand new memory allocation
    New(Pointer),
    /// The first pointer's data has been moved to the second pointer
    Remap(Pointer, Pointer),
}

impl Collector {
    #[must_use]
    pub fn new(g0_size: usize, g1_size: usize, g2_size: usize) -> Self {
        Self {
            gens: [
                // Box::new(CopyingGen::new(g0_size, 0)),
                // Box::new(CopyingGen::new(g1_size, 1)),
                Box::new(ElderGen::new(g2_size, 0)),
            ],
        }
    }

    /// Allocates the given allocation, invoking garbage collection if necessary
    /// # Args
    /// * `gens` - the generations to allocate from, where index 0 is the first generation
    /// we should try to allocate from
    /// * `alloc` - the allocation to perform
    /// * `roots` - the roots of the program and the remembered sets from all generations
    /// * `did_collect` - whether or not we have already performed a collection
    /// for the generation at index 0
    fn alloc_or_collect(
        gens: &mut [Box<dyn Generation>],
        alloc: Allocation,
        roots: &[Pointer],
        did_collect: bool,
        masks: &[Vec<usize>],
    ) -> Result<Vec<AllocationResult>, InterpError> {
        let gens_left = gens.len() - 1;
        let cur_gen = &mut gens[0];
        if gens_left == 0 && !did_collect && cur_gen.should_collect() {
            // final generation, and we didn't previously collect, and we should collect
            return Self::collect_and_push_allocation(
                gens,
                alloc,
                roots,
                did_collect,
                masks,
            );
        }
        match alloc {
            Allocation::New(amount) => {
                if amount <= cur_gen.free_space() {
                    if let Ok(ptr) = cur_gen.alloc(amount) {
                        return Ok(vec![AllocationResult::New(ptr)]);
                    }
                }
            }
            Allocation::Move(ptr, data) => {
                if data.len() <= cur_gen.free_space() {
                    if let Ok(new_ptr) = cur_gen.memmove(data) {
                        return Ok(vec![AllocationResult::Remap(ptr, new_ptr)]);
                    }
                }
            }
        }
        // out of space:
        Self::collect_and_push_allocation(
            gens,
            alloc,
            roots,
            did_collect,
            masks,
        )
    }

    /// Performs a collection if we didn't already and then tries to allocate the given allocation
    /// # Args
    /// * `gens` - the generations to allocate from, where index 0 is the first generation
    /// we should try to allocate from
    /// * `alloc` - the allocation to perform
    /// * `roots` - the roots of the program and the remembered sets from all generations
    /// * `did_collect` - whether or not we have already performed a collection
    /// for the generation at index 0
    /// # Returns
    /// The result of the allocation
    fn collect_and_push_allocation(
        gens: &mut [Box<dyn Generation>],
        alloc: Allocation,
        roots: &[Pointer],
        did_collect: bool,
        masks: &[Vec<usize>],
    ) -> Result<Vec<AllocationResult>, InterpError> {
        let gen_len = gens.len();
        if gen_len > 1 {
            let gen_ptr = gens.as_mut_ptr();
            let ptr_start = unsafe { gen_ptr.add(1) };
            let ptr_end = gen_len - 1;
            let cur_gen = &mut gens[0];
            if !did_collect {
                // we didn't collect, so collect the current generation
                let promotions = cur_gen.collect(roots, &masks[0]);
                let mut res = vec![];
                assert!(promotions.is_empty() || gen_len > 1);
                // need to push promotions to the next generation
                for (old_ptr, data) in promotions {
                    // data belongs to cur_gen
                    if let Ok(nres) = Self::alloc_or_collect(
                        // safe bc we are using index 0, and starting slice from
                        // index 1, also gen_len > 1
                        unsafe {
                            slice::from_raw_parts_mut(ptr_start, ptr_end)
                        },
                        Allocation::Move(old_ptr, data),
                        roots,
                        did_collect,
                        &masks[1..],
                    ) {
                        res.extend(nres);
                    } else {
                        return Err(InterpError::CannotAllocSize(0));
                    }
                }
                // we promoted and collected, now try and allocate in this generation,
                // this time with did_collect = true
                return Self::alloc_or_collect(gens, alloc, roots, true, masks)
                    .map(|r| {
                        res.extend(r);
                        res
                    });
            }
            Self::alloc_or_collect(
                // safe bc gen_len > 1
                unsafe { slice::from_raw_parts_mut(ptr_start, ptr_end) },
                alloc,
                roots,
                did_collect,
                &masks[1..],
            )
        } else if !did_collect {
            // no more generations left, this is the final generation
            let r = gens[0].collect(roots, &masks[0]);
            // last generation should not promote
            assert!(r.is_empty());
            Self::alloc_or_collect(gens, alloc, roots, true, masks)
        } else {
            // final generation still out of space
            Err(InterpError::CannotAllocSize(0))
        }
    }
}

impl Default for Collector {
    fn default() -> Self {
        // JVM default heap total is 32 MB to 256 MB
        Self::new(2048, 4096, 8192)
    }
}

impl MemoryManager for Collector {
    #[allow(clippy::too_many_lines)]
    fn alloc(
        &mut self,
        amount: i64,
        roots: &mut [Value],
    ) -> Result<Value, InterpError> {
        if amount <= 0 {
            return Err(InterpError::CannotAllocSize(amount));
        }
        let amt_u: usize = amount
            .try_into()
            .map_err(|_| InterpError::CannotAllocSize(amount))?;
        let mut masks = vec![];
        for i in 0..self.gens.len() {
            let mut hs = HashSet::new();
            for g in &self.gens {
                hs.extend(g.remembered_masks(i as u8));
            }
            masks.push(hs.into_iter().collect::<Vec<_>>());
        }
        let total_roots = roots
            .iter()
            .filter_map(|v| {
                if let Value::Pointer(p) = v {
                    Some(*p)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let res = Self::alloc_or_collect(
            &mut self.gens,
            Allocation::New(amt_u),
            &total_roots,
            false,
            &masks,
        )
        .map_err(|_| InterpError::CannotAllocSize(amount))?;
        let mut ret_val = None;
        for r in res {
            match r {
                AllocationResult::New(p) => ret_val = Some(Value::Pointer(p)),
                AllocationResult::Remap(old_ptr, new_ptr) => {
                    for g in &mut self.gens {
                        g.update_ptr(&old_ptr, new_ptr);
                    }
                    for v in roots.iter_mut() {
                        if let Value::Pointer(p) = v {
                            if *p == old_ptr {
                                *p = new_ptr;
                            }
                        }
                    }
                }
            }
        }
        Ok(ret_val.unwrap())
    }

    fn free(&mut self, _: &Pointer) -> Result<(), InterpError> {
        Ok(())
    }

    fn write(&mut self, key: &Pointer, val: Value) -> Result<(), InterpError> {
        if (key.heap_id as usize) >= self.gens.len() {
            return Err(InterpError::InvalidMemoryAccess(key.base, key.offset));
        }
        self.gens[key.heap_id as usize]
            .write(key, val)
            .map_err(|_| InterpError::InvalidMemoryAccess(key.base, key.offset))
    }

    fn read(&self, key: &Pointer) -> Result<&Value, InterpError> {
        if (key.heap_id as usize) >= self.gens.len() {
            return Err(InterpError::InvalidMemoryAccess(key.base, key.offset));
        }
        self.gens[key.heap_id as usize]
            .read(key)
            .map_err(|_| InterpError::InvalidMemoryAccess(key.base, key.offset))
    }

    fn test(&mut self) -> MemStats {
        let mut stats = MemStats::default();
        for (idx, g) in &mut self.gens.iter_mut().enumerate() {
            // one last collection
            let (num_size, values_allocated) = g.len();
            let gs = GenStats {
                num_collections: g.num_collections(),
                num_size,
                num_remembered_set: g.num_remembered(idx.try_into().unwrap()),
                free_space: g.free_space(),
                values_allocated,
                num_promotions: g.num_promotions(),
            };
            stats.gen_stats.push(gs);
            g.collect(&[], &[]);
            stats.memory_leak |= !g.is_empty();
        }
        stats
    }
}

// Author of the following: Will Thompson

/// A Value in the interpreter
#[derive(Debug, Default, Clone, Copy)]
pub enum Value {
    /// A 64 bit integer
    Int(i64),
    /// A boolean
    Bool(bool),
    /// A 64 bit floating point number
    Float(f64),
    /// A unicode character
    Char(char),
    /// A pointer into the heap
    Pointer(Pointer),
    /// A value that has not been initialized
    #[default]
    Uninitialized,
}

/// A pointer into the heap
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct Pointer {
    /// The id of the heap that this pointer is pointing into
    pub heap_id: u8,
    /// The base number of the pointer
    pub base: usize,
    /// The offset from the base, for arrays
    pub offset: i64,
}

impl Pointer {
    #[must_use]
    pub const fn add(&self, offset: i64) -> Self {
        Self {
            base: self.base,
            offset: self.offset + offset,
            heap_id: self.heap_id,
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Int(i) => write!(f, "{i}"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Float(v) if v.is_infinite() && v.is_sign_positive() => {
                write!(f, "Infinity")
            }
            Self::Float(v) if v.is_infinite() && v.is_sign_negative() => {
                write!(f, "-Infinity")
            }
            Self::Float(v) => write!(f, "{v:.17}"),
            Self::Char(c) => write!(f, "{c}"),
            Self::Pointer(p) => write!(f, "{p:?}"),
            Self::Uninitialized => unreachable!(),
        }
    }
}

impl From<&bril_rs::Literal> for Value {
    fn from(l: &bril_rs::Literal) -> Self {
        match l {
            bril_rs::Literal::Int(i) => Self::Int(*i),
            bril_rs::Literal::Bool(b) => Self::Bool(*b),
            bril_rs::Literal::Float(f) => Self::Float(*f),
            bril_rs::Literal::Char(c) => Self::Char(*c),
        }
    }
}

impl From<bril_rs::Literal> for Value {
    fn from(l: bril_rs::Literal) -> Self {
        match l {
            bril_rs::Literal::Int(i) => Self::Int(i),
            bril_rs::Literal::Bool(b) => Self::Bool(b),
            bril_rs::Literal::Float(f) => Self::Float(f),
            bril_rs::Literal::Char(c) => Self::Char(c),
        }
    }
}

impl From<&Value> for i64 {
    fn from(value: &Value) -> Self {
        if let Value::Int(i) = value {
            *i
        } else {
            unreachable!()
        }
    }
}

impl From<&Value> for bool {
    fn from(value: &Value) -> Self {
        if let Value::Bool(b) = value {
            *b
        } else {
            unreachable!()
        }
    }
}

impl From<&Value> for f64 {
    fn from(value: &Value) -> Self {
        if let Value::Float(f) = value {
            *f
        } else {
            unreachable!()
        }
    }
}

impl From<&Value> for char {
    fn from(value: &Value) -> Self {
        if let Value::Char(c) = value {
            *c
        } else {
            unreachable!()
        }
    }
}

impl<'a> From<&'a Value> for &'a Pointer {
    fn from(value: &'a Value) -> Self {
        if let Value::Pointer(p) = value {
            p
        } else {
            eprintln!("Expected a pointer but got {value:?}");
            unreachable!()
        }
    }
}

impl From<&Self> for Value {
    fn from(value: &Self) -> Self {
        *value
    }
}
