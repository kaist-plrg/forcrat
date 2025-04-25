use rustc_index::{bit_set::BitRelations, Idx};

/// Bit set that can hold up to 8 elements.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BitSet8<T> {
    word: u8,
    _marker: std::marker::PhantomData<T>,
}

#[inline]
fn word_mask<T: Idx>(elem: T) -> u8 {
    1 << elem.index()
}

impl<T: Idx + std::fmt::Debug> std::fmt::Debug for BitSet8<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T: Idx> BitSet8<T> {
    #[inline]
    pub fn new_empty() -> Self {
        Self {
            word: 0,
            _marker: std::marker::PhantomData,
        }
    }

    #[inline]
    pub fn new<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::new_empty();
        for elem in iter {
            set.insert(elem);
        }
        set
    }

    #[inline]
    pub fn clear(&mut self) {
        self.word = 0;
    }

    #[inline]
    pub fn contains(&self, elem: T) -> bool {
        let mask = word_mask(elem);
        (self.word & mask) != 0
    }

    #[inline]
    pub fn insert(&mut self, elem: T) -> bool {
        let mask = word_mask(elem);
        let old_word = self.word;
        self.word |= mask;
        old_word != self.word
    }

    #[inline]
    pub fn remove(&mut self, elem: T) -> bool {
        let mask = word_mask(elem);
        let old_word = self.word;
        self.word &= !mask;
        old_word != self.word
    }

    #[inline]
    pub fn insert_all(&mut self, domain_size: u32) {
        self.word = 1u8.overflowing_shl(domain_size).0 - 1;
    }

    #[inline]
    pub fn count(&self) -> usize {
        self.word.count_ones() as usize
    }

    #[inline]
    pub fn superset(&self, other: &BitSet8<T>) -> bool {
        (self.word & other.word) == other.word
    }

    /// Is the set empty?
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.word == 0
    }

    /// Iterates over the indices of set bits in a sorted order.
    #[inline]
    pub fn iter(&self) -> SmallBitIter<'_, T> {
        SmallBitIter {
            word: self.word,
            _marker: std::marker::PhantomData,
        }
    }
}

pub struct SmallBitIter<'a, T> {
    word: u8,
    _marker: std::marker::PhantomData<&'a T>,
}

impl<T: Idx> Iterator for SmallBitIter<'_, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.word == 0 {
            return None;
        }
        let idx = self.word.trailing_zeros() as u8;
        self.word &= !(1 << idx);
        Some(T::new(idx as usize))
    }
}

impl<T: Idx> BitRelations<BitSet8<T>> for BitSet8<T> {
    fn union(&mut self, other: &BitSet8<T>) -> bool {
        bitwise(&mut self.word, other.word, |a, b| a | b)
    }

    fn subtract(&mut self, other: &BitSet8<T>) -> bool {
        bitwise(&mut self.word, other.word, |a, b| a & !b)
    }

    fn intersect(&mut self, other: &BitSet8<T>) -> bool {
        bitwise(&mut self.word, other.word, |a, b| a & b)
    }
}

#[inline]
fn bitwise<Op>(out_val: &mut u8, in_val: u8, op: Op) -> bool
where Op: Fn(u8, u8) -> u8 {
    let old_val = *out_val;
    let new_val = op(old_val, in_val);
    *out_val = new_val;
    old_val != new_val
}
