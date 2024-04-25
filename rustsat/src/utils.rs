//! # Library-Internal Utilities

/// Computes the number of digits needed to represent a number in a given base
#[cfg_attr(feature = "internals", visibility::make(pub))]
pub(crate) fn digits(mut number: usize, mut basis: u8) -> u32 {
    debug_assert_ne!(basis, 0);
    if number == 0 {
        return 1;
    }
    if basis == 1 {
        return std::cmp::max(number as u32, 1);
    }
    let mut digits = 0;
    if (basis & (basis - 1)) == 0 {
        // Base is a power of 2. Optimized version using shift operations.
        let mut pow: u8 = 0;
        basis >>= 1;
        while basis > 0 {
            pow += 1;
            basis >>= 1;
        }
        while number > 0 {
            digits += 1;
            number >>= pow;
        }
    } else {
        while number > 0 {
            digits += 1;
            number /= basis as usize;
        }
    }
    digits
}

/// A wrapper around an iterator to only yield a limited number of elements and then stop
///
/// As opposed to [`std::iter::Take`] this does not take ownership of the original iterator
pub struct LimitedIter<'iter, I> {
    iter: &'iter mut I,
    remaining: usize,
}

impl<'iter, I> LimitedIter<'iter, I> {
    /// Creates a new iterator that yields at most `remaining` elements
    pub fn new(iter: &'iter mut I, remaining: usize) -> Self {
        Self { iter, remaining }
    }
}

impl<I> Iterator for LimitedIter<'_, I>
where
    I: Iterator,
{
    type Item = <I as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        self.iter.next()
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn digits_pow_2() {
        assert_eq!(super::digits(0b11111101, 2), 8);
        assert_eq!(super::digits(0b11111101, 4), 4);
        assert_eq!(super::digits(0b11111101, 8), 3);
        assert_eq!(super::digits(0b11111101, 16), 2);
    }

    #[test]
    fn digits_base_10() {
        assert_eq!(super::digits(3158, 10), 4);
        assert_eq!(super::digits(123, 10), 3);
    }
}
