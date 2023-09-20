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
