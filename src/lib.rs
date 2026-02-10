//! `NonMax` provides integer types that cannot be the maximum value of their underlying primitive type.
//!
//! # Memory Optimization
//!
//! The main benefit of `NonMax<T>` is that `Option<NonMax<T>>` has the same size as `T`.
//! This is achieved through Rust's "niche optimization", where the bit pattern of the
//! maximum value is used to represent `None`.
//!
//! | Primitive | `size_of::<T>()` | `size_of::<Option<T>>()` | `size_of::<Option<NonMax<T>>>()` |
//! |-----------|------------------|--------------------------|---------------------------------|
//! | `u32`     | 4                | 8                        | **4**                           |
//! | `i32`     | 4                | 8                        | **4**                           |
//! | `u8`      | 1                | 2                        | **1**                           |

#![no_std]

use core::convert::TryFrom;
use core::fmt::{self, Binary, Display, LowerHex, Octal, UpperHex};
use core::hash::Hash;
use core::marker::PhantomData;
use core::num::NonZero;
use core::ops::{
    Add, AddAssign, Div, DivAssign, Index, IndexMut, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign,
};

#[cfg(feature = "alloc")]
extern crate alloc;

/// Creates a `NonMax` value at compile-time.
///
/// This macro checks at compile-time that the provided value is not the maximum
/// value for its type. If the value is the maximum, the program will fail to compile.
///
/// # Examples
/// ```
/// # use arithmetic_nonmax::non_max;
/// let x = non_max!(123u8);
/// ```
///
/// ```compile_fail
/// # use arithmetic_nonmax::non_max;
/// let x = non_max!(255u8); // This fails to compile
/// ```
///
/// ```compile_fail
/// # use arithmetic_nonmax::non_max;
/// let x = non_max!(127i8); // i8::MAX fails
/// ```
///
/// ```compile_fail
/// # use arithmetic_nonmax::non_max;
/// let x = non_max!(u16::MAX); // Explicit MAX fails
/// ```
#[macro_export]
macro_rules! non_max {
    ($val:expr) => {{
        const _: () = const {
            if $val == <_ as $crate::NonMaxItem>::MAX {
                panic!("provided value is the maximum value for this type");
            }
        };
        unsafe { <_ as $crate::NonMaxItem>::create_nonmax_unchecked($val) }
    }};
}

/// Error type returned when a value is the maximum for its type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MaxValueError;

impl Display for MaxValueError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "provided value is the maximum value for this type")
    }
}

impl core::error::Error for MaxValueError {}

/// A wrapper type for an integer that cannot be its maximum value.
///
/// This type leverages Rust's `NonZero` optimization by mapping the maximum value to zero internally.
/// As a result, `Option<NonMax<T>>` has the same size as the underlying primitive type `T`.
///
/// # Examples
/// ```
/// # use arithmetic_nonmax::NonMaxU32;
/// # use core::mem::size_of;
/// assert_eq!(size_of::<NonMaxU32>(), 4);
/// assert_eq!(size_of::<Option<NonMaxU32>>(), 4);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NonMax<T: NonMaxItem>(T::NonZero);

impl<T: NonMaxItem + Copy> NonMax<T> {
    /// Creates a new `NonMax` if the given value is not the maximum value.
    ///
    /// # Examples
    /// ```
    /// # use arithmetic_nonmax::NonMaxU8;
    /// assert!(NonMaxU8::new(254).is_some());
    /// assert!(NonMaxU8::new(255).is_none());
    /// ```
    pub fn new(value: T) -> Option<Self> {
        Value::new(value).to_inner_repr().to_nonmax()
    }

    fn to_real_repr(self) -> Value<T, Real> {
        T::from_nonzero(self.0).to_real_repr()
    }

    /// Returns the underlying primitive value.
    ///
    /// # Examples
    /// ```
    /// # use arithmetic_nonmax::NonMaxU32;
    /// let x = NonMaxU32::new(123).unwrap();
    /// assert_eq!(x.get(), 123);
    /// ```
    pub fn get(&self) -> T {
        self.to_real_repr().value()
    }
}

impl<T: NonMaxItem + Copy + PartialEq> NonMax<T> {
    /// Returns `true` if this is the minimum value.
    pub fn is_min(&self) -> bool {
        self.get() == T::MIN_VALUE
    }

    /// Returns `true` if this is the maximum possible value for this type.
    pub fn is_max(&self) -> bool {
        self.get() == T::MAX_SAFE
    }

    /// Returns `true` if the value is zero.
    pub fn is_zero(&self) -> bool {
        self.get() == T::ZERO_VALUE
    }
}

impl<T: NonMaxItem + Copy> NonMax<T> {
    /// Checked integer addition. Computes `self + rhs`, returning `None` if overflow occurred
    /// or if the result is the maximum value.
    pub fn checked_add(self, rhs: Self) -> Option<Self> {
        self.get().checked_add(rhs.get()).and_then(Self::new)
    }

    /// Checked integer subtraction. Computes `self - rhs`, returning `None` if overflow occurred
    /// or if the result is the maximum value.
    pub fn checked_sub(self, rhs: Self) -> Option<Self> {
        self.get().checked_sub(rhs.get()).and_then(Self::new)
    }

    /// Checked integer multiplication. Computes `self * rhs`, returning `None` if overflow occurred
    /// or if the result is the maximum value.
    pub fn checked_mul(self, rhs: Self) -> Option<Self> {
        self.get().checked_mul(rhs.get()).and_then(Self::new)
    }

    /// Checked integer division. Computes `self / rhs`, returning `None` if the divisor is zero
    /// or if the result is the maximum value.
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        self.get().checked_div(rhs.get()).and_then(Self::new)
    }

    /// Checked integer remainder. Computes `self % rhs`, returning `None` if the divisor is zero
    /// or if the result is the maximum value.
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        self.get().checked_rem(rhs.get()).and_then(Self::new)
    }

    /// Checked addition with a primitive value.
    ///
    /// # Examples
    /// ```
    /// # use arithmetic_nonmax::NonMaxU8;
    /// let x = NonMaxU8::new(100).unwrap();
    /// assert_eq!(x.checked_add_val(50).unwrap().get(), 150);
    /// assert!(x.checked_add_val(155).is_none()); // 255 is MAX
    /// ```
    pub fn checked_add_val(self, rhs: T) -> Option<Self> {
        self.get().checked_add(rhs).and_then(Self::new)
    }

    /// Checked subtraction with a primitive value.
    pub fn checked_sub_val(self, rhs: T) -> Option<Self> {
        self.get().checked_sub(rhs).and_then(Self::new)
    }

    /// Checked multiplication with a primitive value.
    pub fn checked_mul_val(self, rhs: T) -> Option<Self> {
        self.get().checked_mul(rhs).and_then(Self::new)
    }

    /// Checked division with a primitive value.
    pub fn checked_div_val(self, rhs: T) -> Option<Self> {
        self.get().checked_div(rhs).and_then(Self::new)
    }

    /// Checked remainder with a primitive value.
    pub fn checked_rem_val(self, rhs: T) -> Option<Self> {
        self.get().checked_rem(rhs).and_then(Self::new)
    }
}

impl<T: NonMaxItem + Copy + Add<Output = T>> Add for NonMax<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        self.checked_add(rhs)
            .expect("attempt to add with overflow or to maximum value")
    }
}

impl<T: NonMaxItem + Copy + Add<Output = T>> Add<T> for NonMax<T> {
    type Output = Self;
    fn add(self, rhs: T) -> Self::Output {
        self.checked_add_val(rhs)
            .expect("attempt to add with overflow or to maximum value")
    }
}

impl<T: NonMaxItem + Copy + Add<Output = T>> AddAssign for NonMax<T> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<T: NonMaxItem + Copy + Add<Output = T>> AddAssign<T> for NonMax<T> {
    fn add_assign(&mut self, rhs: T) {
        *self = *self + rhs;
    }
}

impl<T: NonMaxItem + Copy + Sub<Output = T>> Sub for NonMax<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("attempt to subtract with overflow or to maximum value")
    }
}

impl<T: NonMaxItem + Copy + Sub<Output = T>> Sub<T> for NonMax<T> {
    type Output = Self;
    fn sub(self, rhs: T) -> Self::Output {
        self.checked_sub_val(rhs)
            .expect("attempt to subtract with overflow or to maximum value")
    }
}

impl<T: NonMaxItem + Copy + Sub<Output = T>> SubAssign for NonMax<T> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<T: NonMaxItem + Copy + Sub<Output = T>> SubAssign<T> for NonMax<T> {
    fn sub_assign(&mut self, rhs: T) {
        *self = *self - rhs;
    }
}

impl<T: NonMaxItem + Copy + Mul<Output = T>> Mul for NonMax<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        self.checked_mul(rhs)
            .expect("attempt to multiply with overflow or to maximum value")
    }
}

impl<T: NonMaxItem + Copy + Mul<Output = T>> Mul<T> for NonMax<T> {
    type Output = Self;
    fn mul(self, rhs: T) -> Self::Output {
        self.checked_mul_val(rhs)
            .expect("attempt to multiply with overflow or to maximum value")
    }
}

impl<T: NonMaxItem + Copy + Mul<Output = T>> MulAssign for NonMax<T> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<T: NonMaxItem + Copy + Mul<Output = T>> MulAssign<T> for NonMax<T> {
    fn mul_assign(&mut self, rhs: T) {
        *self = *self * rhs;
    }
}

impl<T: NonMaxItem + Copy + Div<Output = T>> Div for NonMax<T> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        self.checked_div(rhs)
            .expect("attempt to divide by zero or to maximum value")
    }
}

impl<T: NonMaxItem + Copy + Div<T, Output = T>> Div<T> for NonMax<T> {
    type Output = Self;
    fn div(self, rhs: T) -> Self::Output {
        self.checked_div_val(rhs)
            .expect("attempt to divide by zero or to maximum value")
    }
}

impl<T: NonMaxItem + Copy + Div<Output = T>> DivAssign for NonMax<T> {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl<T: NonMaxItem + Copy + Div<T, Output = T>> DivAssign<T> for NonMax<T> {
    fn div_assign(&mut self, rhs: T) {
        *self = *self / rhs;
    }
}

impl<T: NonMaxItem + Copy + Rem<Output = T>> Rem for NonMax<T> {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self::Output {
        self.checked_rem(rhs)
            .expect("attempt to calculate remainder by zero or to maximum value")
    }
}

impl<T: NonMaxItem + Copy + Rem<T, Output = T>> Rem<T> for NonMax<T> {
    type Output = Self;
    fn rem(self, rhs: T) -> Self::Output {
        self.checked_rem_val(rhs)
            .expect("attempt to calculate remainder by zero or to maximum value")
    }
}

impl<T: NonMaxItem + Copy + Rem<Output = T>> RemAssign for NonMax<T> {
    fn rem_assign(&mut self, rhs: Self) {
        *self = *self % rhs;
    }
}

impl<T: NonMaxItem + Copy + Rem<T, Output = T>> RemAssign<T> for NonMax<T> {
    fn rem_assign(&mut self, rhs: T) {
        *self = *self % rhs;
    }
}

impl<T: NonMaxItem + Copy + PartialOrd> PartialOrd for NonMax<T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.to_real_repr().partial_cmp(&other.to_real_repr())
    }
}

impl<T: NonMaxItem + Copy + Ord> Ord for NonMax<T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.to_real_repr().cmp(&other.to_real_repr())
    }
}

impl<T: NonMaxItem + Copy + Display> Display for NonMax<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.get(), f)
    }
}

impl<T: NonMaxItem + Copy + Binary> Binary for NonMax<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Binary::fmt(&self.get(), f)
    }
}

impl<T: NonMaxItem + Copy + Octal> Octal for NonMax<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Octal::fmt(&self.get(), f)
    }
}

impl<T: NonMaxItem + Copy + LowerHex> LowerHex for NonMax<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        LowerHex::fmt(&self.get(), f)
    }
}

impl<T: NonMaxItem + Copy + UpperHex> UpperHex for NonMax<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        UpperHex::fmt(&self.get(), f)
    }
}

impl<T: NonMaxItem + Copy> Default for NonMax<T> {
    fn default() -> Self {
        Self::new(T::ZERO_VALUE).unwrap()
    }
}

#[doc(hidden)]
pub trait NonMaxItem: Sized {
    type NonZero: Copy + PartialEq + Eq + PartialOrd + Ord + Hash;
    const MIN_VALUE: Self;
    const MAX: Self;
    const MAX_SAFE: Self;
    const ZERO_VALUE: Self;
    fn transform(self) -> Self;
    fn to_nonzero(value: Value<Self, Inner>) -> Option<Self::NonZero>;
    unsafe fn to_nonzero_unchecked(value: Value<Self, Inner>) -> Self::NonZero;
    fn from_nonzero(value: Self::NonZero) -> Value<Self, Inner>;

    fn checked_add(self, rhs: Self) -> Option<Self>;
    fn checked_sub(self, rhs: Self) -> Option<Self>;
    fn checked_mul(self, rhs: Self) -> Option<Self>;
    fn checked_div(self, rhs: Self) -> Option<Self>;
    fn checked_rem(self, rhs: Self) -> Option<Self>;

    /// Creates a `NonMax` from this value without checking.
    ///
    /// # Safety
    /// The value must not be the maximum value.
    unsafe fn create_nonmax_unchecked(self) -> NonMax<Self>;
}

macro_rules! impl_non_max_item {
    ($($t:ty, $name:ident, $doc:expr),*) => {
        $(
            impl NonMaxItem for $t {
                type NonZero = NonZero<$t>;
                const MIN_VALUE: Self = <$t>::MIN;
                const MAX: Self = <$t>::MAX;
                const MAX_SAFE: Self = <$t>::MAX - 1;
                const ZERO_VALUE: Self = 0;
                fn transform(self) -> Self {
                    self ^ <$t>::MAX
                }
                fn to_nonzero(value: Value<Self, Inner>) -> Option<Self::NonZero> {
                    Self::NonZero::new(value.value())
                }
                unsafe fn to_nonzero_unchecked(value: Value<Self, Inner>) -> Self::NonZero {
                    unsafe { Self::NonZero::new_unchecked(value.value()) }
                }
                fn from_nonzero(value: Self::NonZero) -> Value<Self, Inner> {
                    Value::new(value.get())
                }

                fn checked_add(self, rhs: Self) -> Option<Self> { self.checked_add(rhs) }
                fn checked_sub(self, rhs: Self) -> Option<Self> { self.checked_sub(rhs) }
                fn checked_mul(self, rhs: Self) -> Option<Self> { self.checked_mul(rhs) }
                fn checked_div(self, rhs: Self) -> Option<Self> { self.checked_div(rhs) }
                fn checked_rem(self, rhs: Self) -> Option<Self> { self.checked_rem(rhs) }

                unsafe fn create_nonmax_unchecked(self) -> NonMax<Self> {
                    unsafe { NonMax::<$t>::new_unchecked(self) }
                }
            }

            impl From<NonMax<$t>> for $t {
                fn from(value: NonMax<$t>) -> Self {
                    value.get()
                }
            }

            impl TryFrom<$t> for NonMax<$t> {
                type Error = MaxValueError;

                fn try_from(value: $t) -> Result<Self, Self::Error> {
                    Self::new(value).ok_or(MaxValueError)
                }
            }

            #[doc = $doc]
            pub type $name = NonMax<$t>;

            impl $name {
                /// The minimum value for this type.
                pub const MIN: Self = unsafe { Self(NonZero::new_unchecked(<$t>::MIN ^ <$t>::MAX)) };
                /// The maximum value for this type.
                pub const MAX: Self = unsafe { Self(NonZero::new_unchecked((<$t>::MAX - 1) ^ <$t>::MAX)) };
                /// The zero value for this type.
                pub const ZERO: Self = unsafe { Self(NonZero::new_unchecked(0 ^ <$t>::MAX)) };

                /// Creates a new `NonMax` without checking the value.
                ///
                /// # Safety
                /// The value must not be the maximum value of the underlying type.
                pub const unsafe fn new_unchecked(value: $t) -> Self {
                    Self(unsafe { NonZero::new_unchecked(value ^ <$t>::MAX) })
                }
            }
        )*
    };
}

impl_non_max_item!(
    u8,
    NonMaxU8,
    "An unsigned 8-bit integer that cannot be `u8::MAX`.",
    u16,
    NonMaxU16,
    "An unsigned 16-bit integer that cannot be `u16::MAX`.",
    u32,
    NonMaxU32,
    "An unsigned 32-bit integer that cannot be `u32::MAX`.",
    u64,
    NonMaxU64,
    "An unsigned 64-bit integer that cannot be `u64::MAX`.",
    u128,
    NonMaxU128,
    "An unsigned 128-bit integer that cannot be `u128::MAX`.",
    usize,
    NonMaxUsize,
    "An unsigned pointer-sized integer that cannot be `usize::MAX`.",
    i8,
    NonMaxI8,
    "A signed 8-bit integer that cannot be `i8::MAX`.",
    i16,
    NonMaxI16,
    "A signed 16-bit integer that cannot be `i16::MAX`.",
    i32,
    NonMaxI32,
    "A signed 32-bit integer that cannot be `i32::MAX`.",
    i64,
    NonMaxI64,
    "A signed 64-bit integer that cannot be `i64::MAX`.",
    i128,
    NonMaxI128,
    "A signed 128-bit integer that cannot be `i128::MAX`.",
    isize,
    NonMaxIsize,
    "A signed pointer-sized integer that cannot be `isize::MAX`."
);

#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Real;
#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Inner;

#[doc(hidden)]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct Value<T, M> {
    value: T,
    _marker: PhantomData<M>,
}

impl<T: NonMaxItem + Copy, M> Value<T, M> {
    fn new(value: T) -> Self {
        Self {
            value,
            _marker: PhantomData,
        }
    }

    fn value(&self) -> T {
        self.value
    }
}

impl<T: NonMaxItem + Copy> Value<T, Real> {
    fn to_inner_repr(self) -> Value<T, Inner> {
        Value::new(T::transform(self.value))
    }
}

impl<T: NonMaxItem + Copy + Add<Output = T>> Add for Value<T, Real> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.value() + rhs.value())
    }
}

impl<T: NonMaxItem + Copy + Sub<Output = T>> Sub for Value<T, Real> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.value() - rhs.value())
    }
}

impl<T: NonMaxItem + Copy + Mul<Output = T>> Mul for Value<T, Real> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.value() * rhs.value())
    }
}

impl<T: NonMaxItem + Copy + Div<Output = T>> Div for Value<T, Real> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        Self::new(self.value() / rhs.value())
    }
}

impl<T: NonMaxItem + Copy + Rem<Output = T>> Rem for Value<T, Real> {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self::Output {
        Self::new(self.value() % rhs.value())
    }
}

impl<T: NonMaxItem + Copy> Value<T, Inner> {
    fn to_real_repr(self) -> Value<T, Real> {
        Value::new(T::transform(self.value))
    }

    fn to_nonmax(self) -> Option<NonMax<T>> {
        T::to_nonzero(self).map(NonMax)
    }
}

impl<T: NonMaxItem + Copy + PartialOrd> PartialOrd for Value<T, Real> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        self.value().partial_cmp(&other.value())
    }
}

impl<T: NonMaxItem + Copy + Ord> Ord for Value<T, Real> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.value().cmp(&other.value())
    }
}

impl<T: NonMaxItem + Copy + Display> Display for Value<T, Real> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value())
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use core::mem::size_of;
    use std::collections::HashSet;

    #[test]
    fn test_hash() {
        let mut set = HashSet::new();
        set.insert(NonMaxU32::new(1).unwrap());
        set.insert(NonMaxU32::new(2).unwrap());
        set.insert(NonMaxU32::new(1).unwrap());

        assert_eq!(set.len(), 2);
        assert!(set.contains(&NonMaxU32::new(1).unwrap()));
    }

    #[test]
    fn test_sizes() {
        assert_eq!(size_of::<NonMaxU32>(), 4);
        assert_eq!(size_of::<Option<NonMaxU32>>(), 4);

        assert_eq!(size_of::<NonMaxI32>(), 4);
        assert_eq!(size_of::<Option<NonMaxI32>>(), 4);

        assert_eq!(size_of::<NonMaxU8>(), 1);
        assert_eq!(size_of::<Option<NonMaxU8>>(), 1);
    }

    #[test]
    fn test_conversions() {
        let x = NonMaxU8::try_from(100).unwrap();
        assert_eq!(u8::from(x), 100);

        let max_val = u8::MAX;
        assert!(NonMaxU8::try_from(max_val).is_err());
    }

    #[test]
    fn test_arithmetic_with_val() {
        let x = NonMaxU8::new(100).unwrap();
        let y = x + 50;
        assert_eq!(u8::from(y), 150);

        let mut z = NonMaxU8::new(10).unwrap();
        z += 20;
        assert_eq!(u8::from(z), 30);

        let a = NonMaxU8::new(10).unwrap();
        let b = a * 5;
        assert_eq!(u8::from(b), 50);

        let c = NonMaxU8::new(100).unwrap();
        let d = c / 3;
        assert_eq!(u8::from(d), 33);
    }

    #[test]
    fn test_add_overflow() {
        let x = NonMaxU8::try_from(250).unwrap();
        // Now it should return None instead of panicking
        assert!(x.checked_add_val(10).is_none());
    }

    #[test]
    fn test_add_to_max() {
        let x = NonMaxU8::try_from(250).unwrap();
        // Result is 255 (MAX), so it should return None
        assert!(x.checked_add_val(5).is_none());
    }

    #[test]
    fn test_signed_integer() {
        // i8: -128 to 127. MAX is 127.
        let x = NonMaxI8::try_from(100).unwrap();
        let y = x + 20;
        assert_eq!(i8::from(y), 120);

        let z = NonMaxI8::try_from(-50).unwrap();
        let w = z + 10;
        assert_eq!(i8::from(w), -40);

        // MIN (-128) is allowed
        let min_val = NonMaxI8::try_from(i8::MIN).unwrap();
        assert_eq!(i8::from(min_val), -128);
    }

    #[test]
    fn test_signed_overflow() {
        let x = NonMaxI8::try_from(120).unwrap();
        // Overflow detected
        assert!(x.checked_add_val(10).is_none());
    }

    #[test]
    fn test_signed_to_max() {
        let x = NonMaxI8::try_from(120).unwrap();
        // Result is 127 (MAX), so None
        assert!(x.checked_add_val(7).is_none());
    }

    #[test]
    fn test_formatting() {
        let x = NonMaxU8::new(254).unwrap();
        assert_eq!(std::format!("{}", x), "254");
        assert_eq!(std::format!("{:b}", x), "11111110");
        assert_eq!(std::format!("{:o}", x), "376");
        assert_eq!(std::format!("{:x}", x), "fe");
        assert_eq!(std::format!("{:X}", x), "FE");
    }

    #[test]
    fn test_min_max_constants() {
        assert_eq!(NonMaxU8::MIN.get(), 0);
        assert_eq!(NonMaxU8::MAX.get(), 254);
        assert!(NonMaxU8::MIN.is_min());
        assert!(NonMaxU8::MAX.is_max());
        assert!(!NonMaxU8::MIN.is_max());
        assert!(!NonMaxU8::MAX.is_min());

        assert_eq!(NonMaxI8::MIN.get(), -128);
        assert_eq!(NonMaxI8::MAX.get(), 126);
    }

    #[test]
    fn test_zero_constant() {
        assert_eq!(NonMaxU8::ZERO.get(), 0);
        assert!(NonMaxU8::ZERO.is_zero());
        assert_eq!(NonMaxI32::ZERO.get(), 0);
        assert!(NonMaxI32::ZERO.is_zero());
    }

    #[test]
    fn test_non_max_macro() {
        let x = non_max!(123u8);
        assert_eq!(x.get(), 123);

        let y = non_max!(456u32);
        assert_eq!(y.get(), 456);

        let z = non_max!(-10i32);
        assert_eq!(z.get(), -10);
    }

    #[test]
    fn test_indexing() {
        let v = [1, 2, 3];
        let idx = NonMaxUsize::new(1).unwrap();
        assert_eq!(v[idx], 2);

        let mut v_mut = [1, 2, 3];
        v_mut[idx] = 10;
        assert_eq!(v_mut[1], 10);

        #[cfg(feature = "alloc")]
        {
            let v_vec = std::vec![1, 2, 3];
            assert_eq!(v_vec[idx], 2);

            let mut v_vec_mut = std::vec![1, 2, 3];
            v_vec_mut[idx] = 20;
            assert_eq!(v_vec_mut[1], 20);
        }
    }
}

impl<T> Index<NonMaxUsize> for [T] {
    type Output = T;
    #[inline]
    fn index(&self, index: NonMaxUsize) -> &Self::Output {
        &self[index.get()]
    }
}

impl<T> IndexMut<NonMaxUsize> for [T] {
    #[inline]
    fn index_mut(&mut self, index: NonMaxUsize) -> &mut Self::Output {
        &mut self[index.get()]
    }
}

#[cfg(feature = "alloc")]
impl<T> Index<NonMaxUsize> for alloc::vec::Vec<T> {
    type Output = T;
    #[inline]
    fn index(&self, index: NonMaxUsize) -> &Self::Output {
        &self[index.get()]
    }
}

#[cfg(feature = "alloc")]
impl<T> IndexMut<NonMaxUsize> for alloc::vec::Vec<T> {
    #[inline]
    fn index_mut(&mut self, index: NonMaxUsize) -> &mut Self::Output {
        &mut self[index.get()]
    }
}
