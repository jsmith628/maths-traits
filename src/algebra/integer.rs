//!
//!Traits for integers and natural numbers
//!

use core::convert::{TryFrom};
use core::ops::{Rem, RemAssign};
use core::iter::Iterator;

use num_traits::{ToPrimitive, FromPrimitive};

use crate::analysis::ordered::*;
use crate::algebra::*;

///Aliases conversion traits to and from the primitive integer types
pub trait CastPrimInt =
    TryFrom<i8>   + TryFrom<u8>   +
    TryFrom<i16>  + TryFrom<u16>  +
    TryFrom<i32>  + TryFrom<u32>  +
    TryFrom<i64>  + TryFrom<u64>  +
    TryFrom<i128> + TryFrom<u128> ;

///
///A subset of the Integers that has all of the major integer operations
///
///This includes:
/// * Basic ring operations
/// * Euclidean division any everything implied by having it
/// * Algebraic ordering properties and archimedian division
/// * Additional operations conventionally implemented on integer types
///
///In practice, this means that a type implementing this trait must be either a
///representation of the natural numbers or the integers as a whole.
///
///Furthermore, this trait contains associated types referring to an unsigned and signed type of
///similar precision to make it easier to manage the broader system of types used in integer algorithms
///
pub trait IntegerSubset: Ord + Eq + Clone + CastPrimInt + ToPrimitive + FromPrimitive
                        + EuclideanSemidomain
                        + Primality
                        + ArchSemiring + ArchimedeanDiv + Sign
                        + Sub<Self, Output=Self> + Div<Self, Output=Self> + Rem<Self, Output=Self>
                        + SubAssign<Self> + DivAssign<Self> + RemAssign<Self>
{

    ///
    ///This type's corresponding signed Integer representation
    ///
    ///Implementors should guarantee that this type has the same theoretical bit precision as
    ///the Unsigned type
    ///
    type Signed: Integer + IntegerSubset<Signed=Self::Signed, Unsigned=Self::Unsigned>;

    ///
    ///This type's corresponding unsigned Integer representation
    ///
    ///Implementors should guarantee that this type has the same theoretical bit precision as
    ///the Signed type
    ///
    type Unsigned: Natural + IntegerSubset<Signed=Self::Signed, Unsigned=Self::Unsigned>;

    ///
    ///Converts `self` to a signed integer representation
    ///
    ///Note that this has the same guarantees as the primitive `as` operation
    ///and can thus panic on overflow
    ///
    fn as_signed(self) -> Self::Signed;

    ///
    ///Converts `self` into an unsigned integer representation
    ///
    ///Note that this has the same guarantees as the primitive `as` operation
    ///and can thus panic on underflow
    ///
    fn as_unsigned(self) -> Self::Unsigned;

    ///
    ///Takes the absolute value and converts into an unsigned integer representation
    ///
    ///Implementors should guarantee that this conversion never fails or panics since
    ///the unsigned and signed types are assumed to be of the same theoretical bit precision
    ///
    #[inline] fn abs_unsigned(self) -> Self::Unsigned { self.abs().as_unsigned() }

    ///A shorthand for `1+1`
    #[inline] fn two() -> Self { Self::one()+Self::one() }

    ///
    ///Multiplies by two
    ///
    ///This is meant both as convenience and to expose the `<<` operator for representations that
    ///support it. As such, this method has the _potential_ to be faster than normal multiplication
    ///
    #[inline] fn mul_two(self) -> Self { self * Self::two() }

    ///
    ///Divides by two
    ///
    ///This is meant both as convenience and to expose the `>>` operator for representations that
    ///support it. As such, this method has the _potential_ to be faster than normal division
    ///
    #[inline] fn div_two(self) -> Self { self / Self::two() }

    ///Determines if a number is divisible by two
    #[inline] fn even(&self) -> bool {Self::two().divides(self.clone())}

    ///Determines if a number is not divisible by two
    #[inline] fn odd(&self) -> bool {!self.even()}
}

///An [IntegerSubset] that specifically represents an unsigned integer
pub trait Natural: IntegerSubset<Unsigned=Self> {}

///An [IntegerSubset] that specifically represents a signed integer
pub trait Integer: IntegerSubset<Signed=Self> + ArchUnitalRing {}

///
///An iterator over the factors of an integer using the
///[trial division](https://en.wikipedia.org/wiki/Trial_division) algorithm
///
///Given the nature of the algorithm, factors are guaranteed to be returned ascending order,
///with a factor of `-1` given at the beginning if the number is negative, a single `0` given
///if zero, and no factors returned if the original integer is `1`.
///
///```
/// # use maths_traits::algebra::*;
///let mut factors = TrialDivision::factors_of(-15);
///
///assert_eq!(factors.next(), Some(-1));
///assert_eq!(factors.next(), Some(3));
///assert_eq!(factors.next(), Some(5));
///assert_eq!(factors.next(), None);
///```
///
pub struct TrialDivision<Z:IntegerSubset> {
    x: Z,
    f: Z,
    mode: bool
}

impl<Z:IntegerSubset> TrialDivision<Z> {
    ///constructs an iterator over the factors of the argument
    pub fn factors_of(x:Z) -> Self { TrialDivision {x:x,f:Z::two(),mode:false} }

    ///the product of the remaining factors to be iterated over
    pub fn remaining(&self) -> Z { self.x.clone() }

    ///
    ///the current factor being tested in the algorithm
    ///
    ///Note that there is no guarantee that this actually _is_ a factor
    ///**or** that this function's result will change after an iterator step
    ///
    pub fn current_factor(&self) -> Z { self.f.clone() }
}

impl<Z:IntegerSubset> Iterator for TrialDivision<Z> {
    type Item = Z;

    fn next(&mut self) -> Option<Z> {

        if self.x.is_one() {return None;}
        let three = Z::embed_nat(3u8);

        if self.f >= three {

            if self.f.clone().pow_n(2u8) > self.x { //if x is prime
                self.f = self.x.clone();
                self.x = Z::one();
                Some(self.f.clone())
            } else {
                //divide and check the remainder
                let (q, r) = self.x.clone().div_alg(self.f.clone());

                if r.is_zero() {//if the remainder is zero, we have a factor
                    self.x = q;
                    Some(self.f.clone())
                } else {//else do the next loop
                    //get the next factor
                    if !self.mode {
                        self.mode = if self.f == three {false} else {true};
                        self.f += Z::two();
                    } else {
                        self.mode = false;
                        self.f += Z::two() + Z::two();
                    }
                    self.next()
                }
            }

        } else {
            if self.x.is_zero() { //x is zero
                self.x = Z::one();
                Some(Z::zero())
            } else if self.x.negative() { //emit a factor of -1
                self.x = self.x.clone().abs();
                Some(Z::zero() - Z::one())
            } else { //if f is 2 we want to do bit-shifts and stuff for 2
                if self.x.even() {
                    self.x = self.x.clone().div_two();
                    Some(Z::two())
                } else {
                    self.f = three;
                    self.mode = false;
                    self.next()
                }
            }
        }

    }

}

macro_rules! impl_int_subset {

    (@unit $self:ident @unsigned) => {*$self==1};
    (@unit $self:ident @signed) => {*$self==1 || *$self == -1 };

    (@factors $factors:ident $self:ident @unsigned) => {};
    (@factors $factors:ident $self:ident @signed) => {
        if *$self < 0 {
            $factors.push(-1);
        }
    };

    (@neg $self:ident @unsigned) => {false};
    (@neg $self:ident @signed) => {*$self < 0 };
    (@abs $self:ident $name:ident @unsigned) => {$self};
    (@abs $self:ident $name:ident @signed) => {Sign::abs($self) };

    //base case for loop
    ($name:ident:$signed:ident:$unsigned:ident $($tt:tt)*) => {

        impl Divisibility for $name {
            #[inline] fn unit(&self) -> bool{ impl_int_subset!(@unit self $($tt)*) }
            #[inline] fn inverse(self) -> Option<Self>
                {if self.unit() { Option::Some(self) }else {Option::None} }
            #[inline] fn divides(self, rhs: Self) -> bool { (rhs % self) == 0}
            #[inline] fn divide(self, rhs: Self) -> Option<Self> {
                let (q, r) = self.div_alg(rhs);
                if r==0 {Some(q)} else {None}
            }
        }

        impl NoZeroDivisors for $name {}

        impl GCD for $name {
            #[inline] fn lcm(self, rhs: Self) -> Self { (self*rhs) / self.gcd(rhs) }
            #[inline] fn gcd(self, rhs: Self) -> Self{ euclidean(self, rhs) }
        }

        impl UniquelyFactorizable for $name {}

        impl Factorizable for $name {
            type Factors = TrialDivision<Self>;
            #[inline] fn factors(self) -> TrialDivision<Self> {TrialDivision::factors_of(self)}
        }

        impl EuclideanDiv for $name {
            type Naturals = $unsigned;
            #[inline] fn euclid_norm(&self) -> $unsigned {self.abs_unsigned()}

            ///Euclidean division implemented using the `/` operator
            #[inline] fn div_euc(self, rhs: Self) -> Self {self / rhs}

            ///Euclidean remainder implemented using the `%` operator
            #[inline] fn rem_euc(self, rhs: Self) -> Self {self % rhs}

            ///
            ///Euclidean division implemented using the `/` and `%` operators
            ///
            ///Note that this does mean that the remainder may be negative and this method
            ///only guarantees that it satisfies the basic [Eucldidean division](EuclideanDiv::div_alg)
            ///axioms
            #[inline] fn div_alg(self, rhs: Self) -> (Self, Self) {(self / rhs, self % rhs)}
        }

        impl IntegerSubset for $name {
            type Signed = $signed;
            type Unsigned = $unsigned;
            #[inline] fn as_signed(self) -> $signed { self as $signed }
            #[inline] fn as_unsigned(self) -> $unsigned { self as $unsigned }

            #[inline] fn two() -> Self { 2 }
            #[inline] fn mul_two(self) -> Self { self << 1 }
            #[inline] fn div_two(self) -> Self { self >> 1 }
            #[inline] fn even(&self) -> bool { (*self & 1) == 0 }
            #[inline] fn odd(&self) -> bool { (*self & 1) == 1 }
        }

    }
}

macro_rules! impl_int {
    ($($s:ident:$u:ident)*) => {
        $(
            impl Bezout for $s {
                #[inline]
                fn bezout_coefficients(self, rhs: Self) -> (Self, Self) {
                    let (x, y, _g) = extended_euclidean(self, rhs);
                    (x, y)
                }
                #[inline] fn bezout_with_gcd(self, rhs: Self) -> (Self, Self, Self) { extended_euclidean(self, rhs) }
            }

            impl_int_subset!($u:$s:$u @unsigned);
            impl_int_subset!($s:$s:$u @signed);
            impl Natural for $u {}
            impl Integer for $s {}
        )*
    };
}

macro_rules! impl_primality {
    ($($t:ident:$hp:ident)*) => {$(
        impl Primality for $t {
            #[inline] fn irreducible(&self) -> bool { self.prime() }
            #[inline] fn prime(&self) -> bool { miller_rabin(*self as $hp) }
        }
    )*}
}

impl_int!(i8:u8 i16:u16 i32:u32 i64:u64 i128:u128 isize:usize);
impl_primality!(i8:u16 i16:u32 i32:u64 i64:u128 i128:u128 isize:u128);
impl_primality!(u8:u16 u16:u32 u32:u64 u64:u128 u128:u128 usize:u128);

#[cfg(feature = "bigint")]
mod impl_bigint {
    use super::*;
    use num_integer::Integer as NumInteger;
    use num_bigint::{BigUint, BigInt};

    //
    //while we *can* just use impl_int!, some of the methods we need to impl already have
    //methods in num_integer::Integer
    //

    macro_rules! impl_bigint {
        ($name:ty:$signed:ty:$unsigned:ty) => {
            impl Divisibility for $name {
                #[inline] fn unit(&self) -> bool{
                    self.is_one() || Self::try_from(-1i32).map(|m| &m==self).unwrap_or(false)
                }

                #[inline] fn inverse(self) -> Option<Self>
                    {if self.unit() { Option::Some(self) } else {Option::None} }
                #[inline] fn divides(self, rhs: Self) -> bool { NumInteger::is_multiple_of(&rhs, &self) }
                #[inline] fn divide(self, rhs: Self) -> Option<Self> {
                    let (q, r) = self.div_alg(rhs);
                    if r.is_zero() {Some(q)} else {None}
                }
            }

            impl NoZeroDivisors for $name {}

            impl GCD for $name {
                #[inline] fn lcm(self, rhs: Self) -> Self { NumInteger::gcd_lcm(&self, &rhs).1  }
                #[inline] fn gcd(self, rhs: Self) -> Self{ NumInteger::gcd(&self, &rhs) }
            }

            impl UniquelyFactorizable for $name {}

            impl Factorizable for $name {
                type Factors = TrialDivision<Self>;
                #[inline] fn factors(self) -> TrialDivision<Self> {TrialDivision::factors_of(self)}
            }

            impl EuclideanDiv for $name {
                type Naturals = $unsigned;
                #[inline] fn euclid_norm(&self) -> $unsigned {self.clone().abs_unsigned()}

                ///Euclidean division implemented using the `/` operator
                #[inline] fn div_euc(self, rhs: Self) -> Self {self / rhs}

                ///Euclidean remainder implemented using the `%` operator
                #[inline] fn rem_euc(self, rhs: Self) -> Self {self % rhs}

                ///
                ///Euclidean division implemented using the `/` and `%` operators
                ///
                ///Note that this does mean that the remainder may be negative and this method
                ///only guarantees that it satisfies the basic [Eucldidean division](EuclideanDiv::div_alg)
                ///axioms
                #[inline] fn div_alg(self, rhs: Self) -> (Self, Self) {(&self / &rhs, &self % &rhs)}
            }

            impl IntegerSubset for $name {
                type Signed = $signed;
                type Unsigned = $unsigned;
                #[inline] fn as_signed(self) -> $signed { <$signed>::from(self) }
                #[inline] fn as_unsigned(self) -> $unsigned { <$unsigned>::try_from(self).unwrap() }

                #[inline] fn two() -> Self { 2u32.into() }
                #[inline] fn mul_two(self) -> Self { self << 1 }
                #[inline] fn div_two(self) -> Self { self >> 1 }
                #[inline] fn even(&self) -> bool { NumInteger::is_even(self) }
                #[inline] fn odd(&self) -> bool { NumInteger::is_odd(self) }
            }

            impl Primality for $name {
                #[inline] fn irreducible(&self) -> bool { self.prime() }
                #[inline] fn prime(&self) -> bool { miller_rabin(self.clone().as_unsigned()) }
            }

        };

        ($signed:ty:$unsigned:ty) => {

            impl_bigint!($signed:$signed:$unsigned);
            impl_bigint!($unsigned:$signed:$unsigned);

            impl Bezout for $signed {
                #[inline]
                fn bezout_coefficients(self, rhs: Self) -> (Self, Self) {
                    let gcd = NumInteger::extended_gcd(&self, &rhs);
                    (gcd.x, gcd.y)
                }
                #[inline]
                fn bezout_with_gcd(self, rhs: Self) -> (Self, Self, Self) {
                    let gcd = NumInteger::extended_gcd(&self, &rhs);
                    (gcd.x, gcd.y, gcd.gcd)
                }
            }

            impl Integer for $signed {}
            impl Natural for $unsigned {}

        }

    }

    impl_bigint!{BigInt:BigUint}
}
