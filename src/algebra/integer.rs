
use std::convert::{TryFrom, TryInto};
use core::ops::{Rem, RemAssign};

use analysis::ordered::*;
use algebra::*;

auto!{
    pub trait CastPrimInt =
        TryFrom<i8>   + TryFrom<u8>   + TryInto<i8>   + TryInto<u8> +
        TryFrom<i16>  + TryFrom<u16>  + TryInto<i16>  + TryInto<u16> +
        TryFrom<i32>  + TryFrom<u32>  + TryInto<i32>  + TryInto<u32> +
        TryFrom<i64>  + TryFrom<u64>  + TryInto<i64>  + TryInto<u64> +
        TryFrom<i128> + TryFrom<u128> + TryInto<i128> + TryInto<u128>;
}

pub trait IntegerSubset: Ord + Eq + Clone + CastPrimInt
                        + EuclideanSemidomain
                        + Primality
                        + ArchSemiring
                        + Sub<Self, Output=Self> + Div<Self, Output=Self> + Rem<Self, Output=Self>
                        + SubAssign<Self> + DivAssign<Self> + RemAssign<Self>
{
    type Signed: Integer + IntegerSubset<Signed=Self::Signed, Unsigned=Self::Unsigned>;
    type Unsigned: Natural + IntegerSubset<Signed=Self::Signed, Unsigned=Self::Unsigned>;

    fn as_signed(&self) -> Self::Signed;
    fn as_unsigned(&self) -> Self::Unsigned;

    #[inline] fn two() -> Self { Self::one()+Self::one() }
    #[inline] fn mul_two(self) -> Self { self * Self::two() }
    #[inline] fn div_two(self) -> Self { self / Self::two() }

    #[inline] fn even(&self) -> bool {(Self::one()+Self::one()).divides(self.clone())}
    #[inline] fn odd(&self) -> bool {!self.even()}
}

pub trait Natural: IntegerSubset<Unsigned=Self> {}
pub trait Integer: IntegerSubset<Signed=Self> + ArchUnitalRing {}

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
    (@abs $self:ident $name:ident @signed) => {($self as $name).abs() };

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

        #[cfg(std)]
        impl Factorizable for $name {
            fn factors(&self) -> Vec<Self> {
                let mut factors = Vec::new();
                let mut a:$name = *self;

                if a==0 || a==1 {
                     //the factorization of 0 or a unit is itself
                    factors.push(*self);
                }else{
                    let mut i:$name = 2;
                    let mut start = true;
                    while a!=1 {
                        let (q, r) = (a as $name).div_alg(i.clone());
                        if r==0 {
                            //we found a factor!
                            a = q;
                            factors.push(i);
                        }else {
                            //not a factor :(
                            if i*i >= a {
                                //if a is definitely prime
                                factors.push(a);
                            }else {
                                //thus, we continue, skipping all non-2 evens
                                if start {
                                    i = 3;
                                    start = false;
                                } else {
                                    i = i + 2;
                                }
                            }
                        }
                    }
                }

                impl_int_subset!( @factors factors self $($tt)*);

                factors

            }
        }

        impl EuclideanDiv for $name {
            type Naturals = $unsigned;
            #[inline] fn euclid_norm(&self) -> $unsigned {self.as_signed().abs().as_unsigned()}
            
            ///Euclidean division implemented using the `/` operator
            #[inline] fn div_euc(self, rhs: Self) -> Self {self / rhs}

            ///Euclidean remainder implemented using the `%` operator
            #[inline] fn rem_euc(self, rhs: Self) -> Self {self % rhs}

            ///
            ///Euclidean division implemented using the `/` and `%` operators
            ///
            ///Note that this does mean that the remainder may be negative and this method
            ///only guarrantees that it satisfies the basic [Eucldidean division](EuclideanDiv::div_alg)
            ///axioms
            #[inline] fn div_alg(self, rhs: Self) -> (Self, Self) {(self / rhs, self % rhs)}
        }

        impl IntegerSubset for $name {
            type Signed = $signed;
            type Unsigned = $unsigned;
            #[inline] fn as_signed(&self) -> $signed { *self as $signed }
            #[inline] fn as_unsigned(&self) -> $unsigned {
                if cfg!(debug_assertions) && self.negative() {
                    panic!("Cannot make unsigned: {} < 0", self)
                } else {
                    *self as $unsigned
                }
            }

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
