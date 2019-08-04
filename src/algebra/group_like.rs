//!
//!Traits for sets with a single binary operation and various properties of that operation
//!
//!Currently, the group operation is interpreted as being either the [`Add`] or [`Mul`] operation,
//!and each of the group properties in this module have both an additive and multiplicative variant.
//!
//!As it stands currently, there is no real difference between the two, so it is ultimately up
//!to the implementor's preference which one (or both) to use. Obviously though, addition and multiplication
//!carry difference connotations in different contexts, so for clarity and consistency it is
//!suggested to try to follow the general mathematical or programming conventions whenever possible.
//!In particular:
//!* Try to use multiplication for structures with a single operation
//!except when convention dictates otherwise (such as the case of string concatenation).
//!* While the option does exist, avoid implementing a non-commutative or especially a non-associative
//!addition operation unless convention dictates otherwise.
//!* Avoid implementing both an addition and multiplication where the multiplication *doesn't* distrubute
//!or where the addition distributes instead.
//!
//!# Implementation
//!
//!To implement a struct as a group-like structure, the various group-like trait aliases will be usable
//!according to which and how the following properties are implemented:
//!* An additive or multiplicative binary operation:
//!    * Has some function taking any pair of elements from `Self` and outputing any other member of `Self`
//!    * Represented with either [`Add`] and [`AddAssign`] or [`Mul`] and [`MulAssign`] from [`std::ops`]
//!    * (Note that for the auto-implementing categorization traits to work, the corresponding
//!      "Assign" traits must be implemented.)
//!* An identity element:
//!    * Contains a unique element `0` or `1` such that `0+x=x` and `x+0=x` or
//!     `1*x=x`,`x*1=x` for all `x`
//!    * Represented with either [`Zero`] or [`One`] from [`num_traits`]
//!* Invertibility:
//!    * For every `x` in the set, there exists some other `y` in the struct such that
//!     `x*y=1` and `y*x=1` (or `x+y=0` and `y+x=0` if additive), and there exists
//!     a corresponding inverse operation.
//!    * Represented with either [`Neg`], [`Sub`], and [`SubAssign`] or [`Inv`], [`Div`], and [`DivAssign`]
//!      from [`std::ops`] and [`num_traits`]
//!    * Note, again, that the "Assign" variants are required
//!* Commutative:
//!    * If the operation is order invariant, ie `x+y=y+x` or `x*y=y*x` for all `x` and `y`.
//!    * Represented with [`AddCommutative`] or [`MulCommutative`]
//!* Associative:
//!    * If operation sequences are _evaluation_ order invariant, ie `x+(y+z)=(x+y)+z` or `x*(y*z)=(x*y)*z`
//!     for all `x`, `y`, and `z`.
//!    * Represented with [`AddAssociative`] or [`MulAssociative`]
//!
//!# Exponentiation
//!
//!In addition to these traits, it may be desirable to implement a [multiplication](Mul) or
//![exponentiation](num_traits::Pow) operation with particular [integer](crate::algebra::Integer)
//!or [natural](crate::algebra::Natural) type. See [`MulN`], [`MulZ`], [`PowN`], and [`PowZ`] for more details.
//!
//!# Usage
//!
//!Structs with the above properties implemented will be automatically usable under a number of trait
//!aliases for particular group-like structures. These structures follow standard mathematical
//!convention and roughly correspond to a heirarchy varying levels of "niceness" of each
//!binary operation.
//!
//!These structures can be diagrammed as follows:
//!```text
//!    ---Magma---
//!    |         |
//!    |     Semigroup
//!   Loop       |
//!    |      Monoid
//!    |         |
//!    ---Group---
//!         |
//!   Abelian Group
//!```
//!where:
//!* A [Magma](MulMagma) is a set with any binary operation
//!* A [Semigroup](MulSemigroup) is an [associative](MulAssociative) Magma
//!* A [Monoid](MulMonoid) is a Semigroup with an [identity](One) element
//!* A [Loop](MulLoop) is a Magma with an [identity](One) element and [inverses](Invertable)
//!* A [Group](MulGroup) is a Monoid with [inverses](Invertable), or alternatively, an [associative](MulAssociative) Loop
//!* An [Abelian Group](MulAbelianGroup) is a [commutative](MulCommutative) Group
//!
//!For more information, see Wikipedia's article on 
//![algebraic structures](https://en.wikipedia.org/wiki/Outline_of_algebraic_structures)
//!
//!# Additional Notes
//!
//!It is worth noting that this particular system is certainly non-exhaustive and is missing a number
//!of group-like structures. In particular, it is missing the Category-like structures and Quasigroups
//!
//!In the case of categories, this is because as it stands currently, there are few uses for partial
//!operations while including them would add noticeable complexity.
//!
//!In the case of quasigroups however, the reason is because with the way the primitive types are
//!designed, the only way to determine if an addition or subtraction operation is *truely* invertible
//!is to check against the [Neg] or [Inv] traits, as the unsigned integers implement **both** division
//!and subtraction even though technically those operations are not valid on all natural numbers.
//!So seeing as quasigroups aren't particularly useful anyway, the decision was made to omit them.
//!
//!

pub use self::additive::*;
pub use self::multiplicative::*;

///Traits for group-like structures using addition
pub mod additive {
    pub use core::ops::{Add, Sub, Neg, AddAssign, SubAssign};
    pub use num_traits::{Zero};
    use core::convert::{From};
    use core::ops::{Mul};

    use super::{repeated_doubling, repeated_doubling_neg};
    use crate::algebra::{Natural, IntegerSubset, Semiring, Ring};

    #[allow(unused_imports)] use crate::algebra::Integer;

    ///
    ///A marker trait for stucts whose addition operation is evaluation order independent,
    ///ie `x+(y+z)=(x+y)+z` for all `x`, `y`, and `z`.
    ///
    ///This is an extremely common property, and _most_ commonly used algebraic systems have it.
    ///Nonetheless, there are some algebraic constructions like loop concatenation, the cross product,
    ///lie algebras, and octonions that do not have this property, so the option to _not_ implement it exists.
    ///
    ///Note however, it is _highly_ recommended to implement non-associative structs as multiplicative
    ///to be consistent with convention.
    ///
    pub trait AddAssociative {}

    ///
    ///A marker trait for stucts whose addition operation is order independent,
    ///ie `x+y=y+x` for all `x`, `y`, and `z`.
    ///
    ///This is an extremely common property, and _most_ commonly used algebraic systems have it.
    ///Nonetheless, there are also a fairly number of algebraic constructions do not, such as
    ///matrix multiplication, most finite groups, and in particular, string concatenation.
    ///
    ///Note however, it is _highly_ recommended to implement non-commutative structs
    ///(except string concatentation) as multiplicative to be consistent with convention.
    ///
    pub trait AddCommutative {}

    ///
    ///An auto-implemented trait for multiplication by [natural numbers](Natural) with
    ///[associative](AddAssociative) types using repeated addition
    ///
    ///This is intended as a simple and easy way to compute object multiples in abstract algebraic
    ///algorithms without resorting to explicitly applying addition repeatedly. For this reason, the
    ///trait is automatically implemented for any relevant associative algebraic structure and
    ///the supplied function is generic over the [`Natural`] type.
    ///
    ///```
    ///# use maths_traits::algebra::*;
    ///
    /// assert_eq!(2.5f32.mul_n(4u8), 10.0);
    /// assert_eq!(2.5f32.mul_n(4u16), 10.0);
    /// assert_eq!(2.5f32.mul_n(4u128), 10.0);
    /// assert_eq!(2.5f64.mul_n(4u8), 10.0);
    /// assert_eq!(2.5f64.mul_n(4u16), 10.0);
    /// assert_eq!(2.5f64.mul_n(4u128), 10.0);
    ///
    ///```
    ///
    ///# Usage Notes
    ///
    ///This trait is intended for use with *small* integers and can make no guarrantee that the
    ///mathematical output will actually fit in the valid range for the output type. As such,
    ///it is possible for the method to panic, overflow, or return an NaN or error value, so if this
    ///is an expected possibility, it is recommended to use [TryInto](core::convert::TryInto) or
    ///a different to perform the operation.
    ///
    ///It is worth noting that this particular design was chosen over returning a [Result](core::Result)
    ///or [Option](core::Option) since this general behavior is already the default for primitive types
    ///despite the relative ease with which it can happen.
    ///
    ///# Implementation Notes
    ///
    ///Note that while multiplication by natural numbers is very simply defined using
    ///repeated addition, in order to add flexibility in implementation and the possibility for
    ///proper optimization, the automatic implmentation of this trait will first try to use other
    ///traits as a base before defaulting to the general [repeated_doubling] algorithm
    ///
    ///Specifically, for a given [Natural] type `N`, the auto-impl will first attempt to use
    ///[`Mul<N>`](Mul), if implemented. If that fails, it will then try to convert using [`From<N>`](From)
    ///and multiplying if if it implemented and the struct is a [Semiring].
    ///Finally, in the general case, it will use the [repeated_doubling] function.
    ///
    pub trait MulN: AddSemigroup + Zero {
        #[inline]
        fn mul_n<N:Natural>(self, n:N) -> Self {

            trait Helper1<Z:Natural>: AddSemigroup + Zero { fn _mul1(self, n:Z) -> Self; }
            impl<H: AddSemigroup + Zero, Z:Natural> Helper1<Z> for H {
                #[inline] default fn _mul1(self, n:Z) -> Self {self._mul2(n)}
            }
            impl<H: AddSemigroup + Zero + Mul<Z,Output=H>, Z:Natural> Helper1<Z> for H {
                #[inline] fn _mul1(self, n:Z) -> Self {self * n}
            }

            trait Helper2<Z:Natural>: AddSemigroup + Zero { fn _mul2(self, n:Z) -> Self; }
            impl<H: AddSemigroup + Zero, Z:Natural> Helper2<Z> for H {
                #[inline] default fn _mul2(self, n:Z) -> Self {repeated_doubling(self, n)}
            }
            impl<H: Semiring + From<Z>, Z:Natural> Helper2<Z> for H {
                #[inline] fn _mul2(self, n:Z) -> Self {H::from(n) * self}
            }

            self._mul1(n)
        }
    }

    impl<G:AddSemigroup + Zero> MulN for G {}

    ///
    ///An auto-implemented trait for multiplication by [integers](Integer) with
    ///[associative](AddAssociative) and [negatable](Negatable) types using
    ///negation and repeated addition
    ///
    ///This is intended as a simple and easy way to compute object multiples in abstract algebraic
    ///algorithms without resorting to explicitly applying addition repeatedly. For this reason, the
    ///trait is automatically implemented for any relevant associative and negatable algebraic structure and
    ///the supplied function is generic over the [`Integer`] type.
    ///
    ///```
    ///# use maths_traits::algebra::*;
    ///
    /// assert_eq!(2.5f32.mul_z(5u8), 12.5);
    /// assert_eq!(2.5f32.mul_z(5u128), 12.5);
    /// assert_eq!(2.5f64.mul_z(5u8), 12.5);
    /// assert_eq!(2.5f64.mul_z(5u128), 12.5);
    /// assert_eq!(2.5f32.mul_z(-5i8), -12.5);
    /// assert_eq!(2.5f32.mul_z(-5i64), -12.5);
    ///
    ///```
    ///
    ///# Usage Notes
    ///
    ///This trait is intended for use with *small* integers and can make no guarrantee that the
    ///mathematical output will actually fit in the valid range for the output type. As such,
    ///it is possible for the method to panic, overflow, or return an NaN or error value, so if this
    ///is an expected possibility, it is recommended to use [TryInto](core::convert::TryInto) or
    ///a different to perform the operation.
    ///
    ///It is worth noting that this particular design was chosen over returning a [Result](core::Result)
    ///or [Option](core::Option) since this general behavior is already the default for primitive types
    ///despite the relative ease with which it can happen.
    ///
    ///# Implementation Notes
    ///
    ///Note that while multiplication by integers is very simply defined using
    ///repeated addition and subtraction, in order to add flexibility in implementation and the possibility for
    ///proper optimization, the automatic implmentation of this trait will first try to use other
    ///traits as a base before defaulting to the general [repeated_doubling_neg] algorithm
    ///
    ///Specifically, for a given [Integer] type `Z`, the auto-impl will first attempt to use
    ///[`Mul<Z>`](Mul), if implemented. If that fails, it will then try to convert using [`From<Z>`](From)
    ///and multiplying if if it implemented and the struct is a [Ring].
    ///Finally, in the general case, it will use the [repeated_doubling_neg] function.
    ///
    pub trait MulZ: AddMonoid + Negatable {
        #[inline]
        fn mul_z<N:IntegerSubset>(self, n:N) -> Self {

            trait Helper1<Z:IntegerSubset>: AddMonoid + Negatable { fn _mul1(self, n:Z) -> Self; }
            impl<H: AddMonoid + Negatable, Z:IntegerSubset> Helper1<Z> for H {
                #[inline] default fn _mul1(self, n:Z) -> Self {self._mul2(n)}
            }
            impl<H: AddMonoid + Negatable + Mul<Z,Output=H>, Z:IntegerSubset> Helper1<Z> for H {
                #[inline] fn _mul1(self, n:Z) -> Self {self * n}
            }

            trait Helper2<Z:IntegerSubset>: AddSemigroup + Zero { fn _mul2(self, n:Z) -> Self; }
            impl<H: AddMonoid + Negatable, Z:IntegerSubset> Helper2<Z> for H {
                #[inline] default fn _mul2(self, n:Z) -> Self {repeated_doubling_neg(self, n)}
            }
            impl<H: Ring + From<Z>, Z:IntegerSubset> Helper2<Z> for H {
                #[inline] fn _mul2(self, n:Z) -> Self {H::from(n) * self}
            }

            self._mul1(n)
        }
    }

    impl<G:AddMonoid + Negatable> MulZ for G {}

    ///A set with an fully described additive inverse
    pub trait Negatable = Sized + Clone + Neg<Output=Self> + Sub<Self, Output=Self> + SubAssign<Self>;

    ///A set with an addition operation
    pub trait AddMagma = Sized + Clone + Add<Self,Output=Self> + AddAssign<Self>;
    ///An associative additive magma
    pub trait AddSemigroup = AddMagma + AddAssociative;
    ///An additive semigroup with an identity element
    pub trait AddMonoid = AddSemigroup + Zero + MulN;
    ///An additive magma with an inverse operation and identity
    pub trait AddLoop = AddMagma + Negatable + Zero;
    ///An additive monoid with an inverse operation
    pub trait AddGroup = AddMagma + AddAssociative + Negatable + Zero + MulZ;
    ///A commutative additive group
    pub trait AddAbelianGroup = AddGroup + AddCommutative;

}

///Traits for group-like structures using Multiplication
pub mod multiplicative {
    pub use core::ops::{Mul, Div, MulAssign, DivAssign};
    pub use num_traits::{Inv, One};
    use num_traits::Pow;

    use super::{repeated_squaring, repeated_squaring_inv};
    use crate::algebra::{Natural, IntegerSubset};

    #[allow(unused_imports)] use crate::algebra::Integer;

    ///
    ///A marker trait for stucts whose multiplication operation is evaluation order independent,
    ///ie `x*(y*z)=(x*y)*z` for all `x`, `y`, and `z`.
    ///
    ///This is an extremely common property, and _most_ commonly used algebraic systems have it.
    ///Nonetheless, there are some algebraic constructions like loop concatenation, the cross product,
    ///lie algebras, and octonions that do not have this property, so the option to _not_ implement it exists.
    ///
    pub trait MulAssociative: {}

    ///
    ///A marker trait for stucts whose addition operation is order independent,
    ///ie `x+y=y+x` for all `x`, `y`, and `z`.
    ///
    ///This is an extremely common property, and _most_ commonly used algebraic systems have it.
    ///Nonetheless, there are also a fairly number of algebraic constructions do not, such as
    ///matrix multiplication and most finite groups.
    ///
    pub trait MulCommutative {}

    ///
    ///An auto-implemented trait for exponentiation by [natural numbers](Natural) with
    ///[associative](MulAssociative) types using repeated multiplication
    ///
    ///This is intended as a simple and easy way to compute object powers in abstract algebraic
    ///algorithms without resorting to explicitly applying multiplication repeatedly. For this reason, the
    ///trait is automatically implemented for any relevant associative algebraic structure and
    ///the supplied function is generic over the [`Natural`] type.
    ///
    ///```
    ///# use maths_traits::algebra::*;
    ///
    /// assert_eq!(2.0f32.pow_n(4u8), 16.0);
    /// assert_eq!(2.0f32.pow_n(4u16), 16.0);
    /// assert_eq!(2.0f32.pow_n(4u128), 16.0);
    /// assert_eq!(2.0f64.pow_n(4u8), 16.0);
    /// assert_eq!(2.0f64.pow_n(4u16), 16.0);
    /// assert_eq!(2.0f64.pow_n(4u128), 16.0);
    ///
    ///```
    ///# Usage Notes
    ///
    ///This trait is intended for use with *small* integers and can make no guarrantee that the
    ///mathematical output will actually fit in the valid range for the output type. As such,
    ///it is possible for the method to panic, overflow, or return an NaN or error value, so if this
    ///is an expected possibility, it is recommended to use [TryInto](core::convert::TryInto) or
    ///a different to perform the operation.
    ///
    ///It is worth noting that this particular design was chosen over returning a [Result](core::Result)
    ///or [Option](core::Option) since this general behavior is already the default for primitive types
    ///despite the relative ease with which it can happen.
    ///
    ///# Implementation Notes
    ///
    ///Note that while exponentiation by natural numbers is very simply defined using
    ///repeated multiplication, in order to add flexibility in implementation and the possibility for
    ///proper optimization, the automatic implmentation of this trait will first try to use other
    ///traits as a base before defaulting to the general [repeated_squaring] algorithm
    ///
    ///Specifically, for a given [Natural] type `N`, the auto-impl will first attempt to use
    ///[`Pow<N>`](Pow), if implemented, then if that fails, it will use the general
    ///[repeated_squaring] algorithm
    ///
    pub trait PowN: MulSemigroup + One {
        #[inline]
        fn pow_n<N:Natural>(self, n:N) -> Self {
            trait Helper<Z:Natural>: MulSemigroup + One { fn _pow_n(self, n:Z) -> Self; }
            impl<G:MulSemigroup+One, Z:Natural> Helper<Z> for G {
                #[inline] default fn _pow_n(self, n:Z) -> Self {repeated_squaring(self, n)}
            }
            impl<G:MulSemigroup+One+Pow<Z,Output=Self>, Z:Natural> Helper<Z> for G {
                #[inline] fn _pow_n(self, n:Z) -> Self {self.pow(n)}
            }

            self._pow_n(n)
        }
    }
    impl<G:MulSemigroup+One> PowN for G {}

    ///
    ///An auto-implemented trait for exponentiation by [integers](Integer) with
    ///[associative](MulAssociative) and [invertable](Invertable) types using
    ///inversion and repeated multiplication
    ///
    ///This is intended as a simple and easy way to compute object powers in abstract algebraic
    ///algorithms without resorting to explicitly applying multiplication repeatedly. For this reason, the
    ///trait is automatically implemented for any relevant associative and invertable algebraic structure and
    ///the supplied function is generic over the [`Integer`] type.
    ///
    ///```
    ///# use maths_traits::algebra::*;
    ///
    /// assert_eq!(2.0f32.pow_z(3u8), 8.0);
    /// assert_eq!(2.0f32.pow_z(3u128), 8.0);
    /// assert_eq!(2.0f64.pow_z(3u8), 8.0);
    /// assert_eq!(2.0f64.pow_z(3u128), 8.0);
    /// assert_eq!(2.0f32.pow_z(-3i8), 0.125);
    /// assert_eq!(2.0f32.pow_z(-3i64), 0.125);
    ///
    ///```
    ///# Usage Notes
    ///
    ///This trait is intended for use with *small* integers and can make no guarrantee that the
    ///mathematical output will actually fit in the valid range for the output type. As such,
    ///it is possible for the method to panic, overflow, or return an NaN or error value, so if this
    ///is an expected possibility, it is recommended to use [TryInto](core::convert::TryInto) or
    ///a different to perform the operation.
    ///
    ///It is worth noting that this particular design was chosen over returning a [Result](core::Result)
    ///or [Option](core::Option) since this general behavior is already the default for primitive types
    ///despite the relative ease with which it can happen.
    ///
    ///# Implementation Notes
    ///
    ///Note that while exponentiation by integers is very simply defined using
    ///repeated multiplication and inversion, in order to add flexibility in implementation and the possibility for
    ///proper optimization, the automatic implmentation of this trait will first try to use other
    ///traits as a base before defaulting to the general [repeated_squaring_inv] algorithm
    ///
    ///Specifically, for a given [Natural] type `N`, the auto-impl will first attempt to use
    ///[`Pow<N>`](Pow), if implemented, then if that fails, it will use the general
    ///[repeated_squaring_inv] algorithm
    ///
    pub trait PowZ: MulMonoid + Invertable {
        #[inline]
        fn pow_z<Z:IntegerSubset>(self, n:Z) -> Self {
            trait Helper<N:IntegerSubset>: MulMonoid + Invertable { fn _pow_z(self, n:N) -> Self; }
            impl<G:MulMonoid+Invertable, N:IntegerSubset> Helper<N> for G {
                #[inline] default fn _pow_z(self, n:N) -> Self {repeated_squaring_inv(self, n)}
            }
            impl<G:MulMonoid+Invertable+Pow<N,Output=Self>, N:IntegerSubset> Helper<N> for G {
                #[inline] fn _pow_z(self, n:N) -> Self {self.pow(n)}
            }

            self._pow_z(n)
        }
    }
    impl<G:MulMonoid+Invertable> PowZ for G {}


    ///A set with an fully described multiplicative inverse
    pub trait Invertable = Sized + Clone + Inv<Output=Self> + Div<Self, Output=Self> + DivAssign<Self>;
    ///A set with a multiplication operation
    pub trait MulMagma = Sized + Clone + Mul<Self, Output=Self> + MulAssign<Self>;
    ///An associative multiplicative magma
    pub trait MulSemigroup = MulMagma + MulAssociative;
    ///A multiplicative semigroup with an identity element
    pub trait MulMonoid = MulSemigroup + One + PowN;
    ///A multiplicative magma with an inverse operation and identity
    pub trait MulLoop = MulMagma + Invertable + One;
    ///A multiplicative monoid with an inverse operation
    pub trait MulGroup = MulMagma + MulAssociative + Invertable + One + PowZ;
    ///A commutative multiplicative group
    pub trait MulAbelianGroup = MulGroup + MulCommutative;
}

use crate::algebra::{Natural, IntegerSubset};

trait IsZero:Sized { fn _is_zero(&self) -> bool; }
impl<Z> IsZero for Z { #[inline(always)] default fn _is_zero(&self) -> bool {false} }
impl<Z:Zero> IsZero for Z { #[inline(always)] fn _is_zero(&self) -> bool {self.is_zero()} }

fn mul_pow_helper<E:Natural, R:Clone, Op: Fn(R,R) -> R>(mut b: R, mut p: E, op: Op) -> R {
    //repeated squaring/doubling
    let mut res = b.clone();
    p -= E::one();
    while !p.is_zero() {
        if p.even() {
            //if the exponent (or multiple) is even, we can factor out the two
            //ie b^2p = (b^2)^p or 2p*b = p*2b
            b = op(b.clone(), b);
            p = p.div_two();
        } else {
            //else b^(p+1)=(b^p)*b or (p+1)*b = p*b + b
            res = op(res, b.clone());
            p -= E::one();
        }
    }
    res
}

///
///Raises a [monoid](MulMonoid) element to a integral power using inversion and repeated squaring
///
///# Panics
///If both the base and power are `0`
///
#[inline]
pub fn repeated_squaring_inv<E:IntegerSubset, R:MulGroup+Clone>(b: R, p: E) -> R {
    if p.negative() {
        repeated_squaring(b, p.abs_unsigned()).inv()
    } else {
        repeated_squaring(b, p.as_unsigned())
    }
}

///
///Raises a [monoid](MulMonoid) element to a positive integer power using the repeated squaring algorithm
///
///# Panics
///If both the base and power are `0`
///
#[inline]
pub fn repeated_squaring<E:Natural, R:MulMonoid+Clone>(b: R, p: E) -> R {
    if p.is_zero() {
        if b._is_zero() { panic!("Attempted to raise 0^0") }
        R::one()
    } else {
        mul_pow_helper(b, p, R::mul)
    }
}


///Multiplies a [monoid](AddMonoid) by a positive integer using negation and repeated doublings
#[inline]
pub fn repeated_doubling_neg<E:IntegerSubset, R:AddGroup>(b: R, p: E) -> R {
    if p.negative() {
        -repeated_doubling(b, p.abs_unsigned())
    } else {
        repeated_doubling(b, p.as_unsigned())
    }
}

///Multiplies a [monoid](AddMonoid) by a positive integer using repeated doublings
#[inline]
pub fn repeated_doubling<E:Natural, R:AddMonoid>(b: R, p: E) -> R {
    if p.is_zero() {
        R::zero()
    } else {
        mul_pow_helper(b, p, R::add)
    }
}

macro_rules! impl_props {
    ($($z:ty)*; $($f:ty)*) => {
        $(impl_props!(@int $z);)*
        $(impl_props!(@float $f);)*
    };

    (@int $z:ty) => {
        impl_props!(@props $z);
        impl_props!(@props core::num::Wrapping<$z>);
    };
    (@float $f:ty) => {impl_props!(@props $f);};
    (@props $t:ty) => {

        impl AddAssociative for $t {}
        impl AddCommutative for $t {}
        impl MulAssociative for $t {}
        impl MulCommutative for $t {}
    };
}

impl_props!{ usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128; f32 f64 }

#[cfg(std)] impl<'a> AddAssociative for ::std::borrow::Cow<'a,str> {}
