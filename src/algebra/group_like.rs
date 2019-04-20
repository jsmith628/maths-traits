//!
//!Traits for sets with a single binary operation and various properties of that operation
//!
//!Currently, the group operation is interpreted as being either the [`Add`] or [`Mul`] operation,
//!and each of the group properties in this module have both an additive and multiplicative variant.
//!
//!As it stands currently, there is no real difference between the two, so it is ultimately up
//!to the implementor's preference which one (or both) to use. However, obviously, addition and multiplication
//!carry difference connotations in different contexts, so for clarity and consistency it is
//!suggested to try to follow the general mathematical or programming conventions whenever possible.
//!In particular:
//!* Try to use multiplication for single operation structures
//!except when convention dictates otherwise (such as the case of string concatenation).
//!* While the option does exist, avoid implementing a non-commutative or especially a non-associative
//!addition operation unless convention dictates otherwise.
//!* Avoid implementing both an addition and multiplication where the multiplication *doesn't* distrubute
//!or where the addition distributes instead.
//!
//!# Implementation
//!
//!The inclusion of a particular struct into a group-like trait will depend on its implementation
//!of the following properties:
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
//![exponentiation](num_traits::Pow) operation with particular [integers](::algebra::Integer)
//!or [naturals](::algebra::Natural). See [`MulN`], [`MulZ`], [`PowN`], and [`PowZ`] for more details.
//!
//!# Usage
//!
//!Structs with these properties implemented will be automatically added to a number of categorization
//!traits for various mathematical sets. These traits all have additive and multiplicative variants
//!and fit into a heirarchy of mathematical structures as such:
//!``` ignore
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

pub use self::additive::*;
pub use self::multiplicative::*;

//Note: we do not have additive or multiplicative quasigroups because some types
//override operators while guarranteeing too little.
//For example, to have a multiplicative quasigroup, we'd need true division, but all
//primitive int types have a division operation that is mathematically incorrect
//(even if convenient). So the best way to weed these out is with the inv trait, but
//*technically* there may not be true "inverses" in quasigroups. But whatever, quasigroups aren't
//particularly useful anyway

///Traits for group-like structures using addition
pub mod additive {
    pub use core::ops::{Add, Sub, Neg, AddAssign, SubAssign};
    pub use num_traits::{Zero};
    use core::convert::{From, Into};
    use core::ops::{Mul};

    use super::{repeated_doubling, repeated_doubling_neg};
    use algebra::{Natural, IntegerSubset, Semiring, Ring};

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

    pub trait MulN: AddSemigroup + Zero { fn mul_n<N:Natural>(self, n:N) -> Self; }
    pub trait MulZ: AddMonoid + Negatable { fn mul_z<Z:IntegerSubset>(self, n:Z) -> Self; }

    impl<G:AddSemigroup + Zero> MulN for G {
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
                #[inline] fn _mul2(self, n:Z) -> Self {self * n.into()}
            }

            self._mul1(n)
        }
    }

    impl<G:AddMonoid + Negatable> MulZ for G {
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
                #[inline] fn _mul2(self, n:Z) -> Self {self * n.into()}
            }

            self._mul1(n)
        }
    }

    auto!{

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

        pub trait AddSubmagma<G> = AddMagma + Add<G,Output=G> where G:AddMagma;
        pub trait AddSubsemigroup<G> = AddSemigroup + AddSubmagma<G> where G:AddMagma;
        pub trait AddSubmonoid<G> = AddMonoid + AddSubmagma<G> where G:AddMonoid;
        pub trait AddSubloop<G> = AddLoop + AddSubmagma<G> + Sub<G,Output=G> where G:AddLoop;
        pub trait AddSubgroup<G> = AddGroup + AddSubmagma<G> + Sub<G,Output=G> where G:AddGroup;
        pub trait AddAbelianSubgroup<G> = AddAbelianGroup + AddSubgroup<G> where G:AddGroup;

        pub trait AddSupermagma<H> = AddMagma + Add<H,Output=Self> + AddAssign<H> where H:AddMagma;
        pub trait AddSupersemigroup<H> = AddSemigroup + AddSupermagma<H> where H:AddSemigroup;
        pub trait AddSupermonoid<H> = AddMonoid + AddSupermagma<H> where H:AddMonoid;
        pub trait AddSuperloop<H> = AddLoop + AddSupermagma<H> + Sub<H,Output=Self> + SubAssign<H> where H:AddLoop;
        pub trait AddSupergroup<H> = AddGroup + AddSupermagma<H> + Sub<H,Output=Self> + SubAssign<H> where H:AddGroup;
        pub trait AddAbelianSupergroup<H> = AddAbelianGroup + AddSupergroup<H> where H:AddAbelianGroup;
    }

}

///Traits for group-like structures using Multiplication
pub mod multiplicative {
    pub use core::ops::{Mul, Div, MulAssign, DivAssign};
    pub use num_traits::{Inv, One};
    use num_traits::Pow;

    use super::{repeated_squaring, repeated_squaring_inv};
    use algebra::{Natural, IntegerSubset};

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

    trait PowNHelper<N:Natural>: MulSemigroup + One { fn _pow_n(self, n:N) -> Self; }
    impl<G:MulSemigroup+One+Pow<N,Output=Self>, N:Natural> PowNHelper<N> for G {
        #[inline] fn _pow_n(self, n:N) -> Self {self.pow(n)}
    }
    impl<G:MulSemigroup+One, N:Natural> PowNHelper<N> for G {
        #[inline] default fn _pow_n(self, n:N) -> Self {repeated_squaring(self, n)}
    }

    trait PowZHelper<Z:IntegerSubset>: MulSemigroup + One { fn _pow_z(self, n:Z) -> Self; }
    impl<G:MulMonoid+Invertable+Pow<Z,Output=Self>, Z:IntegerSubset> PowZHelper<Z> for G {
        #[inline] fn _pow_z(self, n:Z) -> Self {self.pow(n)}
    }
    impl<G:MulMonoid+Invertable, Z:IntegerSubset> PowZHelper<Z> for G {
        #[inline] default fn _pow_z(self, n:Z) -> Self {repeated_squaring_inv(self, n)}
    }

    pub trait PowN: MulSemigroup + One {
        #[inline] fn pow_n<N:Natural>(self, n:N) -> Self {self._pow_n(n)}
    }
    pub trait PowZ: MulMonoid + Invertable {
        #[inline] fn pow_z<Z:IntegerSubset>(self, n:Z) -> Self {self._pow_z(n)}
    }
    impl<G:MulSemigroup+One> PowN for G {}
    impl<G:MulMonoid+Invertable> PowZ for G {}

    auto!{

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

        pub trait MulSubmagma<G> = MulMagma + Mul<G,Output=G> where G:MulMagma;
        pub trait MulSubsemigroup<G> = MulSemigroup + MulSubmagma<G> where G:MulMagma;
        pub trait MulSubmonoid<G> = MulMonoid + MulSubmagma<G> where G:MulMonoid;
        pub trait MulSubloop<G> = MulLoop + MulSubmagma<G> + Div<G,Output=G> where G:MulLoop;
        pub trait MulSubgroup<G> = MulGroup + MulSubmagma<G> + Div<G,Output=G> where G:MulGroup;
        pub trait MulAbelianSubgroup<G> = MulAbelianGroup + MulSubgroup<G> where G:MulGroup;

        pub trait MulSupermagma<H> = MulMagma + Mul<H,Output=Self> + MulAssign<H> where H:MulMagma;
        pub trait MulSupersemigroup<H> = MulSemigroup + MulSupermagma<H> where H:MulSemigroup;
        pub trait MulSupermonoid<H> = MulMonoid + MulSupermagma<H> where H:MulMonoid;
        pub trait MulSuperloop<H> = MulLoop + MulSupermagma<H> + Div<H,Output=Self> + DivAssign<H> where H:MulLoop;
        pub trait MulSupergroup<H> = MulGroup + MulSupermagma<H> + Div<H,Output=Self> + DivAssign<H> where H:MulGroup;
        pub trait MulAbelianSupergroup<H> = MulAbelianGroup + MulSupergroup<H> where H:MulAbelianGroup;
    }



}

use algebra::{Natural, IntegerSubset};

trait IsZero { fn _is_zero(&self) -> bool; }
impl<Z> IsZero for Z {  #[inline(always)] default fn _is_zero(&self) -> bool {false} }
impl<Z:Zero> IsZero for Z {  #[inline(always)] fn _is_zero(&self) -> bool {self.is_zero()} }

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
            p = p - E::one();
        }
    }
    res
}

#[inline]
pub fn repeated_squaring_inv<E:IntegerSubset, R:MulGroup+Clone>(b: R, p: E) -> R {
    if p.negative() {
        repeated_squaring(b, p.as_unsigned()).inv()
    } else {
        repeated_squaring(b, p.as_unsigned())
    }
}

#[inline]
pub fn repeated_squaring<E:Natural, R:MulMonoid+Clone>(b: R, p: E) -> R {
    if p.is_zero() {
        if b._is_zero() { panic!("Attempted to raise 0^0") }
        R::one()
    } else {
        mul_pow_helper(b, p, R::mul)
    }
}

#[inline]
pub fn repeated_doubling_neg<E:IntegerSubset, R:AddGroup+Clone>(b: R, p: E) -> R {
    if p.negative() {
        -repeated_doubling(b, p.as_unsigned())
    } else {
        repeated_doubling(b, p.as_unsigned())
    }
}

#[inline]
pub fn repeated_doubling<E:Natural, R:AddMonoid+Clone>(b: R, p: E) -> R {
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

    (@int $z:ty) => {impl_props!(@props $z);};
    (@float $f:ty) => {impl_props!(@props $f);};
    (@props $t:ty) => {
        impl AddAssociative for $t {}
        impl AddCommutative for $t {}

        impl MulAssociative for $t {}
        impl MulCommutative for $t {}

    };
}

impl_props!{ usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128; f32 f64 }
