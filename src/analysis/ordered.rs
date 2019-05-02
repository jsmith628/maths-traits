
use algebra::*;

///
///A marker trait signifying that for `x > y`, `x+z > x+z` and `z+x > z+x` for all `z`
///
///Note that for [monoids](AddMonoid) with some negative or positive element `x` this
///_automatically_ means that the magma is infinite, as otherwise, there would be a
///maximum element `M` and minimum `m`, contradicting `M + x > M + 0 = M` (if `x > 0`)
///or `m + x < m + 0 = m` (if `x < 0`). (Of course, the bitwise representations of these
///structures size limited by size, but in practice, we treat them as infinite anyway.)
///
///Futhermore, for [monoids](AddMonoid) and [groups](AddGroup), this provides a way to embed the
///[Naturals](Natural) and [Integers](Integer) into the structure respectively, and if the structure also is
///an ordered semiring with [one](One), then there is even a canonical embedding following both addition
///and multiplication rules
///
pub trait AddOrdered: PartialOrd {}

///
///A marker trait signifying that for `x > y`, `x*z > x*z` and `z*x > z*x` for all `z > 0`
///
///Like for [AddOrdered], for this also implies for non-trivial structures that they are infinite
///and provides for embeddings of the [Naturals](Natural) and [Integers](Integer) in much the same
///way.
///
pub trait MulOrdered: PartialOrd {}

///Helpful methods for measuring an element's order relative to 0
pub trait Signed: PartialOrd + Zero {
    ///If this element is strictly greater than zero
    fn positive(&self) -> bool;
    ///If this element is strictly less than zero
    fn negative(&self) -> bool;
    ///If this element is greater than or equal to zero
    fn non_negative(&self) -> bool;
    ///If this element is less than or equal to zero
    fn non_positive(&self) -> bool;
}

///Auto-implemented using `default` to allow for specialization if desired
impl<G: PartialOrd + Zero> Signed for G {
    #[inline] default fn positive(&self) -> bool { self > &Self::zero() }
    #[inline] default fn negative(&self) -> bool { self < &Self::zero() }
    #[inline] default fn non_negative(&self) -> bool { self >= &Self::zero() }
    #[inline] default fn non_positive(&self) -> bool { self <= &Self::zero() }
}

///Helpful methods for manipulating an element's order relative to 0
pub trait Sign: Signed + One + Neg<Output=Self> {
    ///Returns 1 if positive, -1 if negative, or itself (ie. 0 or NaN) if neither
    fn signum(self) -> Self;
    ///Returns this element's negative if less than 0 or itself otherwise
    fn abs(self) -> Self;
}

///Auto-implemented using `default` to allow for specialization if desired
impl<G: Signed + One + Neg<Output=Self>> Sign for G {
    #[inline]
    default fn signum(self) -> Self {
        if self.positive() {
            Self::one()
        } else if self.negative() {
            -Self::one()
        } else {
            Self::zero()
        }
    }
    #[inline] default fn abs(self) -> Self { if self.negative() {-self} else {self} }
}

///
///The property that if `x < y`, there exists some natural `n` where `n*x = x*...*x > y`
///
///This is often interpreted as the structure having no "infinite" elements, since any element
///can be reached from any other non-zero element (even the smallest of elements) through _only_
///repeated addition.
///
///Now, it is worth noting that in practice, implementing structs _might_ still have some form
///of infinite elements, so long as they aren't "distinguished" in some way. In particular,
///IEEE floating points have INF, -INF, and NaN as standard values, all of which violate this property
///however, in order to simplify the API and still have [f32] and [f64] be considered [reals](crate::analysis::Real),
///these values are interpreted as errors. Of course, in general, new structs implementing this trait
///should avoid this if possible.
///
pub trait ArchimedeanProperty: AddOrdered + AddAssociative {}

///
///Division with remainder using an ordering and the Archimedean Property
///
///In a sense, this is extremely similar to [Euclidean division](EuclideanDiv) and in certain
///contexts (like the [Integers](Integer) and [Naturals](Natural)), this division satisfies the
///same relevant axioms. However, they are not _always_ equivalent, the real numbers being a notable
///exception.
///
pub trait ArchimedeanDiv: Sized + ArchimedeanProperty {

    ///
    ///Maps a natural number into this structure preserving addition and
    ///using the relevant canonical representation
    ///
    ///For rings and semirings with [One], this representation should make the [Natural] 1 to 1 in
    ///the structure and should also preserve multiplication
    ///
    fn embed_nat<N:Natural>(n:N) -> Self;

    ///the unique integer `n` such that `n*rhs <= self` and `(n+1)*rhs > self`
    fn div_arch(self, rhs: Self) -> Self;

    ///the remaining difference after dividing by rhs (ie. `self - self.div_arch(rhs)*rhs`)
    fn rem_arch(self, rhs: Self) -> Self;

    ///
    ///Divides `self` by `rhs` with remainder using the archimdean property
    ///
    ///Specifically, this function finds the unique Integer `n` and element `r` such that:
    /// * `self = n*rhs + r`
    /// * `n*rhs <= self`
    /// * `(n+1)*rhs > self`
    ///
    ///Note that the meaning of "Integer" here refers to the canonical representation/mapping
    ///of the Integers into this structure by nature of the [additive ordering](AddOrdered) on
    ///this structure and _not_ the integers themselves. As such, the quotient returned must
    ///be a possible output or [negation](Neg) a possibile output of
    ///[embed_nat()](ArchimedeanDiv::embed_nat).
    ///
    ///Furthermore, because the choice of quotient, the remainder returned must _always_ be non-negative.
    ///For this reason, for primitive types, this method corresponds to the div_euclid and
    ///rem_euclid methods and _not_ the `/` and `%` operators.
    ///
    fn div_alg_arch(self, rhs: Self) -> (Self, Self);
}

auto!{
    ///An additive magma with an ordered addition operation
    pub trait OrdMagma = AddMagma + AddOrdered;
    ///An additive semigroup with an ordered addition operation
    pub trait OrdSemigroup = OrdMagma + AddSemigroup;
    ///An additive loop with an ordered addition operation
    pub trait OrdLoop = OrdMagma + AddLoop;
    ///An additive monoid with an ordered addition operation
    pub trait OrdMonoid = OrdSemigroup + AddMonoid + Signed;
    ///An additive group with an ordered addition operation
    pub trait OrdGroup = OrdMonoid + AddGroup;
    ///An additive abelian group with an ordered addition operation
    pub trait OrdAbelianGroup = OrdGroup + AddAbelianGroup;

    ///A semiring with ordered addition and multiplication
    pub trait OrdSemiring = Semiring + OrdMonoid + MulOrdered;
    ///A unitial semiring with ordered addition and multiplication
    pub trait OrdUnitalSemiring = OrdSemiring + UnitalSemiring;
    ///A commutative semiring with ordered addition and multiplication
    pub trait OrdCommutativeSemiring = OrdUnitalSemiring + CommutativeSemiring;
    ///A division semiring with ordered addition and multiplication
    pub trait OrdDivisionSemiring = OrdUnitalSemiring + DivisionSemiring;

    ///A ring with ordered addition and multiplication
    pub trait OrdRing = Ring + OrdAbelianGroup + MulOrdered;
    ///A unital ring with ordered addition and multiplication
    pub trait OrdUnitalRing = OrdRing + UnitalRing + Sign;
    ///A commutative ring with ordered addition and multiplication
    pub trait OrdCommutativeRing = OrdUnitalRing + CommutativeRing;
    ///A division ring with ordered addition and multiplication
    pub trait OrdDivisionRing = OrdCommutativeRing + DivisionRing;

    ///A field with ordered addition and multiplication
    pub trait OrdField = OrdUnitalRing + Field;

    ///An ordered semigroup with the Archimedean property
    pub trait ArchSemigroup = OrdSemigroup + ArchimedeanProperty;
    ///An ordered monoid with the Archimedean property
    pub trait ArchMonoid = ArchSemigroup + OrdMonoid;
    ///An ordered group with the Archimedean property
    pub trait ArchGroup = ArchMonoid + OrdGroup;
    ///An ordered abeliean group with the Archimedean property
    pub trait ArchAbelianGroup = ArchMonoid + OrdAbelianGroup;

    ///An ordered semiring with the Archimedean property
    pub trait ArchSemiring = ArchMonoid + OrdSemiring;
    ///An ordered unital semiring with the Archimedean property and Archimedean division
    pub trait ArchUnitalSemiring = ArchSemiring + OrdUnitalSemiring + ArchimedeanDiv;
    ///An ordered commutative semiring with the Archimedean property and Archimedean division
    pub trait ArchCommutativeSemiring = ArchUnitalSemiring + OrdCommutativeSemiring;
    ///An ordered division semiring with the Archimedean property and Archimedean division
    pub trait ArchDivisionSemiring = ArchCommutativeSemiring + OrdDivisionSemiring;

    ///An ordered ring with the Archimedean property
    pub trait ArchRing = ArchAbelianGroup + OrdRing;
    ///An ordered unital ring with the Archimedean property and Archimedean division
    pub trait ArchUnitalRing = ArchRing + OrdUnitalRing + ArchimedeanDiv;
    ///An ordered commutative ring with the Archimedean property and Archimedean division
    pub trait ArchCommutativeRing = ArchUnitalRing + OrdCommutativeRing;
    ///An ordered division ring with the Archimedean property and Archimedean division
    pub trait ArchDivisionRing = ArchCommutativeRing + OrdDivisionRing;

    ///An ordered field ring with the Archimedean property and Archimedean division
    pub trait ArchField = ArchUnitalRing + OrdField;

}

macro_rules! impl_ordered_int {
    ($($t:ident)*) => {$(

        impl AddOrdered for $t {}
        impl MulOrdered for $t {}
        impl ArchimedeanProperty for $t {}

        impl Sign for $t {
            #[inline] fn signum(self) -> Self { $t::signum(self) }
            #[inline] fn abs(self) -> Self { self.abs() }
        }
        impl ArchimedeanDiv for $t {
            #[inline] fn embed_nat<N:Natural>(n:N) -> Self { (1).mul_n(n) }
            #[inline] fn div_arch(self, rhs:Self) -> Self {self.div_euclid(rhs)}
            #[inline] fn rem_arch(self, rhs:Self) -> Self {self.rem_euclid(rhs)}
            #[inline] fn div_alg_arch(self, rhs:Self) -> (Self, Self) {(self.div_arch(rhs), self.rem_arch(rhs))}
        }
    )*}
}

macro_rules! impl_ordered_uint {
    ($($t:ty)*) => {$(

        impl AddOrdered for $t {}
        impl MulOrdered for $t {}
        impl ArchimedeanProperty for $t {}

        impl ArchimedeanDiv for $t {
            #[inline] fn embed_nat<N:Natural>(n:N) -> Self { (1).mul_n(n) }
            #[inline] fn div_arch(self, rhs:Self) -> Self {self / rhs}
            #[inline] fn rem_arch(self, rhs:Self) -> Self {self % rhs}
            #[inline] fn div_alg_arch(self, rhs:Self) -> (Self, Self) {(self / rhs, self % rhs)}
        }
    )*}
}

macro_rules! impl_ordered_float {
    ($($t:ident)*) => {$(

        impl AddOrdered for $t {}
        impl MulOrdered for $t {}
        impl ArchimedeanProperty for $t {}

        impl Sign for $t {
            #[cfg(feature = "std")] #[inline] fn signum(self) -> Self { $t::signum(self) }
            #[cfg(feature = "std")] #[inline] fn abs(self) -> Self { self.abs() }
        }
        impl ArchimedeanDiv for $t {
            #[inline] fn embed_nat<N:Natural>(n:N) -> Self { (1.0).mul_n(n) }
            #[inline] fn rem_arch(self, rhs:Self) -> Self {
                let rem = self % rhs;
                if rem < 0.0 { rem + rhs.abs() } else { rem }
            }
            #[inline] fn div_arch(self, rhs:Self) -> Self { self.div_alg_arch(rhs).0 }
            #[inline] fn div_alg_arch(self, rhs:Self) -> (Self, Self) {
                let rem = self.rem_arch(rhs);
                ((self - rem) / self, rem)
            }
        }
    )*}
}

impl_ordered_int!(i8 i16 i32 i64 i128 isize);
impl_ordered_uint!(u8 u16 u32 u64 u128 usize);
impl_ordered_float!(f32 f64);
