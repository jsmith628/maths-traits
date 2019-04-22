
use algebra::*;

pub trait AddOrdered {}
pub trait MulOrdered {}

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

impl<G: PartialOrd + Zero> Signed for G {
    #[inline] default fn positive(&self) -> bool { self > &Self::zero() }
    #[inline] default fn negative(&self) -> bool { self < &Self::zero() }
    #[inline] default fn non_negative(&self) -> bool { self >= &Self::zero() }
    #[inline] default fn non_positive(&self) -> bool { self <= &Self::zero() }
}

pub trait Sign: Signed + One + Neg<Output=Self> {
    fn signum(self) -> Self;
    fn abs(self) -> Self;
}

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

pub trait ArchimedeanProperty {}

pub trait ArchimedeanDiv: Sized + ArchimedeanProperty {
    fn embed_nat<N:Natural>(n:N) -> Self;
    fn div_arch(self, rhs: Self) -> Self;
    fn rem_arch(self, rhs: Self) -> Self;
    fn div_alg_arch(self, rhs: Self) -> (Self, Self);
}

auto!{
    pub trait OrdMagma = AddMagma + AddOrdered;
    pub trait OrdSemigroup = OrdMagma + AddSemigroup;
    pub trait OrdLoop = OrdMagma + AddLoop;
    pub trait OrdMonoid = OrdSemigroup + AddMonoid + Signed;
    pub trait OrdGroup = OrdMonoid + AddGroup;
    pub trait OrdAbelianGroup = OrdGroup + AddAbelianGroup;

    pub trait OrdSemiring = Semiring + OrdMonoid + MulOrdered;
    pub trait OrdUnitalSemiring = OrdSemiring + UnitalSemiring;
    pub trait OrdCommutativeSemiring = OrdUnitalSemiring + CommutativeSemiring;
    pub trait OrdDivisionSemiring = OrdUnitalSemiring + DivisionSemiring;

    pub trait OrdRing = Ring + OrdAbelianGroup + MulOrdered;
    pub trait OrdUnitalRing = OrdRing + UnitalRing + Sign;
    pub trait OrdCommutativeRing = OrdUnitalRing + CommutativeRing;
    pub trait OrdDivisionRing = OrdCommutativeRing + DivisionRing;

    pub trait OrdField = OrdUnitalRing + Field;

    pub trait ArchMagma = OrdMagma + ArchimedeanProperty;
    pub trait ArchSemigroup = ArchMagma + OrdSemigroup;
    pub trait ArchLoop = ArchMagma + OrdLoop;
    pub trait ArchMonoid = ArchSemigroup + OrdMonoid;
    pub trait ArchGroup = ArchMonoid + OrdGroup;
    pub trait ArchAbelianGroup = ArchMonoid + OrdAbelianGroup;

    pub trait ArchSemiring = ArchMonoid + OrdSemiring;
    pub trait ArchUnitalSemiring = ArchSemiring + OrdUnitalSemiring;
    pub trait ArchCommutativeSemiring = ArchUnitalSemiring + OrdCommutativeSemiring;
    pub trait ArchDivisionSemiring = ArchCommutativeSemiring + OrdDivisionSemiring;

    pub trait ArchRing = ArchAbelianGroup + OrdRing;
    pub trait ArchUnitalRing = ArchRing + OrdUnitalRing + ArchimedeanDiv;
    pub trait ArchCommutativeRing = ArchUnitalRing + OrdCommutativeRing;
    pub trait ArchDivisionRing = ArchCommutativeRing + OrdDivisionRing;

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
            #[inline] fn div_arch(self, rhs:Self) -> Self {self / rhs}
            #[inline] fn rem_arch(self, rhs:Self) -> Self {self % rhs}
            #[inline] fn div_alg_arch(self, rhs:Self) -> (Self, Self) {(self / rhs, self % rhs)}
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
            #[inline] fn signum(self) -> Self { $t::signum(self) }
            #[inline] fn abs(self) -> Self { self.abs() }
        }
        impl ArchimedeanDiv for $t {
            #[inline] fn embed_nat<N:Natural>(n:N) -> Self { (1.0).mul_n(n) }
            #[inline] fn div_arch(self, rhs:Self) -> Self {self / rhs - self % rhs}
            #[inline] fn rem_arch(self, rhs:Self) -> Self {self % rhs}
            #[inline] fn div_alg_arch(self, rhs:Self) -> (Self, Self) {(self.div_arch(rhs), self.rem_arch(rhs))}
        }
    )*}
}

impl_ordered_int!(i8 i16 i32 i64 i128 isize);
impl_ordered_uint!(u8 u16 u32 u64 u128 usize);
impl_ordered_float!(f32 f64);
