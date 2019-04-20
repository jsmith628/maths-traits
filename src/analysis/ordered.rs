
use algebra::*;

pub trait OrderedMonoid: PartialOrd + AddMonoid {
    #[inline] fn positive(&self) -> bool { self > &Self::zero() }
    #[inline] fn negative(&self) -> bool { self < &Self::zero() }

    #[inline] fn max(self, rhs: Self) -> Self { if self < rhs {rhs} else {self} }
    #[inline] fn min(self, rhs: Self) -> Self { if self < rhs {self} else {rhs} }
}

pub trait OrderedSemiring: OrderedMonoid + UnitalSemiring {
    fn signum(self) -> Self;
    fn abs(self) -> Self;
}

pub trait ArchimedianMonoid: OrderedMonoid {
    fn div_arch(self, rhs: Self) -> Self;
    fn rem_arch(self, rhs: Self) -> Self;
    fn div_alg_arch(self, rhs: Self) -> (Self, Self);
}

auto!{
    pub trait OrderedGroup = OrderedMonoid + AddGroup;
    pub trait OrderedRing = OrderedSemiring + Ring;
    pub trait OrderedField = OrderedRing + Field;

    pub trait ArchimedianGroup = ArchimedianMonoid + AddGroup;
    pub trait ArchimedianSemiring = ArchimedianMonoid + OrderedSemiring;
    pub trait ArchimedianRing = ArchimedianSemiring + Ring;
    pub trait ArchimedianField = ArchimedianRing + Field;
}

macro_rules! impl_ordered_int {
    ($($t:ident)*) => {$(
        impl OrderedMonoid for $t {
            #[inline] fn positive(&self) -> bool { *self > 0 }
            #[inline] fn negative(&self) -> bool { *self < 0 }
        }
        impl OrderedSemiring for $t {
            #[inline] fn signum(self) -> Self { $t::signum(self) }
            #[inline] fn abs(self) -> Self { self.abs() }
        }
        impl ArchimedianMonoid for $t {
            #[inline] fn div_arch(self, rhs:Self) -> Self {self / rhs}
            #[inline] fn rem_arch(self, rhs:Self) -> Self {self % rhs}
            #[inline] fn div_alg_arch(self, rhs:Self) -> (Self, Self) {(self / rhs, self % rhs)}
        }
    )*}
}

macro_rules! impl_ordered_uint {
    ($($t:ty)*) => {$(
        impl OrderedMonoid for $t {
            #[inline] fn positive(&self) -> bool { *self != 0 }
            #[inline] fn negative(&self) -> bool { false }
        }
        impl OrderedSemiring for $t {
            #[inline] fn signum(self) -> Self { if self==0 { 0 } else { 1 } }
            #[inline] fn abs(self) -> Self { self }
        }
        impl ArchimedianMonoid for $t {
            #[inline] fn div_arch(self, rhs:Self) -> Self {self / rhs}
            #[inline] fn rem_arch(self, rhs:Self) -> Self {self % rhs}
            #[inline] fn div_alg_arch(self, rhs:Self) -> (Self, Self) {(self / rhs, self % rhs)}
        }
    )*}
}

macro_rules! impl_ordered_float {
    ($($t:ident)*) => {$(
        impl OrderedMonoid for $t {
            #[inline] fn positive(&self) -> bool { *self > 0.0 }
            #[inline] fn negative(&self) -> bool { *self < 0.0 }
        }
        impl OrderedSemiring for $t {
            #[inline] fn signum(self) -> Self { $t::signum(self) }
            #[inline] fn abs(self) -> Self { self.abs() }
        }
        impl ArchimedianMonoid for $t {
            #[inline] fn div_arch(self, rhs:Self) -> Self {self / rhs - self % rhs}
            #[inline] fn rem_arch(self, rhs:Self) -> Self {self % rhs}
            #[inline] fn div_alg_arch(self, rhs:Self) -> (Self, Self) {(self.div_arch(rhs), self.rem_arch(rhs))}
        }
    )*}
}

impl_ordered_int!(i8 i16 i32 i64 i128 isize);
impl_ordered_uint!(u8 u16 u32 u64 u128 usize);
impl_ordered_float!(f32 f64);
