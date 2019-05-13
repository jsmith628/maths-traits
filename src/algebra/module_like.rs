
pub use core::ops::{Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Div, DivAssign, Index, IndexMut};
use algebra::*;

///
///A product between two vectors or module elements resulting in a scalar that is semi-linear in both arguments
///
///Rigorously, the dot product is a mapping `•:M⨯M->R` from a Ring Module to its base ring such that:
/// * `(x + y)•z = x•z + y•z`
/// * `x•(y + z) = x•y + x•y`
/// * `(c*x)•y = c*(x•y)`
/// * `x•(c*y) = (x•y)*σ(c)` where `σ:R->R` is some anti-automorphism, usually the complex conjugate
///   or the identity map
///
/// # Notes on definition
///
///In pursuit of generality, the definition used here is noticeably less strict than the more commonly
///dot product definition. Of course, the normal dot product is covered by this definition, but in order to
///capture a number of other important mathematical operations, some properties have been relaxed
///for greater abstraction. In particular:
/// * `x•y` might not equal `y•x`
/// * `x•(c*y)` does not necessarily equal `c*(x•y)` or even `(x•y)*c` in general
/// * `x•x` can equal 0
/// * `x•x` can be negative or non-real
///
///However, in exchange, this trait can represent the following in addition to the real inner product:
/// * The complex and hypercomplex inner products, which have `x•(c*y) = conj(c)*(x•y)`
/// * The Minkowski space-time interval, which requires the time-basis to square to -1
/// * The 2D cross product: `[x₁,y₁]•[x₂,y₂] = x₁*y₂ - x₂*y₁` which requires non-symmetry
/// * Conformal Models of Geometric Algebra, which require vector bases that square to 0
///
/// # Additional properties
///
///In addition to the base properties, the dot product can have a number of additional restrictions
///signified here by added the corresponding marker trait:
/// * A [Reflexive Form](ReflexiveModule) requires that `x•y = 0` implies `y•x = 0`
/// * If M and R have an involution `'`,
///     * A [Sesquilinear Form](SesquilinearModule) requires `x•(c*y) = c'*(x•y)`
///     * A [Hermitian Form](HermitianModule) requires `(x•y)' = y'•x'`
///     * A [Skew-Hermitian Form](HermitianModule) requires `(x•y)' = -y'•x'`
/// * A [Bilinear Form](ReflexiveModule) requires that `x•(c*y) = (x•y)*c`
/// * A [Symmetric Form](ReflexiveModule) requires that `x•y = y•x`
/// * A [Skew-Symmetric Form](ReflexiveModule) requires that `x•y = -y•x`
///
///
pub trait DotProduct<K: UnitalRing>: RingModule<K> {
    fn dot(self, rhs: Self) -> K;
    #[inline] fn squared(self) -> K {self.clone().dot(self)}

    #[inline] fn orthogonal(self, rhs: Self) -> bool {self.dot(rhs).is_zero()}
    #[inline] fn reject(self, rhs: Self) -> Self where K:DivisionRing { rhs.clone() - self.project(rhs) }
    #[inline] fn project(self, rhs: Self) -> Self where K:DivisionRing {
        let l = self.clone().squared().inv() * self.clone().dot(rhs);
        self * l
    }
}

pub trait ReflexiveModule<K: UnitalRing>: DotProduct<K> {}

pub trait SesquilinearModule<K: InvolutiveUnitalRing>: DotProduct<K> + Involution {}
pub trait HermitianModule<K: InvolutiveUnitalRing>: ReflexiveModule<K> + SesquilinearModule<K> {}
pub trait SkewHermitianModule<K: InvolutiveUnitalRing>: ReflexiveModule<K> + SesquilinearModule<K> {}

pub trait BilinearModule<K: UnitalRing>: DotProduct<K> {}
pub trait SymmetricModule<K: UnitalRing>: ReflexiveModule<K> + BilinearModule<K> {}
pub trait SkewSymmetricModule<K: UnitalRing>: ReflexiveModule<K> + BilinearModule<K> {}

auto!{
    ///An abelian additive group with a distributive scalar multiplication with a unital ring
    pub trait RingModule<K> = AddAbelianGroup + Mul<K, Output=Self> + MulAssign<K> where K: UnitalRing;
    ///An abelian additive group with a distributive scalar multiplication with a field
    pub trait VectorSpace<K> = RingModule<K> + Div<K, Output=Self> + DivAssign<K> where K: Field;
    ///A vector space with a distributive multiplication operation
    pub trait Algebra<K> = VectorSpace<K> + MulMagma + Distributive where K: Field;

    pub trait AffineSpace<K, V> =
        Sized + Clone + Sub<Self, Output=V> + Add<V, Output=Self> + AddAssign<V> + Sub<V, Output=Self> + SubAssign<V>
        where K: Field, V: VectorSpace<K>;

    pub trait DotProductSpace<K> = DotProduct<K> + VectorSpace<K> where K: Field;
    pub trait ReflexiveSpace<K> = ReflexiveModule<K> + VectorSpace<K> where K: Field;
    pub trait SesquilinearSpace<K> = SesquilinearModule<K> + VectorSpace<K> where K: InvolutiveField;
    pub trait HermitianSpace<K> = HermitianModule<K> + VectorSpace<K> where K: InvolutiveField;
    pub trait SkewHermitianSpace<K> = SkewHermitianModule<K> + VectorSpace<K> where K: InvolutiveField;
    pub trait BilinearSpace<K> = BilinearModule<K> + VectorSpace<K> where K: Field;
    pub trait SymmetricSpace<K> = SymmetricModule<K> + VectorSpace<K> where K: Field;
    pub trait SkewSymmetricSpace<K> = SkewSymmetricModule<K> + VectorSpace<K> where K: Field;
}


macro_rules! impl_forms {
    ($($t:ident)*) => {
        $(
            impl ReflexiveModule<$t> for $t {}
            impl SesquilinearModule<$t> for $t {}
            impl HermitianModule<$t> for $t {}
            impl BilinearModule<$t> for $t {}
            impl SymmetricModule<$t> for $t {}
        )*
    }
}

macro_rules! impl_dot_int {
    ($($t:ident)*) => {
        $(
            impl DotProduct<$t> for $t {
                #[inline(always)] fn dot(self, rhs:Self) -> Self {self * rhs}
                #[inline(always)] fn orthogonal(self, rhs: Self) -> bool {self.is_zero() || rhs.is_zero()}
            }
            impl_forms!($t);
        )*
    }
}

macro_rules! impl_dot_float {
    ($($t:ident)*) => {
        $(
            impl DotProduct<$t> for $t {
                #[inline(always)] fn dot(self, rhs:Self) -> Self {self * rhs}
                #[inline(always)] fn orthogonal(self, rhs: Self) -> bool {self.is_zero() || rhs.is_zero()}
                #[inline(always)] fn reject(self, rhs: Self) -> Self { if self==0.0 {rhs} else {0.0} }
                #[inline(always)] fn project(self, rhs: Self) -> Self { if self==0.0 {0.0} else {rhs} }
            }
            impl_forms!($t);
        )*
    }
}

impl_dot_int!(i8 i16 i32 i64 isize i128);
impl_dot_float!(f32 f64);
