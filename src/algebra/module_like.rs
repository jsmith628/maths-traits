
pub use core::ops::{Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Div, DivAssign, Index, IndexMut};
use algebra::*;

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

pub trait ConvergentBasis<K>: Index<usize,Output=K> {fn basis(i:usize) -> Self;}
pub trait CountableBasis<K>: ConvergentBasis<K> + IndexMut<usize, Output=K> {fn elements(&self) -> usize;}
pub trait FiniteBasis<K>: CountableBasis<K> { fn dimensions() -> usize; }

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

    ///A ring module with a countable basis
    pub trait CountableModule<K> = RingModule<K> + CountableBasis<K> where K: UnitalRing;
    ///A vector space with a countable basis
    pub trait CountableVectorSpace<K> = VectorSpace<K> + CountableBasis<K> where K: Field;
    ///A ring module with a finite dimension
    pub trait FiniteModule<K> = RingModule<K> + FiniteBasis<K> where K: UnitalRing;
    ///A vector space with a finite dimension
    pub trait FiniteVectorSpace<K> = VectorSpace<K> + FiniteBasis<K> where K: Field;

    pub trait DotProductSpace<K> = DotProduct<K> + VectorSpace<K> where K: Field;
    pub trait ReflexiveSpace<K> = ReflexiveModule<K> + VectorSpace<K> where K: Field;
    pub trait SesquilinearSpace<K> = SesquilinearModule<K> + VectorSpace<K> where K: InvolutiveField;
    pub trait HermitianSpace<K> = HermitianModule<K> + VectorSpace<K> where K: InvolutiveField;
    pub trait SkewHermitianSpace<K> = SkewHermitianModule<K> + VectorSpace<K> where K: InvolutiveField;
    pub trait BilinearSpace<K> = BilinearModule<K> + VectorSpace<K> where K: Field;
    pub trait SymmetricSpace<K> = SymmetricModule<K> + VectorSpace<K> where K: Field;
    pub trait SkewSymmetricSpace<K> = SkewSymmetricModule<K> + VectorSpace<K> where K: Field;
}

macro_rules! impl_dot {
    ($($t:ident)*) => {
        $(
            impl DotProduct<$t> for $t {
                #[inline(always)] fn dot(self, rhs:Self) -> Self {self * rhs}
            }

            impl ReflexiveModule<$t> for $t {}
            impl SesquilinearModule<$t> for $t {}
            impl HermitianModule<$t> for $t {}
            impl BilinearModule<$t> for $t {}
            impl SymmetricModule<$t> for $t {}
        )*
    }
}

impl_dot!(i8 i16 i32 i64 isize i128 f32 f64);
