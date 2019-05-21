
pub use core::ops::{Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Div, DivAssign, Index, IndexMut};
use analysis::{ComplexRing};
use algebra::*;

///
///A product between two vectors or module elements resulting in a scalar that is semi-linear in both arguments
///
///Rigorously, a σ-sesquilinear form is a mapping `•:M⨯M->R` from a Ring Module to its base ring such that:
/// * `(x + y)•z = x•z + y•z`
/// * `x•(y + z) = x•y + x•y`
/// * `(c*x)•y = c*(x•y)`
/// * `x•(c*y) = (x•y)*σ(c)` where `σ:R->R` is some anti-automorphism, usually the complex conjugate
///   or the identity map
///
/// # Notes on Definition
///
///It is additionally worth emphasizing that in general, while there are a number of other properties
///commonly added to this list, none of them should be assumed without the addition of the appropriate
///marker trait. In particular:
/// * `x•(c*y)` may not equal `(x•y)*c`
/// * `x•y` may not equal `y•x`
/// * `x•y = 0` does not necessarily imply `y•x = 0`
///
///However, if these properties are desired, then the following additional traits can be implemented
///or used:
/// * [ReflexiveForm]: `x•y = 0` implies `y•x = 0`
///     * as a consequence, [Orthogonality](SesquilinearForm::orthogonal) becomes a reflexive property
/// * [SymSesquilinearForm]: `σ(x•y) = y•x`
/// * [SkewSesquilinearForm]: `σ(x•y) = -y•x`
/// * [BilinearForm]: `x•(c*y) = (x•y)*c`, ie, `σ(x) = x` for all `x`
///     * If also a [SymSesquilinearForm], this implies `x•y = y•x`
///     * If also a [SkewSesquilinearForm], this implies `x•y = -y•x`
/// * [ComplexSesquilinearForm]: `x•(c*y) = (x•y)*c̅`, ie `R ⊆ ℂ` and `σ(x) = x̅` for all `x`
///     * If also a [SymSesquilinearForm], this implies `x•y = conj(y•x)`
///     * If also a [SkewSesquilinearForm], this implies `x•y = -conj(y•x)`
///
/// # Examples
///
/// * Dot product of finite dimensional spaces and modules: `x•y = Σ(xₖ*yₖ)`
/// * Inner Product of real and complex vector spaces of any dimension
/// * Complex and Hyper-complex moduli: `z*w̅`
/// * The "Cross-Product" in 2D real-vector spaces: `x₁*y₂ - x₂*y₁`
///     * Alternatively, the mapping taking two vectors to the determinant of the matrix with
///      the vectors as its columns
/// * Minkowski metric: `ds² = dx² + dy² + dz² - dt²`
/// * Scalar product of the conformal model of Geometric algebra
///
pub trait SesquilinearForm<R:UnitalRing, M:RingModule<R>> {

    ///
    ///The function that applies the sesquilinear form
    ///
    ///Specifically, a mapping `•:M⨯M->R` such that
    /// * `(x + y)•z = x•z + y•z`
    /// * `x•(y + z) = x•y + x•y`
    /// * `(c*x)•y = c*(x•y)`
    /// * `x•(c*y) = (x•y)*σ(c)` where [`σ`](SesquilinearForm::sigma) is some anti-automorphism of `R`
    ///
    fn product_of(&self, v1:M, v2:M) -> R;

    ///
    ///The mapping on `R` that factors the second argument of the [sesquilinear form](SesquilinearForm::product)
    ///
    ///Specifically: a function `σ:R->R` such that:
    /// * `x•(c*y) = (x•y)*σ(c)`
    /// * `σ` is an anti-automorphism:
    ///     * `σ(a + b) = σ(a) + σ(b)`
    ///     * `σ(a*b) = σ(b)*σ(a)`
    ///     * `σ(a)!=σ(b)` whenever `a!=b`
    ///     * for all `a` in `R`, there is a `b` in `R` where `σ(b) = a`
    ///
    #[inline] fn sigma(&self, x:R) -> R {x}

    ///The inverse of the [`σ`](SesquilinearForm::sigma)
    #[inline] fn sigma_inv(&self, x:R) -> R {x}

    ///An alias for `x•x`
    #[inline] fn square(&self, x:M) -> R {self.product_of(x.clone(),x)}

    ///Returns true if `x•x = 0`
    #[inline] fn is_null(&self, x:M) -> bool {self.square(x).is_zero()}

    ///
    ///Returns true if `x•y = 0`
    ///
    ///Note that this may not imply that `y` is orthogonal to `x`, unless the product is also a
    ///[ReflexiveForm]
    ///
    #[inline] fn orthogonal(&self, x:M, y:M) -> bool {self.product_of(x, y).is_zero()}

    ///
    ///The orthogonal component of `y` with respect to `x`, assuming x is not [null](SesquilinearForm::is_null)
    ///
    ///Specifically, this a vector or element `v` such that:
    /// * `v•x = 0`
    /// * `y-v = c*x` for some `c` in `R`
    ///
    ///Most of the time, this can be computed simply by subtracting the [parallel component](SesquilinearForm::par_comp)
    ///from `y`
    ///
    ///Do note however, that if `x` is a [null-element](SesquilinearForm::is_null) (ie. `x•x = 0`),
    ///then such a vector does not exist and this function may `panic!`
    ///
    #[inline] fn orth_comp(&self, x:M, y: M) -> M where R:DivisionRing { y.clone() - self.par_comp(x,y) }

    ///
    ///The parallel component of `y` with respect to `x`, assuming x is not [null](SesquilinearForm::is_null)
    ///
    ///Specifically, this a vector or element `w` such that:
    /// * `w = c*x` for some `c` in `R`
    /// * `(y-w)•x = 0`
    ///
    ///This can usually be computed simply with the formula `w = x*(y•x)*((x•x)⁻¹)`
    ///
    ///Do note however, that if `x` is a [null-element](SesquilinearForm::is_null) (ie. `x•x = 0`),
    ///then such a vector does not exist and this function may `panic!`
    ///
    #[inline] fn par_comp(&self, x:M, y: M) -> M where R:DivisionRing {
        let l = self.product(y, x.clone()) * self.square(x.clone()).inv();
        x * l
    }

}

pub trait ReflexiveForm<R:UnitalRing, M:RingModule<R>>: SesquilinearForm<R,M> {}
pub trait SymSesquilinearForm<R:UnitalRing, M:RingModule<R>>: ReflexiveForm<R,M> {}
pub trait SkewSesquilinearForm<R:UnitalRing, M:RingModule<R>>: ReflexiveForm<R,M> {}

pub trait BilinearForm<R:UnitalRing, M:RingModule<R>>: SesquilinearForm<R,M> {}
pub trait ComplexSesquilinearForm<R:ComplexRing, M:RingModule<R>>: SesquilinearForm<R,M> {}

auto! {
    pub trait SymmetricForm<R,M> = BilinearForm<R,M> + SymSesquilinearForm<R,M> where R:UnitalRing, M:RingModule<R>;
    pub trait SkewSymmetricForm<R,M> = BilinearForm<R,M> + SkewSesquilinearForm<R,M> where R:UnitalRing, M:RingModule<R>;
    pub trait HermitianForm<R,M> = ComplexSesquilinearForm<R,M> + SymSesquilinearForm<R,M> where R:ComplexRing, M:RingModule<R>;
    pub trait SkewHermitianForm<R,M> = ComplexSesquilinearForm<R,M> + SkewSesquilinearForm<R,M> where R:ComplexRing, M:RingModule<R>;
}

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

}
