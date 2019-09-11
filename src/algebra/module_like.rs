//!
//!Traits for structures with an addition and scalar multiplication operation
//!
//!# Implementation
//!
//!This module builds upon the and behaves in a way similar to the [group-like](crate::algebra::group_like)
//!structures, though, at this point in time, there are no additional properties or operations
//!for structs to consider when targeting this module's systems.
//!
//!# Usage
//!
//!Similarly to the [group-like](crate::algebra::group_like) module, there are a number of
//!trait aliases corresponding to a system of module-like algebraic structures that form a heirarchy
//!as represented in the following diagram:
//!
//!```text
//!        Affine Space    Additive Abelian Group
//!             |                   |
//!             |              Ring Module
//!             |                   |
//!             ----Vector Space-----
//!                      |
//!                   Algebra
//!```
//!
//!Where:
//! * A [ring-module](RingModule) is an [additive abelian group](AddAbelianGroup)
//!   with a scalar multiplication operation with elements from a particular [Ring]
//! * A [vector-space](VectorSpace) is a ring-module with scalars that form a field
//! * An [algebra](Algebra) is a vector-space with a distributive multiplication operation
//! * An [affine-space](AffineSpace) is a set with a subtraction operation producing a vector
//!     * <i>for more information see the trait-level documentation</i>
//!

pub use core::ops::{Add, AddAssign, Sub, SubAssign, Neg, Mul, MulAssign, Div, DivAssign, Index, IndexMut};
use crate::algebra::*;
use crate::analysis::{ComplexRing};

///
///A product between two vectors or module elements resulting in a scalar that is semi-linear in both arguments
///
///Rigorously, a σ-sesquilinear form is a mapping `•:M⨯M->R` from a Ring Module to its base ring such that:
/// * `(x+y)•z = x•z + y•z`
/// * `x•(y+z) = x•y + x•y`
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
/// * [ComplexSesquilinearForm]: `x•(c*y) = (x•y)*̅c`, ie `R ⊆ ℂ` and `σ(x) = ̅x` for all `x`
///     * If also a [SymSesquilinearForm], this implies `x•y = ̅y̅•̅x`
///     * If also a [SkewSesquilinearForm], this implies `x•y = -̅y̅•̅x`
///
/// # Examples
///
/// * Dot product of finite dimensional spaces and modules: `x•y = Σ(xₖ*yₖ)`
/// * Inner Product of real and complex vector spaces of any dimension
/// * Complex and Hyper-complex moduli: `z*̅w`
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
    ///The mapping on `R` that factors the second argument of the [sesquilinear form](SesquilinearForm::product_of)
    ///
    ///Specifically: a function `σ:R->R` such that:
    /// * `x•(c*y) = (x•y)*σ(c)`
    /// * `σ` is an anti-automorphism:
    ///     * `σ(a + b) = σ(a) + σ(b)`
    ///     * `σ(a*b) = σ(b)*σ(a)`
    ///     * `σ(a)!=σ(b)` whenever `a!=b`
    ///     * for all `a` in `R`, there is a `b` in `R` where `σ(b) = a`
    ///
    ///By default, this is just the identity operation, but common alternatives include negation
    ///and the complex conjugate
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
        let l = self.product_of(y, x.clone()) * self.square(x.clone()).inv();
        x * l
    }

}

///A [SesquilinearForm] where `x•y = 0` implies `y•x = 0`
pub trait ReflexiveForm<R:UnitalRing, M:RingModule<R>>: SesquilinearForm<R,M> {}

///
///A [SesquilinearForm] where `σ(x•y) = y•x`
///
///The is a property implemented on _most_ sesquilinear forms, but a notable exception is the
///the "Cross-Product" 2D vectors: `x₁*y₂ - x₂*y₁`
///
pub trait SymSesquilinearForm<R:UnitalRing, M:RingModule<R>>: ReflexiveForm<R,M> {}

///
///A [SesquilinearForm] where `σ(x•y) = -y•x`
///
///An example of which is the 2D "Cross-Product": `x₁*y₂ - x₂*y₁`
///
pub trait SkewSesquilinearForm<R:UnitalRing, M:RingModule<R>>: ReflexiveForm<R,M> {}

///A [SesquilinearForm] where `x•(c*y) = (x•y)*c` and `σ(x) = x`
pub trait BilinearForm<R:UnitalRing, M:RingModule<R>>: SesquilinearForm<R,M> {}

///A [BilinearForm] where `x•y = y•x`
pub trait SymmetricForm<R,M> = BilinearForm<R,M> + SymSesquilinearForm<R,M> where R:UnitalRing, M:RingModule<R>;

///A [BilinearForm] where `x•y = -y•x`
pub trait SkewSymmetricForm<R,M> = BilinearForm<R,M> + SkewSesquilinearForm<R,M> where R:UnitalRing, M:RingModule<R>;

///A [SesquilinearForm] where `x•(c*y) = (x•y)*̅c` and `σ(x) = ̅x`
pub trait ComplexSesquilinearForm<R:ComplexRing, M:RingModule<R>>: SesquilinearForm<R,M> {}

///A [ComplexSesquilinearForm] where `x•y = ̅y̅•̅x`
pub trait HermitianForm<R,M> = ComplexSesquilinearForm<R,M> + SymSesquilinearForm<R,M> where R:ComplexRing, M:RingModule<R>;

///A [ComplexSesquilinearForm] where `x•y = -̅y̅•̅x`
pub trait SkewHermitianForm<R,M> = ComplexSesquilinearForm<R,M> + SkewSesquilinearForm<R,M> where R:ComplexRing, M:RingModule<R>;


///An abelian additive group with a distributive scalar multiplication with a unital ring
pub trait RingModule<K: UnitalRing> = AddAbelianGroup + Mul<K, Output=Self> + MulAssign<K> + Distributive<K>;
///A ring module with a distributive multiplication operation
pub trait RingAlgebra<K: UnitalRing> = RingModule<K> + MulMagma + Distributive;
///A ring algebra with a multiplicative identity
pub trait UnitalRingAlgebra<K: UnitalRing> = RingAlgebra<K> + One;
///A ring algebra with an associative multiplication operation
pub trait AssociativeRingAlgebra<K: UnitalRing> = RingAlgebra<K> + MulAssociative;

///An abelian additive group with a distributive scalar multiplication with a field
pub trait VectorSpace<K: Field> = RingModule<K> + Div<K, Output=Self> + DivAssign<K>;
///A vector space with a distributive multiplication operation
pub trait Algebra<K: Field> = VectorSpace<K> + MulMagma + Distributive;
///An algebra with a multiplicative identity
pub trait UnitalAlgebra<K: Field> = Algebra<K> + One;
///An algebra with an associative multiplication operation
pub trait AssociativeAlgebra<K: Field> = Algebra<K> + MulAssociative;

///
///A set of points without an origin
///
///Rigorously, this is defined as a set `A` with a companion vector-space `V` and operations
///`-:AxA -> V` and `+:AxV -> A` such that:
/// * `x+0 = x`
/// * `(x+v)+w = x+(v+w)`
/// * `x+(y-x) = y`
/// * for all `x` in `A` and `v` in `V`, there exists a `y` in `A` where `x-y=v`
///
///In practice though, this can be thought of a collection of points with no distinguished origin.
///In fact, every affine space can be represented by a vector space by choosing a point as the origin.
///
///Examples include:
/// * Actual physical space: In physics, there is no notion of an absolute set of coordinates, but
///   we model displacements between them using 3D vectors
/// * Temporal measurements: In most contexts, there is no notion of an absolute time, so all times
///   are measured relative some other instant (such as 0CE or the beginning of the Unix epoch).
/// * Pointers: While not technically an affine-space because integer offsets don't have scalar multiplication,
///   pointers still carry the same sort of idea since you can subtract pointers to get integer offsets
///   and add offsets to pointers
///
pub trait AffineSpace<K: Field, V: VectorSpace<K>> = Sized + Clone +
    Sub<Self, Output=V> + Add<V, Output=Self> + Sub<V, Output=Self> +
    SubAssign<V> + AddAssign<V>;
