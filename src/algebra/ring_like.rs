//!
//!Traits for structures with both an addition and multiplication operation
//!
//!While ring-like structures can technically apply to any pair of operations, for ease of use
//!and to stick with mathematical convention, these operations are taken to be specifically addition
//!and multiplication where multiplication distributes over addition.
//!
//!# Implementation
//!
//!This module behaves in a way similar to the [group-like](crate::algebra::group_like) structures and,
//!in fact, builds upon it such that the ring-like trait aliases use the properties present in that
//!module. However, in addition to the basic group traits, the following properties are also considered:
//! * Distributivity:
//!    * Multiplication can act on summed elements independently,
//!      ie`z*(x+y)=z*x+z*y` and `(x+y)*z=x*z+y*z` for all `x`, `y`, and `z`.
//!    * Represented by the [`Distributive`] trait
//!    * Note that unlike other marker traits, this one takes a type parameter so that
//!      multiplication between types can also be marked
//!      (such as scalar-vector or matrix-vector multiplication)
//! * The Exponentiation and Logarthm operations:
//!    * Unary operations that map between addition and multiplication
//!    * Represented with the [`Exponential`] trait
//! * Properties regarding partial divisibility and factoring
//!    * These traits _essentially_ measure how "integer-like" a particular ring is by abstracting
//!      many properties and operations commonly associated with integers and natural numbers
//!    * These include, but are not limited to:
//!        * [Divisibility]
//!        * [Primality]
//!        * [GCD]
//!        * [Euclidean Division](EuclideanDiv)
//!        * [Factorizability](Factorizable)
//!    * For more information, see each individual trait's documentation
//!
//!# Usage
//!
//!Similarly to the [group-like](crate::algebra::group_like) module, there are a number of
//!trait aliases corresponding to a system of ring-like algebraic structures that form a heirarchy
//!as represented in the following diagram:
//!
//!```text
//!
//!    Add Abelian Group   Mul Semigroup
//!           |                 |
//!           -------Ring--------
//!                    |
//!    ----------Unital Ring-------------------------
//!    |                    |             |         |
//!    |             Commutative Ring   Domain      |
//!    |                    |             |         |
//!    |                    ---------------         |
//!    |                           |                |
//!    |                     Integral Domain        |
//!    |                           |                |
//!Division Ring            ---GCD Domain---        |
//!    |                    |              |        |
//!    |                   UFD       Bezout Domain  |
//!    |                    |              |        |
//!    |                    ------PID-------        |
//!    |                           |                |
//!    |                    Euclidean Domain        |
//!    |                           |                |
//!    -------------Field-----------         Exponential Ring
//!                   |                             |
//!                   ------Exponential Field--------
//!
//!```
//!
//!Note also that in addition to the above system, there is a complementary system of "Semirings"
//!that follows almost the same exact structure but doesn't require a subtraction operation
//!
//!# Naming
//!
//!It is worth noting that in mathematical literature, there is some leniency in what certain
//!structures are called, so some trait aliases may be named differently than what some are used to.
//!
//!In particular:
//! * Some mathematicians and literature use the term "Ring" to refer to what is called a "Unital Ring"
//!   here, instead preferring the term "Rng" for Rings without a multiplicative identity. In fact,
//!   this convention is _probably_ the majority considering how little use there is for non-unital rings.
//!   However, the choice was made against using the "Rng" system for the simple reason that it is
//!   obviously highly prone to typesetting errors and is arguably pretty unintuitive for those learning
//!   the terminology.
//! * The term "Semiring" doesn't really have an established meaning in mathematical convention, so
//!   the use here reflects a particular design choice more than a particular standard.
//!

use crate::algebra::*;
use core::iter::Iterator;

///A marker trait for stucts whose multiplication operation preserves addition,
///ie `z*(x+y)=z*x+z*y` and `(x+y)*z=x*z+y*z` for all `x`, `y`, and `z`.
pub trait Distributive<T=Self> {}

///
///Common methods regarding multiplicative inverses in a ring or semiring
///
///Do note that while for some rings these methods are relatively quick (like the integers),
///for others, such as polynomials, this test might actually be relatively expensive
pub trait Divisibility: Sized {
    ///Determines if there exists an element `x` such that `self*x` = `rhs`
    fn divides(self, rhs: Self) -> bool;

    ///Finds an element `x` such that `self*x` = `rhs` if such an element exists
    fn divide(self, rhs: Self) -> Option<Self>;

    ///Determines if this element has a multiplicative inverse
    fn unit(&self) -> bool;

    ///Finds this element's multiplicative inverse if it exists
    fn inverse(self) -> Option<Self>;
}

///
///Methods for testing irreduciblity and primality
///
///Do note that for obvious reasons these methods should be assumed to be expensive by default.
///Furthermore, given the difficulty of checking irreduciblity or primality for general rings,
///it is entirely possible that there is simply no good algorithm for doing so, and as such, this
///trait is _not_ a requirement for any of the ring categorization traits.
///
///Furthermore, it is important to note that in general, while all primes are irreducible,
///the notions are **not** synonymous. In particular, in Z[sqrt(5)], 3 is irreducible
///but is not prime. However, if all pairs of elements have a [GCD],
///then all irreducibles are prime as well.
pub trait Primality: Divisibility {

    ///Determines if this element cannot be produced from the product of two other non-invertible elements
    fn irreducible(&self) -> bool;

    ///
    ///Determines if this element is prime
    ///
    ///An element `x` is prime if when `y` is a multiple of `x`, `a*b=y` implies that `x` divides
    ///_either_ `a` _or_ `b`. Do note that this implies irreduciblity.
    ///
    fn prime(&self) -> bool;
}

///
///A marker trait for [semirings](Semiring) where there are no nonzero elements that multiply to zero
///
///ie. for all `x` and `y` where `x!=0` and `y!=0`, `x*y!=0`
///
pub trait NoZeroDivisors {}

///A trait for finding the greatest common divisor and least common multiple of two elements
pub trait GCD: Sized {
    ///
    ///Finds the greatest common divisor of two elements
    ///
    ///An element `d` is a GCD of `x` and `y` if for all `z` where `z` divides both `x` and `y`,
    ///`z` also divides `d`.
    ///
    ///Do note that this element will often not be _entirely_ unique. However, it _is_ the case that
    ///any two GCDs in a [GCDDomain] will always differ by only multiplication by an invertible element.
    ///For example, while _both_ -4 and 4 are GCDs of 12 and 8 (as Integers), -4 can be
    ///transformed into 4 and vice versa by multiplying by -1
    ///
    fn gcd(self, rhs: Self) -> Self;

    ///
    ///Finds the least common multiple of two elements
    ///
    ///An element `m` is a LCM of `x` and `y` if for all `z` where `x` and `y` both divide `z`,
    ///`m` also divides `z`. This element is also not always unique in the same way as the gcd.
    ///
    ///Additionally, the GCD and LCM can always be computed from each other
    ///by LCM(x,y) = (x*y)/GCD(x,y), so the existence of one always implies the existence of
    ///the other
    ///
    fn lcm(self, rhs: Self) -> Self;
}

///A trait for finding the Bezout coefficients of a pair of elements
pub trait Bezout: GCD {

    ///
    ///Bezout coefficients of a pair of elements
    ///
    ///The Bezout coefficients for `x` and `y` are a pair of elements `a` and `b` such that
    ///`a*x + b*y = GCD(x,y)`. Note that like with the [GCD], these are only unique up to units.
    ///However, the coefficients returned by this function must satisfy the defining identity for
    ///the _particular_ GCD as returned by [GCD::gcd()]
    ///
    #[inline]
    fn bezout_coefficients(self, rhs: Self) -> (Self, Self) {
        let (a,b,_) = self.bezout_with_gcd(rhs);
        (a,b)
    }

    ///
    ///Computes the [GCD](GCD::gcd()) and the [bezout coefficients](Bezout::bezout_coefficients)
    ///in one function call
    ///
    fn bezout_with_gcd(self, rhs: Self) -> (Self, Self, Self);
}

///
///A marker trait for [semirings](Semiring) where each element's set of irreducible divisors is unique
///
///Note that this trait is independent of [`Factorizable`] and doesn't contain its own
///`factors()` method since there are a number of notable examples of rings
///where unique factorization is provable, but no known algorithm to find the factors is known.
///This is the case for integer polynomials for example.
///
pub trait UniquelyFactorizable: Sized {}

///
///For [semirings](Semiring) that have a _known_ algorithm for decomposing elements into a set
///of irreducible factors
///
///# Notes on "Irreduciblity"
///
///An irreducible factor as defined here is any element that cannot be written as a product of two
///or more non-invertible elements. Note that this is technically, but not usually, different than
///a "prime" element. For more information, see [`Divisibility`].
///
///# Uniqueness and Ordering
///
///This trait on its own makes **no guarantees** that the returned factors are unique or ordered
/// in **any** way. The only requirements are that:
///* The product of the factors must be the original number
///* No factors of `1` are included
///* `0` returns `[0]`
///* Only *one* invertible element can be included and must be the first factor
///    * For example, `-6` might return `[-1, 2, 3]` or `[-1, 3, 2]`, but not `[2, -1, 3]`
///
///Importantly, this means does that some structures **can** return different sets of factors
///at different times. For example, in ℤ[√5], `6 = 2*3 = (1+√5)*(1-√5)` are both valid irreducible
///factorizations.
///
///_However_, if the [`UniquelyFactorizable`] trait is _also_ implemented, this is restricted somewhat,
///but only up to ordering and units.
///
///In particular, given two lists of factors for an element:
///* There is still no guaranteed ordering, so the lists could be permuted somehow
///* Some factors in the second might be multiplied by some invertible element from the first
///  or return an extra invertible element in the list.
///     * For instance, `-10` might return `[-5, 2]` or `[5,-2]` or `[2,-5]` or even `[-1,5,2]`
///
///Furthermore, there is no requirement for any sort of ordering, as the wide range of possible
///implementing structures gives no obvious standard as to what that would be.
///
///_However_, implementors are highly encouraged to guarantee some sort of ordering and uniqueness
///themselves using their particular properties. For instance, the implementation on the primitive integers
///return all non-negative factors in order of increasing absolute magnitude with a `-1` at the beginning
///for negative numbers, or a polynomial could factor as monic polynomials of increasing degree.
///
pub trait Factorizable: Sized {
    type Factors: Iterator<Item=Self>;
    fn factors(self) -> Self::Factors;
}

///A trait for performing division with with remainder
pub trait EuclideanDiv: Sized {
    ///The specific type used for the Euclidean Norm
    type Naturals: Natural;

    ///
    ///A measure of the "degree" of a given element.
    ///
    ///This function must satisfy the following restrictions:
    /// * `a.euclid_norm() <= (a*b).euclid_norm()` for all `a`,`b`
    /// * for `(q,r) = div_alg()`, `r.euclid_norm() < q.euclid_norm()`
    ///
    ///Beyond these, there are no other restrictions. In particular, the Euclidean Norm need not be unique.
    ///For example, the Euclidean norm of a polynomial is usually taken as the non-unique degree.
    ///
    fn euclid_norm(&self) -> Self::Naturals;

    ///The quotient from [Euclidean division](EuclideanDiv::div_alg)
    fn div_euc(self, rhs: Self) -> Self;

    ///The remainder from the [Euclidean division](EuclideanDiv::div_alg)
    fn rem_euc(self, rhs: Self) -> Self;

    ///
    ///Divides a pair of elements with remainder
    ///
    ///Given inputs `a` and `b`, this produces a quotient-remainder pair `(q,r)` such that:
    /// * `a = q*b + r`
    /// * `r.euclid_norm() < q.euclid_norm()`
    ///
    ///Do note that in general, this result is **not** unique, the most striking example
    ///simply being the Integers, for which **every** division with a remainder has the choice
    ///of a positive or negative remainder. (Take `13 = 4*3 + 1 = 5*3 - 2` for example) Furthermore,
    ///other rings, like the Guassian Integers, can have even more options, and others, like polynomials,
    ///can have _infinite_ possible options.
    ///
    ///As such, it is up to the implementor to decide what the canonical form of this result is
    ///and to communicate it as such, and this trait makes no guarantees that this has happened
    ///
    fn div_alg(self, rhs: Self) -> (Self, Self);
}

///
///A unary operation mapping addition into multiplication
///
///Rigourously, and exponential operation is a mapping `E:R->R` such that:
/// * `E(x+y) = E(x)*E(y)` whenever `x*y = y*x`
/// * `E(x) != 0`
///
///In addition to these base properties, this trait also stipulates that this function _not_ map
///every element to 1, so as to rule out the trivial case.
///
///Furthmore, to clear up ambiguity, it is important to note that different variations on this
///definition exists. For instance:
/// * As already mentioned, some may allow the mapping to be non-trivial
/// * Some may also allow `E(x) = 0`
/// * For the [Real](crate::analysis::Real) and [Complex](crate::analysis::Complex) exponentials,
///   there are a [multitude][1] of equivalent definitions that have no true effect on the mapping
///
///More importantly though, most authors specify that the `E(x+y) = E(x)*E(y)` for _all_ `x` and `y`
///(such as on [Wikipedia][2])
///However, doing so disallows both the Matrix exponential and Quaternion exponential as well
///as the Clifford Algebra exponential, all of which are, frankly, the only reason to make the exponential
///its own separate trait.
///
/// # Effects on Ring structure
///
///It is worth noting that _any_ ring that has a non-trivial exponential operation must automatically
///have a characteristic of 0 (that is, `1+1+1+...+1` will never equal zero) and hence, has an
///embedding of the Integers within it.
///
///This fact is easily proven as follows:
/// * assume `char(R) = n != 0`
/// * then, for any `x` in `R`, `nx = x+...+x = 0`, and,
///   the [Frobenious automorphism][3] gives that `(x+y)ⁿ = xⁿ + yⁿ`
/// * Hence, `(E(x) - 1)ⁿ = E(x)ⁿ - 1 = E(nx) - 1 = E(0) - 1 = 0`
/// * Thus, we have that that `E(x) = 1` contradicting our assumtions
///
///Additionally, any element that is the output of the expoenential _must_ be an invertible element,
///since <br> `1 = E(0) = E(x-x) = E(x)*E(-x)` implying `E(x) = E(x)⁻¹`
///
/// # Uniqueness
///
///In general, this characterization of the exponential function is *not* unique. However, in the
///vast majority of cases, there is a canonical version that all others derive from _or_ there is only
///one non-trivial case.
///
///For example, most real-algebras have infinitely many exponentials, but we get a canonical form
///stipulating that the function satisfy the classic differential equation `E'(x) = E(x)` or some
///variant.
///
/// [1]: https://en.wikipedia.org/wiki/Characterizations_of_the_exponential_function
/// [2]: https://en.wikipedia.org/wiki/Exponential_field
/// [3]: https://en.wikipedia.org/wiki/Frobenius_endomorphism
///
pub trait Exponential: Sized {
    ///
    ///The exponential of this ring element
    ///
    ///Here, `exp(x)` is defined such that:
    /// * `exp(x+y) = exp(x)*exp(y)` for all `x` and `y` where `x*y=y*x`
    /// * `exp(x) != 0`
    /// * `exp(x)` is continuous (if applicable)
    /// * `d/dx exp(x)|ₓ₌₁ = 1` (if applicable)
    ///
    ///For most structures, this function is equivalent to the infinite series Σ x<sup>n</sup>/n!
    ///
    fn exp(self) -> Self;

    ///
    ///An inverse of [exp(x)](Exponential::exp) where `ln(1) = 0`
    ///
    ///This returns a `None` value whenever the inverse does not exist for the given input.
    ///
    /// ## Uniqueness and Continuity
    ///
    ///Do note, however, that for almost all non-[Real](crate::analysis::Real) structures, this function
    ///is not unique and can **never** be continuous. Of course, some of this ambiguity is resolved by
    ///stipulating that `ln(1) = 0`, but even so, some remains,
    ///and so, it is entirely up to the implementor to any specific canonical form if applicable.
    ///
    ///For example, the [Complex](crate::analysis::Complex) numbers, the natural logarithm *must* be discontinuous somewhere,
    ///and there are infinitely many choices as to where that is. However, usually, this ambiguity
    ///is removed by taking the imaginary component of the result between -π and π and setting
    ///the discontinuity to be on the negative real axis
    ///
    fn try_ln(self) -> Option<Self>;
}

///A commutative and additive monoid with a distributive and associative multiplication operation
pub trait Semiring = Distributive + AddMonoid + AddCommutative + MulSemigroup;
///A semiring with an identity element
pub trait UnitalSemiring = Semiring + MulMonoid;
///A unital semiring where multiplication is commutative
pub trait CommutativeSemiring = UnitalSemiring + MulCommutative;
///A semiring with a multiplicative inverse
pub trait DivisionSemiring = UnitalSemiring + MulGroup;

///An additive abelian group with a distributive and associative multiplication operation
pub trait Ring = Distributive + AddAbelianGroup + MulSemigroup;
///A ring with an identity element
pub trait UnitalRing = Ring + MulMonoid;
///A unital ring where multiplication is commutative
pub trait CommutativeRing = UnitalRing + MulCommutative;
///A ring with a multiplicative inverse
pub trait DivisionRing = UnitalRing + MulGroup;
///A ring with an exponential operation
pub trait ExponentialRing = UnitalRing + Exponential;

///A unital semiring with no pairs of nonzero elements that multiply to zero
pub trait Semidomain = UnitalSemiring + Divisibility + NoZeroDivisors;
///A semidomain that is commutative
pub trait IntegralSemidomain = Semidomain + MulCommutative;
///An integral semidomain where every pair of elements has a greatest common divisor
pub trait GCDSemidomain = IntegralSemidomain + GCD;
///A GCD semidomain where every pair of elements is uniquely factorizable into irreducible elements (up to units)
pub trait UFSemidomain = GCDSemidomain + UniquelyFactorizable;
///A UF semidomain with a division algorithm for dividing with a remainder
pub trait EuclideanSemidomain = UFSemidomain + EuclideanDiv;

///A unital ring with no pairs of nonzero elements that multiply to zero
pub trait Domain = UnitalRing + Divisibility + NoZeroDivisors;
///A domain that is commutative
pub trait IntegralDomain = Domain + MulCommutative;
///A commutative ring where every pair of elements has a greatest common divisor
pub trait GCDDomain = IntegralDomain + GCD;
///A commutative ring where every pair of elements has a weighted sum to their GCD
pub trait BezoutDomain = GCDDomain + Bezout;
///A commutative ring that is uniquely factorizable into irreducible (up to units)
pub trait UFD = GCDDomain + UniquelyFactorizable;
///
///An integral domain where every ideal is generated by one element
///
///ie. a UFD that is Bezout
///
pub trait PID = UFD + BezoutDomain;
///A commutative ring with a division algorithm for dividing with a remainder
pub trait EuclideanDomain = PID + EuclideanDiv;

///A set that is both an additive and multiplicative abelian group where multiplication distributes
pub trait Field = CommutativeRing + MulGroup;
///A field with an exponential operation
pub trait ExponentialField = Field + Exponential;

//
//Implementation for primitives
//

macro_rules! impl_dist {
    ($($t:ty)*) => {
        $(
            impl Distributive for $t{}
            impl Distributive for ::core::num::Wrapping<$t>{}
        )*
    };
}
impl_dist!(usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64);

macro_rules! impl_for_field {
    ($($t:ty)*) => {
        $(
            impl Divisibility for $t {
                #[inline(always)] fn divides(self, _rhs: Self) -> bool {true}
                #[inline(always)] fn divide(self, rhs: Self) -> Option<Self> {Some(rhs / self)}
                #[inline(always)] fn unit(&self) -> bool {true}
                #[inline(always)] fn inverse(self) -> Option<Self> {Some(self.inv())}
            }

            impl NoZeroDivisors for $t {}
            impl UniquelyFactorizable for $t {}

        )*
    }
}

impl_for_field!(f32 f64);

///Uses the [Euclidean Algorithm](https://en.wikipedia.org/wiki/Euclidean_algorithm)
///to find the [GCD] of two ring elements using [division with remainder](EuclideanDiv)
pub fn euclidean<T>(lhs: T, rhs: T) -> T where T:CommutativeSemiring+EuclideanDiv {

    fn euclid<U>(a: U, b: U) -> U where U:CommutativeSemiring+EuclideanDiv
    {
        let r = a.rem_euc(b.clone());
        if r.is_zero() {
            b
        }else{
            euclid(b, r)
        }
    }

    if lhs.is_zero() || rhs.is_zero() {return T::zero()}

    if lhs.euclid_norm() >= rhs.euclid_norm() {
        euclid(lhs, rhs)
    } else {
        euclid(rhs, lhs)
    }

}

///
///Uses the [Extended Euclidean Algorithm](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm)
///to find the [GCD] of two ring elements _and_ their [bezout coefficients](Bezout) using
///[division with remainder](EuclideanDiv)
///
pub fn extended_euclidean<T>(lhs: T, rhs: T) -> (T, T, T) where T:CommutativeRing+EuclideanDiv {

    fn euclid<U>(a: U, b: U) -> (U, U, U) where U:CommutativeRing+EuclideanDiv
    {
        let (q, r) = a.div_alg(b.clone());
        if r.is_zero() {
            (U::zero(), U::one(), b)
        }else{
            let (x1, y1, g) = euclid(b, r);
            (y1.clone(), x1 - q * y1, g)
        }
    }

    if lhs.is_zero() || rhs.is_zero() {
        return (T::zero(), T::zero(), T::zero())
    }

    if lhs.euclid_norm() >= rhs.euclid_norm() {
        euclid(lhs, rhs)
    } else {
        let (y, x, g) = euclid(rhs, lhs);
        (x, y, g)
    }

}

///
///Determines if a given Natural number is [prime](Primality) using the
///[Miller-Rabin primality test](https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test)
///
///The algorithm works in essence by searching for counter-examples to Fermat's Little theorem, ie,
///that `a^(p-1) = 1` for all `a` in `Z/pZ` when `p` is prime. In general, this tactic only gives a
///way to prove a number is _not_ prime, but with a few modifications to the check and by picking
///the right examples, it is possible to turn this into a deterministic test. \*
///
///Furthermore, this particular algorithm has the surprising benefit of having a runtime that is
///polynomial in the number of bits in the input. Of course, this does not guarantee that this function
///is particularly "fast" per se, but in testing, the algorithm runs reasonable fast for all primitive
///integer types.
///
///\* It is important to note that the particular method used to achieve a Deterministic Miller Robin
///algorithm in polynomial time, _technically_ depends on the Generalized Riemann Hypothesis. So I
///guess that means that for super huge numbers, this technically _could_ give a false positive... ¯\\\_(ツ)\_/¯
///But hey, what _else_ is there? The AKS Primality Test?
///
pub fn miller_rabin<Z:Natural>(n:Z) -> bool {
    //trivial cases
    if n <= Z::one() { return false; }
    if n == Z::two() { return true; }
    if n.even() { return false; }

    //decompose n-1 (ie. -1 in Z/nZ) into a product of the form d*2^s
    let mut d = n.clone() - Z::one();
    let mut s = Z::zero();
    while d.even() {
        s = s + Z::one();
        d = d.div_two();
    }

    #[inline]
    fn witness<N:Natural>(witness:u128, d:N, s:N, n:N) -> bool {
        _witness(N::try_from(witness).unwrap_or(N::zero()), d, s, n)
    }

    fn _witness<N:Natural>(mut a:N, mut d:N, mut s:N, n:N) -> bool {
        let mut r = a.clone();
        d = d - N::one();
        while d > N::zero() {
            if d.even() {
                d = d.div_two();
                a = (a.clone() * a) % n.clone();
            } else {
                d = d - N::one();
                r = (r * a.clone()) % n.clone();
            }
        }

        if r.is_one() {
            true
        } else {
            loop {

                if r == n.clone() - N::one() { return true; }

                if s.is_zero() {
                    break;
                } else {
                    s = s - N::one();
                    r = (r.clone() * r) % n.clone();
                }
            }
            false
        }

    }

    //the breakpoints for each set of sufficient witnesses
    let b1:Z = Z::try_from(2047u32).unwrap_or(Z::zero());
    let b2:Z = Z::try_from(1373653u32).unwrap_or(Z::zero());
    let b3:Z = Z::try_from(9080191u32).unwrap_or(Z::zero());
    let b4:Z = Z::try_from(25326001u32).unwrap_or(Z::zero());
    let b5:Z = Z::try_from(3215031751u64).unwrap_or(Z::zero());
    let b6:Z = Z::try_from(4759123141u64).unwrap_or(Z::zero());
    let b7:Z = Z::try_from(1122004669633u64).unwrap_or(Z::zero());
    let b8:Z = Z::try_from(2152302898747u64).unwrap_or(Z::zero());
    let b9:Z = Z::try_from(3474749660383u64).unwrap_or(Z::zero());
    let b10:Z = Z::try_from(341550071728321u64).unwrap_or(Z::zero());
    let b11:Z = Z::try_from(3825123056546413051u64).unwrap_or(Z::zero());
    let b12:Z = Z::try_from(318665857834031151167461u128).unwrap_or(Z::zero());
    let b13:Z = Z::try_from(3317044064679887385961981u128).unwrap_or(Z::zero());

    if b1.is_zero() || n < b1 {
        witness(2, d.clone(), s.clone(), n.clone())
    } else if b2.is_zero() || n < b2 {
        witness(2, d.clone(), s.clone(), n.clone()) &&
        witness(3, d.clone(), s.clone(), n.clone())
    } else if b3.is_zero() || n < b3 {
        witness(31, d.clone(), s.clone(), n.clone()) &&
        witness(73, d.clone(), s.clone(), n.clone())
    } else if b4.is_zero() || n < b4 {
        witness(2, d.clone(), s.clone(), n.clone()) &&
        witness(3, d.clone(), s.clone(), n.clone()) &&
        witness(5, d.clone(), s.clone(), n.clone())
    } else if b5.is_zero() || n < b5 {
        witness(2, d.clone(), s.clone(), n.clone()) &&
        witness(3, d.clone(), s.clone(), n.clone()) &&
        witness(5, d.clone(), s.clone(), n.clone()) &&
        witness(7, d.clone(), s.clone(), n.clone())
    } else if b6.is_zero() || n < b6 {
        witness(2, d.clone(), s.clone(), n.clone()) &&
        witness(7, d.clone(), s.clone(), n.clone()) &&
        witness(61, d.clone(), s.clone(), n.clone())
    } else if b7.is_zero() || n < b7 {
        witness(2, d.clone(), s.clone(), n.clone()) &&
        witness(13, d.clone(), s.clone(), n.clone()) &&
        witness(23, d.clone(), s.clone(), n.clone()) &&
        witness(1662803, d.clone(), s.clone(), n.clone())
    } else if b13.is_zero() || n < b13 {
        witness(2, d.clone(), s.clone(), n.clone()) &&
        witness(3, d.clone(), s.clone(), n.clone()) &&
        witness(5, d.clone(), s.clone(), n.clone()) &&
        witness(7, d.clone(), s.clone(), n.clone()) &&
        witness(11, d.clone(), s.clone(), n.clone()) &&
        if !b8.is_zero() && n >= b8 { witness(13, d.clone(), s.clone(), n.clone()) } else {true} &&
        if !b9.is_zero() && n >= b9 { witness(17, d.clone(), s.clone(), n.clone()) } else {true} &&
        if !b10.is_zero() && n >= b10 {
            witness(19, d.clone(), s.clone(), n.clone()) &&
            witness(23, d.clone(), s.clone(), n.clone())
        } else {true} &&
        if !b11.is_zero() && n >= b11 {
            witness(29, d.clone(), s.clone(), n.clone()) &&
            witness(31, d.clone(), s.clone(), n.clone()) &&
            witness(37, d.clone(), s.clone(), n.clone())
        } else {true} &&
        if !b12.is_zero() && n >= b12 { witness(41, d.clone(), s.clone(), n.clone()) } else {true}
    } else {

        //in general, we need to check every witness below 2*ln(n)^2
        let mut a = Z::two();
        while Z::try_from(3.pow_n(a.clone().div_two())).unwrap_or(n.clone()) < n.clone().mul_two() {
            if !_witness(a.clone(), d.clone(), s.clone(), n.clone()) {return false}
            a = a + Z::one();
        }
        true
    }

}

#[cfg(test)]
mod tests {
    use crate::algebra::*;

    //TODO: add tests for euclidean and extended_euclidean

    #[test]
    fn primality() {

        assert!(18446744073709551557u64.prime());
        assert!(!18446744073709551559u64.prime());
        assert!(!18446744073709551555u64.prime());

        assert!(2147483647u32.prime());
        assert!(!2147483649u32.prime());
        assert!(!2147483645u32.prime());

        assert!(65521u16.prime());
        assert!(65519u16.prime());
        assert!(!65523u16.prime());

        assert!(251u8.prime());
        assert!(!253u8.prime());
        assert!(!249u8.prime());

        assert!(13u8.prime());
        assert!(!15u8.prime());
    }

    #[test]
    fn factor() {

        #[cfg(feature = "std")] {
            assert_eq!(91u8.factors().collect::<Vec<_>>(), vec![7,13] );
            assert_eq!((-91i8).factors().collect::<Vec<_>>(), vec![-1,7,13] );

            assert_eq!(360u16.factors().collect::<Vec<_>>(), vec![2,2,2,3,3,5] );
            assert_eq!((-360i16).factors().collect::<Vec<_>>(), vec![-1,2,2,2,3,3,5] );

            assert_eq!(1971813u32.factors().collect::<Vec<_>>(), vec![3,17,23,41,41] );
            assert_eq!((-1971813i32).factors().collect::<Vec<_>>(), vec![-1,3,17,23,41,41] );

            assert_eq!(1971813u32.factors().collect::<Vec<_>>(), vec![3,17,23,41,41] );
            assert_eq!((-1971813i32).factors().collect::<Vec<_>>(), vec![-1,3,17,23,41,41] );

            assert_eq!(0x344CAF57AB24A9u64.factors().collect::<Vec<_>>(), vec![101,101,103,103,107,107,109,109]);
            assert_eq!((-0x344CAF57AB24A9i64).factors().collect::<Vec<_>>(), vec![-1,101,101,103,103,107,107,109,109]);
        }

        fn factors_slice<Z:IntegerSubset+Factorizable>(x:Z, dest: &mut [Z]) -> usize {
            let mut i = 0;
            for f in x.factors() {
                if i<dest.len() {
                    dest[i] = f;
                    i += 1;
                } else {
                    return i;
                }
            }
            return i;
        }

        let mut factors = [0xFF; 3];

        //test 0 returns 0
        assert_eq!(factors_slice(0u8, &mut factors), 1);
        assert_eq!(&factors, &[0,0xFF,0xFF]);

        //test 1 returns 1
        assert_eq!(factors_slice(1u8, &mut factors), 0);
        assert_eq!(&factors, &[0,0xFF,0xFF]);

        //test the algorithm stopping at the end of the array
        assert_eq!(factors_slice(210u8, &mut factors), 3);
        assert_eq!(&factors, &[2,3,5]);//skips 7

        let mut factors = [0;10];

        //test -1 giving -1
        assert_eq!(factors_slice(-1i64, &mut factors), 1);
        assert_eq!(&factors, &[-1,0,0,0,0,0,0,0,0,0]);

        assert_eq!(factors_slice(-0x344CAF57AB24A9i64, &mut factors), 9);
        assert_eq!(&factors, &[-1,101,101,103,103,107,107,109,109,0]);

        assert_eq!(factors_slice(0x344CAF57AB24A9i64, &mut factors), 8);
        assert_eq!(&factors, &[101,101,103,103,107,107,109,109,109,0]);


    }

}
