//!
//!Traits for sets with binary operations
//!
//!Traits in this module have been split into four groups:
//!* ["Group-Like"](group_like) mathematical objects with one binary operation and
//! include structures such as [groups](MulGroup) and [monoids](MulMonoid)
//!* ["Ring-Like"](ring_like) mathematical objects with two binary operations that
//! [distribute](Distributive) over the other. This includes sets like [rings](Ring),
//! [semirings](Semiring), [division rings](DivisionRing), and [fields](Field).
//! In addition, this module contains an added system for integer-like properties like
//! [divisibility](Divisibility), [greatest common denominators](GCD), and
//! [Euclidean division](EuclideanDiv).
//!* ["Module-Like"](module_like) traits for groups with an added scalar multiplication operation.
//! This includes [vector spaces](VectorSpace), [ring modules](RingModule),
//! and [algebras](Algebra) as well as a system for [bilinear forms](BilinearForm).
//!* [Integer](Integer) and [Natural](Natural) numeric traits
//!
//!For ease of use, members of each module have been re-exported into this one.
//!

pub use self::group_like::*;
pub use self::ring_like::*;
pub use self::integer::*;
pub use self::module_like::*;

pub mod group_like;
pub mod ring_like;
pub mod integer;
pub mod module_like;
