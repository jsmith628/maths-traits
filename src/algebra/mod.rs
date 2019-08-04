//!
//!Traits for sets with binary operations
//!
//!Traits in this module have been split into four groups:
//!* ["Group-Like"](algebra::group_like) mathematical objects with one binary operation and
//! include structures such as [groups](algebra::MulGroup) and [monoids](algebra::MulMonoid)
//!* ["Ring-Like"](algebra::ring_like) mathematical objects with two binary operations that
//! [distribute](algebra::Distributive) over the other. This includes sets like [rings](algebra::Ring),
//! [semirings](algebra::Semiring), [division rings](algebra::DivisionRing), and [fields](algebra::Field).
//! In addition, this module contains an added system for integer-like properties like
//! [divisibility](algebra::Divisibility), [greatest common denominators](algebra::GCD), and
//! [Euclidean division](algebra::EuclideanDiv).
//!* ["Module-Like"](algebra::module_like) traits for groups with an added scalar multiplication operation.
//! This includes [vector spaces](algebra::VectorSpace), [ring modules](algebra::RingModule),
//! and [algebras](algebra::Algebra) as well as a system for [bilinear forms](algebra::BilinearForm).
//!* [Integer](algebra::Integer) and [Natural](algebra::Natural) numeric traits
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
