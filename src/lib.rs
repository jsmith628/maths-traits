//!
//!# Maths Traits
//!
//!A simple crate of traits for usable abstractions of common (and uncommon) mathematical constructs
//!
//!# Design
//!
//!The purpose of this crate is to provide a system for working with mathematical objects
//!that is maximally abstract *and* that is easy enough to use such that working with mathematical
//!generics and high abstraction is nearly as simple as designing around a specific type.
//!
//!This system can be used in cases ranging broadly from something as simple as making [reals](analysis::Real) number
//!algorithms apply seamlessly to different precisions to simplifying [vector](algebra::VectorSpace)
//!systems such that using polynomials as coordinates is as easy as switching to a [ring module](algebra::RingModule),
//!or even to something complex like separating the different poperties of [rings](algebra::ring_like)
//!from the [Integers](algebra::Integer) so that objects like polynomials can be rightfully marked
//!as able to do things like [Euclidean division](algebra::EuclideanDiv)
//!
//!To accomplish this goal, the provided framework provided is built with a number of design considerations:
//!* For ease of use and implementation, the included systems utilize [standard Rust][std] or well established
//!  libraries, like [`num_traits`], whenever possible instead of creating new systems.
//!* Traits representing operations or properties and traits representing particular kinds of structures
//!  have been seperated in distinct sets of feature traits and distinct sets of trait aliases. This
//!  way, implementation of the structures is a simple matter of implementing the features and using
//!  the features is as easy as adding a single generic bound for the structure that contains all the desired features
//!* The systems have been named and organized to fit mathematical convention as much as possible in
//!  order to add clarity of use while also increasing generality and flexibility
//!
//!# Usage
//!
//!The traits in this framework are split into two collections, a set of traits for individual properties
//!and operations and a set of trait aliases for mathematical structures that have those properties.
//!This way, to support the system, structs need only implement each relevant property, and to use the system
//!users can simply bound generics by the single alias of whatever mathematical struct fits their needs.
//!
//!For example, for a generalized `Rational` type,
//!you would implement the standard [`Clone`](Clone), [`Add`](std::ops::Add), [`Sub`](std::ops::Sub),
//![`Mul`](std::ops::Mul),
//![`Div`](std::ops::Div), [`Neg`](std::ops::Neg), [`Inv`](num_traits::Inv), [`Zero`](num_traits::Zero),
//![`One`](num_traits::One) traits, and their assign variants as normal. Then, by implementing the new traits
//![`AddCommutative`](algebra::AddCommutative), [`AddAssociative`](algebra::AddAssociative),
//![`MulCommutative`](algebra::MulCommutative), [`MulCommutative`](algebra::MulAssociative), and
//![`Distributive`](algebra::Distributive), all of the aliases using those operations (such as [`Ring`](algebra::Ring)
//!and [`MulMonoid`](algebra::MulMonoid)) will automatically be implemented and usable for the type.
//!
//!<details>
//!<summary> ▶ <i>click to show</i> </summary>
//!
//!```
//!use maths_traits::algebra::*;
//!
//!#[derive(Clone)] //necessary to auto-implement Ring and MulMonoid
//!#[derive(Copy, PartialEq, Eq, Debug)] //for convenience and displaying output
//!pub struct Rational {
//!    n: i32,
//!    d: i32
//!}
//!
//!impl Rational {
//!    pub fn new(numerator:i32, denominator:i32) -> Self {
//!        let gcd = numerator.gcd(denominator);
//!        Rational{n: numerator/gcd, d: denominator/gcd}
//!    }
//!}
//!
//!//Unary Operations from std::ops and num_traits
//!
//!impl Neg for Rational {
//!    type Output = Self;
//!    fn neg(self) -> Self { Rational::new(-self.n, self.d) }
//!}
//!
//!impl Inv for Rational {
//!    type Output = Self;
//!    fn inv(self) -> Self { Rational::new(self.d, self.n) }
//!}
//!
//!//Binary Operations from std::ops
//!
//!impl Add for Rational {
//!    type Output = Self;
//!    fn add(self, rhs:Self) -> Self {
//!        Rational::new(self.n*rhs.d + rhs.n*self.d, self.d*rhs.d)
//!    }
//!}
//!
//!impl AddAssign for Rational {
//!    fn add_assign(&mut self, rhs:Self) {*self = *self+rhs;}
//!}
//!
//!impl Sub for Rational {
//!    type Output = Self;
//!    fn sub(self, rhs:Self) -> Self {
//!        Rational::new(self.n*rhs.d - rhs.n*self.d, self.d*rhs.d)
//!    }
//!}
//!
//!impl SubAssign for Rational {
//!    fn sub_assign(&mut self, rhs:Self) {*self = *self-rhs;}
//!}
//!
//!impl Mul for Rational {
//!    type Output = Self;
//!    fn mul(self, rhs:Self) -> Self { Rational::new(self.n*rhs.n, self.d*rhs.d) }
//!}
//!
//!impl MulAssign for Rational {
//!    fn mul_assign(&mut self, rhs:Self) {*self = *self*rhs;}
//!}
//!
//!impl Div for Rational {
//!    type Output = Self;
//!    fn div(self, rhs:Self) -> Self { Rational::new(self.n*rhs.d, self.d*rhs.n) }
//!}
//!
//!impl DivAssign for Rational {
//!    fn div_assign(&mut self, rhs:Self) {*self = *self/rhs;}
//!}
//!
//!//Identities from num_traits
//!
//!impl Zero for Rational {
//!    fn zero() -> Self {Rational::new(0,1)}
//!    fn is_zero(&self) -> bool {self.n==0}
//!}
//!
//!impl One for Rational {
//!    fn one() -> Self {Rational::new(1, 1)}
//!    fn is_one(&self) -> bool {self.n==1 && self.d==1}
//!}
//!
//!//algebraic properties from math_traits::algebra
//!
//!impl AddAssociative for Rational {}
//!impl AddCommutative for Rational {}
//!impl MulAssociative for Rational {}
//!impl MulCommutative for Rational {}
//!impl Distributive for Rational {}
//!
//!//Now, Ring and MulMonoid are automatically implemented for us
//!
//!fn mul_add<R:Ring>(a:R, b:R, c:R) -> R { a*b + c }
//!use maths_traits::algebra::group_like::repeated_squaring;
//!
//!let half = Rational::new(1, 2);
//!let two_thirds = Rational::new(2, 3);
//!let sixth = Rational::new(1, 6);
//!
//!assert_eq!(mul_add(half, two_thirds, sixth), half);
//!assert_eq!(repeated_squaring(half, 7u32), Rational::new(1, 128));
//!```
//!</details> <p>
//!
//!In addition, with little effort, using a more abstract `Integer` or `GCDDomain` bound we can generalize
//!significantly to be able to have more options for numerators and
//!denominators, including every primitive integer precision, various big-integer types, or even
//!structures like polynomials or functions<p>.
//!
//!
//!<details>
//!<summary> ▶ <i>click to show</i> </summary>
//!
//!```
//!use maths_traits::algebra::*;
//!
//!//Using a GCDDomain here means we can use more integral types, polynomials, and other types
//!#[derive(Clone, Copy, PartialEq, Eq, Debug)]
//!pub struct Rational<T:GCDDomain> {
//!    n:T, d:T
//!}
//!
//!impl<T:GCDDomain> Rational<T> {
//!    pub fn new(numerator:T, denominator:T) -> Self {
//!        let gcd = numerator.clone().gcd(denominator.clone());
//!        Rational{n: numerator.divide(gcd.clone()).unwrap(), d: denominator.divide(gcd).unwrap()}
//!    }
//!}
//!
//!//Standard operations remain basically the same as for the i32 case
//!
//!impl<T:GCDDomain> Neg for Rational<T> {
//!    type Output = Self;
//!    fn neg(self) -> Self { Rational::new(-self.n, self.d) }
//!}
//!
//!impl<T:GCDDomain> Inv for Rational<T> {
//!    type Output = Self;
//!    fn inv(self) -> Self { Rational::new(self.d, self.n) }
//!}
//!
//!impl<T:GCDDomain> Add for Rational<T> {
//!    type Output = Self;
//!    fn add(self, rhs:Self) -> Self {
//!        Rational::new(self.n*rhs.d.clone() + rhs.n*self.d.clone(), self.d*rhs.d)
//!    }
//!}
//!
//!impl<T:GCDDomain> AddAssign for Rational<T> {
//!    fn add_assign(&mut self, rhs:Self) {*self = self.clone()+rhs;}
//!}
//!
//!impl<T:GCDDomain> Sub for Rational<T> {
//!    type Output = Self;
//!    fn sub(self, rhs:Self) -> Self {
//!        Rational::new(self.n*rhs.d.clone() - rhs.n*self.d.clone(), self.d*rhs.d)
//!    }
//!}
//!
//!impl<T:GCDDomain> SubAssign for Rational<T> {
//!    fn sub_assign(&mut self, rhs:Self) {*self = self.clone()-rhs;}
//!}
//!
//!impl<T:GCDDomain> Mul for Rational<T> {
//!    type Output = Self;
//!    fn mul(self, rhs:Self) -> Self { Rational::new(self.n*rhs.n, self.d*rhs.d) }
//!}
//!
//!impl<T:GCDDomain> MulAssign for Rational<T> {
//!    fn mul_assign(&mut self, rhs:Self) {*self = self.clone()*rhs;}
//!}
//!
//!impl<T:GCDDomain> Div for Rational<T> {
//!    type Output = Self;
//!    fn div(self, rhs:Self) -> Self { Rational::new(self.n*rhs.d, self.d*rhs.n) }
//!}
//!
//!impl<T:GCDDomain> DivAssign for Rational<T> {
//!    fn div_assign(&mut self, rhs:Self) {*self = self.clone()/rhs;}
//!}
//!
//!impl<T:GCDDomain+PartialEq> Zero for Rational<T> {
//!    fn zero() -> Self {Rational::new(T::zero(),T::one())}
//!    fn is_zero(&self) -> bool {self.n.is_zero()}
//!}
//!
//!impl<T:GCDDomain+PartialEq> One for Rational<T> {
//!    fn one() -> Self {Rational::new(T::one(), T::one())}
//!    fn is_one(&self) -> bool {self.n.is_one() && self.d.is_one()}
//!}
//!
//!impl<T:GCDDomain> AddAssociative for Rational<T> {}
//!impl<T:GCDDomain> AddCommutative for Rational<T> {}
//!impl<T:GCDDomain> MulAssociative for Rational<T> {}
//!impl<T:GCDDomain> MulCommutative for Rational<T> {}
//!impl<T:GCDDomain> Distributive for Rational<T> {}
//!
//!//Now, we can use both 8-bit integers AND 64 bit integers
//!
//!let half = Rational::new(1i8, 2i8);
//!let sixth = Rational::new(1, 6);
//!let two_thirds = Rational::new(2i64, 3i64);
//!let one_third = Rational::new(1i64, 3i64);
//!
//!assert_eq!(half + sixth, Rational::new(2, 3));
//!assert_eq!(two_thirds + one_third, Rational::new(1, 1));
//!```
//!</details>
//!
//!# Currently Supported Constructs
//!
//!Currently, `maths_traits` supports traits for the following systems of mathematical structures:
//! * [Group-Like](algebra::group_like) algebraic structures: monoids, groups, abelian groups, etc
//! * [Ring-Like](algebra::ring_like) algebraic structures: rings, fields, GCD domains, Euclidean domains, etc
//! * [Module-Like](algebra::module_like) structures: vector spaces, algebras, bilinear-forms, etc
//! * [Integer](algebra::integer::Integer) and [Natural](algebra::integer::Natural) numbers
//! * [Ordered](analysis::ordered) algebraic structures: ordered/archimedian rings, fields, etc
//! * [Real](analysis::real::Real) and [Complex](analysis::real::Complex) numbers
//! * [Metric](analysis::metric) properties of sets: metric spaces, inner-product, norm, etc
//!
//!# `no_std`
//!
//!It is possible to use `maths-traits` without the standard library. To do so, simply compile
//!without the `std` feature by disabling default features in `Cargo.toml`.
//!
//!```TOML
//![dependencies]
//!maths-traits = {version = "0.2", default-features = false}
//!```
//!
//!However, do note that the [`real`](analysis::real) module and anything that depends on it will
//!only be available when using `std` as the floating-point trigonometric and exponential operations
//!are only available when linking to the standard library.
//!
//!# Possible Future Features
//!
//!As `maths_traits` is still in developement, there are a number of features that may be included
//!at a later date:
//! * Traits for vector spaces of finite or countable dimension that have discrete elements. This
//!   will *almost certainly* be added eventually, but hasn't been added yet do to a number of relatively
//!   difficult design questions and time constraints.
//! * A system for category-like structures, ie, sets with an operation that is partial over its elements.
//!   This would relatively simple to add, but *so far*, there do not seem to be enough use cases for such a
//!   system to offset the added code complexity.
//! * Systems for sets, geometric shapes, and set measure. The might be included in the future, but
//!   so far, they do not seem to fit within the scope of this project.
//!
//!Of course, if anyone feels that any specific feature be added, feel free to file an issue or
//!contribute at the [github](https://github.com/anvil777/maths-traits) repository. Since most
//!of the non-implemeted features are non-implemented due to usefulness concerns, if a feature is
//!requested (and is reasonable), it will probably be added (though this is not a guarantee).
//!
//!# Release Stability
//!
//!At the moment, this project is still in developement, so the API most definitely could still change.
//!However, large portions of the crate could definitely be considered fairly stable, so going forward,
//!particularly unstable systems will be gated behind the `unstable` optional feature in order
//!to provide more clarity as to what is and isn't bound to change.
//!
//!Specifically though, expect most changes to occur in the module, metric, and integer systems.
//!

#![feature(trait_alias)]
#![feature(specialization)]
#![feature(extra_log_consts)]

#![cfg_attr(not(feature = "std"), no_std)]

pub mod algebra;
pub mod analysis;
