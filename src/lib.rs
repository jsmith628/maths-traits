//!
//!# Math Traits
//!
//!A simple crate for sane and usable abstractions of common (and uncommon) mathematical constructs
//!using the Rust trait system
//!
//!# Design Philosophy
//!
//!The framework in this crate is written to fit four design goals:
//!* Usage must be simple enough so as to add minimal complication to generics ontop of
//! working with particular implementations or primitives in order to make code more readible and maintainable.
//!* Implementation should utilize the current systems in [Standard Rust][std::ops] or well established
//! libraries (such as [`num_traits`]) instead of creating new systems that require significant special
//! attention to support.
//!* Traits should assume as much abstraction as possible so to have maximal flexibility
//! in what structs can fit a generic.
//!* Whenever possible, trait naming, function, and categorization should fit their corresponding
//! mathematical conventions.
//!
//!# Usage
//!
//!The traits in this framework are split into two sets: one for individual features and mathematical
//!properties and the other a class of auto-implementing traits for functionality grouping and
//! categorization. This way, to support the system, struct writers need only implement each
//!relevant property, and end users can simply use the single trait for whichever mathematical struct
//!fits their needs.
//!
//!For example, to implement the [albegraic](algebra) features for a rational type,
//!one would imlement Clone and the [`Add`](std::ops::Add), [`Sub`](std::ops::Sub), [`Mul`](std::ops::Mul),
//![`Div`](std::ops::Div), [`Neg`](std::ops::Neg), [`Inv`](num_traits::Inv), [`Zero`](num_traits::Zero),
//![`One`](num_traits::One), and their assign variants as normal as well as to the new traits
//![`AddCommutative`](algebra::AddCommutative), [`AddAssociative`](algebra::AddAssociative),
//![`MulCommutative`](algebra::MulCommutative), [`MulCommutative`](algebra::MulAssociative), and
//![`Distributive`](algebra::Distributive) to declare those algebraic properties for our type. Then,
//!the categorization traits such as [`Ring`](algebra::Ring) and [`MulMonoid`](algebra::MulMonoid) will
//!automatically be implemented and usable for our type.
//!
//!```
//!use math_traits::algebra::*;
//!
//!#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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
//!fn mul_add<F:Ring>(a:F, b:F, c:F) -> F { a*b + c }
//!use math_traits::algebra::group_like::repeated_squaring;
//!
//!assert_eq!(mul_add(Rational::new(1, 2), Rational::new(2, 3), Rational::new(1, 6)), Rational::new(1, 2));
//!assert_eq!(repeated_squaring(Rational::new(1, 2), 7u32), Rational::new(1, 128));
//!```
//!
//!# Supported Constructs
//!
//!Currently, mathematical support in `math_traits` consists of a system for algebraic structures
//!including [group-like](algebra::group_like), [ring-like](algebra::ring_like), [integer-like](algebra::integer),
//!and [module-like](algebra::module_like) structures and a system for analytical constructions such as
//![ordered and archimedian groups](analysis::ordered), [real and complex numbers](analysis::real),
//!and [metric and inner product spaces](analysis::metric). For more information, see each respective
//!module.
//!

#![feature(specialization)]
#![feature(euclidean_division)]
#![feature(extra_log_consts)]
#![recursion_limit="8096"]
// #![no_std]s



extern crate core;
extern crate num_traits;

macro_rules! auto {

    ({} @split ) => { };
    ({$($line:tt)+} @split ) => { compile_error!("Expected ;"); };
    ({$($line:tt)*} @split ; $($code:tt)*) => { auto!(@create $($line)*); auto!({} @split $($code)*); };
    ({$($line:tt)*} @split $t:tt $($code:tt)*) => { auto!({$($line)* $t} @split $($code)*); };

    //start the line parsing
    (@create $($line:tt)*) => {auto!({} @create $($line)*);};

    //parse the trait name and generic attributes
    ({$($kw:tt)*} @create trait $t:ident = $($line:tt)*) => {
        auto!({$($kw)*} {$t} {} {} @create $($line)*);
    };
    ({$($kw:tt)*} @create trait $t:ident<$($T:ident),*> = $($line:tt)*) => {
        auto!({$($kw)*} {$t} {$($T),*} {} @create $($line)*);
    };

    //bucket the keywords and attributes at the beginning of the line
    ({$($kws:tt)*} @create $kw:ident $($line:tt)*) => { auto!({$($kws)* $kw} @create $($line)*); };
    ({$($kws:tt)*} @create #[$meta:meta] $($line:tt)*) => { auto!({$($kws)* #[$meta]} @create $($line)*); };
    ({$($kw:tt)*} @create) => {compile_error!(concat!("Expected trait alias", stringify!($($line)*))); };
    ({$($kw:tt)*} @create $t:tt $($line:tt)*) => {compile_error!(concat!("Expected trait alias, found ", stringify!($t)));};

    //parse the trait dependencies and super traits
    ({$($kw:tt)*} {$name:ident} {$($T:tt)*} {$($deps:tt)*} @create) => {
        auto!({$($kw)*} {$name} {$($T)*} {$($deps)*} {} @create);
    };
    ({$($kw:tt)*} {$name:ident} {$($T:tt)*} {$($deps:tt)*} @create where $($line:tt)*) => {
        auto!({$($kw)*} {$name} {$($T)*} {$($deps)*} {where $($line)*} @create);
    };
    ({$($kw:tt)*} {$name:ident} {$($T:tt)*} {$($deps:tt)*} @create $dep:tt $($line:tt)*) => {
        auto!({$($kw)*} {$name} {$($T)*} {$($deps)* $dep} @create $($line)*);
    };

    //create the trait and its auto-implementation
    ({$($kw:tt)*} {$name:ident} {$($T:tt)*} {$($deps:tt)*} {$($wh:tt)*} @create) => {
        $($kw)* trait $name<$($T)*>: $($deps)* $($wh)* {}
        impl<_G: $($deps)*, $($T)*> $name<$($T)*> for _G $($wh)* {}
    };

    //start the parsing
    ($($code:tt)*) => { auto!({} @split $($code)*); };


}

pub mod algebra;
pub mod analysis;

#[cfg(test)]
mod tests {
    use algebra::*;

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

}
