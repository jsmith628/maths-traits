
# Math Traits

A simple crate for sane and usable abstractions of common (and uncommon) mathematical constructs
using the Rust trait system

# Design Philosophy

The framework in this crate is written to fit four design goals:
* Traits should be flexible and assume as much mathematical abstraction as possible.
* Trait names, functions, and categorization should fit their corresponding
 mathematical conventions.
* Usage must be simple enough so that working with these generics instead of primitives add
 minimal complication
* Implementation should utilize the standard Rust or well established
 libraries (such as `num_traits`) as much as possible instead of creating new systems
 requiring significant special attention to support.

# Usage

The traits in this framework are split into two collections, one for individual features and mathematical
properties and one for common mathematical structures, where the second set of traits is automatically
implemented by grouping together functionality from the first set. This way, to support the system,
structs need only implement each relevant property, and end users can simply use the single
trait for whichever mathematical struct fits their needs.

For example, to implement the algebraic features for a `Rational` type,
one would implement `Clone`, `Add`, `Sub`, `Mul`,
`Div`, `Neg`, `Inv`, `Zero`,
`One`, and their assign variants as normal. Then, by implementing the new traits
`AddCommutative`, `AddAssociative`,
`MulCommutative`, `MulCommutative`, and
`Distributive`, all of the categorization traits (such as `Ring`
and `MulMonoid`) will automatically be implemented and usable for the type.

```
use math_traits::algebra::*;

#[derive(Clone)] //necessary to auto-implement Ring and MulMonoid
#[derive(Copy, PartialEq, Eq, Debug)] //for convenience and displaying output
pub struct Rational {
    n: i32,
    d: i32
}

impl Rational {
    pub fn new(numerator:i32, denominator:i32) -> Self {
        let gcd = numerator.gcd(denominator);
        Rational{n: numerator/gcd, d: denominator/gcd}
    }
}

//Unary Operations from std::ops and num_traits

impl Neg for Rational {
    type Output = Self;
    fn neg(self) -> Self { Rational::new(-self.n, self.d) }
}

impl Inv for Rational {
    type Output = Self;
    fn inv(self) -> Self { Rational::new(self.d, self.n) }
}

//Binary Operations from std::ops

impl Add for Rational {
    type Output = Self;
    fn add(self, rhs:Self) -> Self {
        Rational::new(self.n*rhs.d + rhs.n*self.d, self.d*rhs.d)
    }
}

impl AddAssign for Rational {
    fn add_assign(&mut self, rhs:Self) {*self = *self+rhs;}
}

impl Sub for Rational {
    type Output = Self;
    fn sub(self, rhs:Self) -> Self {
        Rational::new(self.n*rhs.d - rhs.n*self.d, self.d*rhs.d)
    }
}

impl SubAssign for Rational {
    fn sub_assign(&mut self, rhs:Self) {*self = *self-rhs;}
}

impl Mul for Rational {
    type Output = Self;
    fn mul(self, rhs:Self) -> Self { Rational::new(self.n*rhs.n, self.d*rhs.d) }
}

impl MulAssign for Rational {
    fn mul_assign(&mut self, rhs:Self) {*self = *self*rhs;}
}

impl Div for Rational {
    type Output = Self;
    fn div(self, rhs:Self) -> Self { Rational::new(self.n*rhs.d, self.d*rhs.n) }
}

impl DivAssign for Rational {
    fn div_assign(&mut self, rhs:Self) {*self = *self/rhs;}
}

//Identities from num_traits

impl Zero for Rational {
    fn zero() -> Self {Rational::new(0,1)}
    fn is_zero(&self) -> bool {self.n==0}
}

impl One for Rational {
    fn one() -> Self {Rational::new(1, 1)}
    fn is_one(&self) -> bool {self.n==1 && self.d==1}
}

//algebraic properties from math_traits::algebra

impl AddAssociative for Rational {}
impl AddCommutative for Rational {}
impl MulAssociative for Rational {}
impl MulCommutative for Rational {}
impl Distributive for Rational {}

//Now, Ring and MulMonoid are automatically implemented for us

fn mul_add<R:Ring>(a:R, b:R, c:R) -> R { a*b + c }
use math_traits::algebra::group_like::repeated_squaring;

let half = Rational::new(1, 2);
let two_thirds = Rational::new(2, 3);
let sixth = Rational::new(1, 6);

assert_eq!(mul_add(half, two_thirds, sixth), half);
assert_eq!(repeated_squaring(half, 7u32), Rational::new(1, 128));
```

# Supported Constructs

Currently, the mathematical structures supported in `math_traits` consist of a system of
group-like, ring-like, integer-like,
and module-like algebraic structures and a system of analytical constructions including
ordered and Archimedean groups, real and complex numbers,
and metric and inner product spaces. For more information, see each respective
module.
