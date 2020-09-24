//!
//!Traits for [Real] and [Complex] properties and representations
//!

use crate::algebra::*;
use crate::analysis::*;

///
///Functions and constants for evaluative trigonometric values
///
///For the most part, these methods are meant for struct representing [real numbers](Real),
///and so, for those, the included functions have their normal meaning. However, in order to
///include the generalizations (such as the complex trig functions), the precise definitions are
///defined in a more abstract way.
///
///Specifically, all of the included methods should satisfy the relevant differential equation definition
///of its function. Specifically:
/// * [Sine](Trig::sin) and [Cosine](Trig::cos) should satisfy
///     * `d/dx cos(x) = -sin(x)`
///     * `d/dx sin(x) = cos(x)`
///     * `cos(0) = 1`
///     * `sin(0) = 0`
/// * [Tangent](Trig::tan) should satisfy
///     * `d/dx tan(x) = 1 + tan²(x)`
///     * `tan(0) = 0`
/// * [Hyperbolic Sine](Trig::sinh) and [Hyperbolic Cosine](Trig::cosh) should satisfy
///     * `d/dx cosh(x) = sinh(x)`
///     * `d/dx sinh(x) = cosh(x)`
///     * `cosh(0) = 1`
///     * `sinh(0) = 0`
/// * [Hyperbolic Tangent](Trig::tanh) should satisfy
///     * `d/dx tanh(x) = 1 - tanh²(x)`
///     * `tanh(0) = 0`
///
///Of course, for Real and Complex numbers, the standard infinite series definitions also apply
///and are most likely the method of computation.
///
pub trait Trig: UnitalRing + Divisibility {

    ///
    ///Finds the Sine of the given value
    ///
    ///For more general inputs, this is defined as the solution to:
    /// * `f"(x) = -f(x)`
    /// * `f(0) = 0`
    /// * `f'(0) = 1`
    ///
    fn sin(self) -> Self;

    ///
    ///Finds the Cosine of the given value
    ///
    ///For more general inputs, this is defined as the solution to:
    /// * `f"(x) = -f(x)`
    /// * `f(0) = 1`
    /// * `f'(0) = 0`
    ///
    fn cos(self) -> Self;

    ///
    ///Finds the Tangent of the given value
    ///
    ///For more general inputs, this is defined as the solution to:
    /// * `f'(x) = 1 + f(x)²`
    /// * `f(0) = 0`
    ///
    fn tan(self) -> Self;

    ///
    ///Finds both the [Sine](Trig::sin) and [Cosine](Trig::cos) as a tuple
    ///
    ///This is supposed to mirror f32::sin_cos() and f64::sin_cos()
    ///
    #[inline] fn sin_cos(self) -> (Self, Self) {(self.clone().sin(), self.cos())}

    ///
    ///Finds the Hyperbolic Sine of the given value
    ///
    ///For more general inputs, this is defined as the solution to:
    /// * `f"(x) = f(x)`
    /// * `f(0) = 0`
    /// * `f'(0) = 1`
    ///
    fn sinh(self) -> Self;

    ///
    ///Finds the Hyperbolic Cosine of the given value
    ///
    ///For more general inputs, this is defined as the solution to:
    /// * `f"(x) = f(x)`
    /// * `f(0) = 1`
    /// * `f'(0) = 0`
    ///
    fn cosh(self) -> Self;

    ///
    ///Finds the Hyperbolic Tangent of the given value
    ///
    ///For more general inputs, this is defined as the solution to:
    /// * `f'(x) = 1 - f(x)²`
    /// * `f(0) = 0`
    ///
    fn tanh(self) -> Self;

    ///
    ///A continuous inverse function of [Sine](Trig::sin) such that `asin(1) = π/2` and `asin(-1) = -π/2`
    ///
    ///Returns a `None` value if and only if the inverse doesn't exist for the given input
    fn try_asin(self) -> Option<Self>;

    ///
    ///A continuous inverse function of [Cosine](Trig::cos) such that `acos(1) = 0` and `asin(-1) = π`
    ///
    ///Returns a `None` value if and only if the inverse doesn't exist for the given input
    fn try_acos(self) -> Option<Self>;

    ///
    ///A continuous inverse function of [Sine](Trig::sin) such that `asin(1) = π/2` and `asin(-1) = -π/2`
    ///
    ///If the inverse does not exist for the given input, then the implementation can
    ///decide between a `panic!` or returning some form of error value (like `NaN`). In general though,
    ///there is no guarrantee which of these will occur, so it is suggested to use [Trig::try_asin]
    ///in such cases.
    ///
    #[inline] fn asin(self) -> Self {self.try_asin().unwrap()}

    ///
    ///A continuous inverse function of [Cosine](Trig::cos) such that `acos(1) = 0` and `asin(-1) = π`
    ///
    ///If the inverse does not exist for the given input, then the implementation can
    ///decide between a `panic!` or returning some form of error value (like `NaN`). In general though,
    ///there is no guarrantee which of these will occur, so it is suggested to use [Trig::try_acos]
    ///in such cases.
    ///
    #[inline] fn acos(self) -> Self {self.try_acos().unwrap()}

    ///A continuous inverse function of [Tangent](Trig::tan) such that `atan(0) = 0` and `atan(1) = π/4`
    fn atan(self) -> Self;

    ///
    ///A continuous function of two variables where `tan(atan2(y,x)) = y/x` for `y!=0` and `atan2(0,1) = 0`
    ///
    ///This is particularly useful for real numbers, where this gives the angle a vector `(x,y)` makes
    ///with the x-axis, without the singularities and ambiguity of computing [`atan(y/x)`](Trig::atan)
    ///
    fn atan2(y: Self, x: Self) -> Self;

    ///
    ///A continuous inverse function of [Hyperbolic Sine](Trig::sinh) such that `asinh(0)=0`
    ///
    ///Returns a `None` value if and only if the inverse doesn't exist for the given input
    fn try_asinh(self) -> Option<Self>;

    ///
    ///A continuous inverse function of [Hyperbolic Cosine](Trig::cosh) such that `acosh(0)=1`
    ///
    ///Returns a `None` value if and only if the inverse doesn't exist for the given input
    fn try_acosh(self) -> Option<Self>;

    ///
    ///A continuous inverse function of [Hyperbolic Tangent](Trig::tanh) such that `atanh(0)=0`
    ///
    ///Returns a `None` value if and only if the inverse doesn't exist for the given input
    fn try_atanh(self) -> Option<Self>;

    ///
    ///A continuous inverse function of [Hyperbolic Sine](Trig::sinh) such that `asinh(0)=0`
    ///
    ///If the inverse does not exist for the given input, then the implementation can
    ///decide between a `panic!` or returning some form of error value (like `NaN`). In general though,
    ///there is no guarrantee which of these will occur, so it is suggested to use [Trig::try_asinh]
    ///in such cases.
    ///
    #[inline] fn asinh(self) -> Self {self.try_asinh().unwrap()}

    ///
    ///A continuous inverse function of [Hyperbolic Cosine](Trig::cosh) such that `acosh(0)=1`
    ///
    ///If the inverse does not exist for the given input, then the implementation can
    ///decide between a `panic!` or returning some form of error value (like `NaN`). In general though,
    ///there is no guarrantee which of these will occur, so it is suggested to use [Trig::try_acosh]
    ///in such cases.
    ///
    #[inline] fn acosh(self) -> Self {self.try_acosh().unwrap()}

    ///
    ///A continuous inverse function of [Hyperbolic Tangent](Trig::tanh) such that `atanh(0)=0`
    ///
    ///If the inverse does not exist for the given input, then the implementation can
    ///decide between a `panic!` or returning some form of error value (like `NaN`). In general though,
    ///there is no guarrantee which of these will occur, so it is suggested to use [Trig::try_atanh]
    ///in such cases.
    ///
    #[inline] fn atanh(self) -> Self {self.try_atanh().unwrap()}

    ///
    ///The classic cicle constant
    ///
    ///For real-algebras, this should be exactly what you expect: the ratio of a circle's cicumferance
    ///to its diameter. However, in keeping with the generalized trig function definitions, this should
    ///give the value of [`acos(-1)`](Trig::acos) and be a zero of [Sine](Trig::sin) and [Tangent](Trig::tan)
    ///regardless of if it is the circle constant for the euclidean metric
    ///
    fn pi() -> Self;

    ///`2/π`. Mirrors [FRAC_2_PI](::core::f32::consts::FRAC_2_PI)
    #[inline] fn frac_2_pi() -> Self {Self::one().mul_n(2u32).divide(Self::pi()).unwrap()}
    ///`π/2`. Mirrors [FRAC_PI_2](::core::f32::consts::FRAC_PI_2)
    #[inline] fn frac_pi_2() -> Self {Self::pi().divide(Self::one().mul_n(2u32)).unwrap()}
    ///`π/3`. Mirrors [FRAC_PI_3](::core::f32::consts::FRAC_PI_3)
    #[inline] fn frac_pi_3() -> Self {Self::pi().divide(Self::one().mul_n(3u32)).unwrap()}
    ///`π/4`. Mirrors [FRAC_PI_4](::core::f32::consts::FRAC_PI_4)
    #[inline] fn frac_pi_4() -> Self {Self::pi().divide(Self::one().mul_n(4u32)).unwrap()}
    ///`π/6`. Mirrors [FRAC_PI_6](::core::f32::consts::FRAC_PI_6)
    #[inline] fn frac_pi_6() -> Self {Self::pi().divide(Self::one().mul_n(6u32)).unwrap()}
    ///`π/8`. Mirrors [FRAC_PI_8](::core::f32::consts::FRAC_PI_8)
    #[inline] fn frac_pi_8() -> Self {Self::pi().divide(Self::one().mul_n(8u32)).unwrap()}

    ///The length of the hypotenuse of a unit right-triangle. Mirrors [SQRT_2](::core::f32::consts::SQRT_2)
    #[inline] fn pythag_const() -> Self {Self::one().mul_n(2u32) * Self::pythag_const_inv()}

    ///The sine of [`π/4`](Trig::frac_pi_4()). Mirrors [FRAC_1_SQRT_2](::core::f32::consts::FRAC_1_SQRT_2)
    #[inline] fn pythag_const_inv() -> Self {Self::frac_pi_4().sin()}

    #[inline] fn to_degrees(self) -> Self {self * (Self::one().mul_n(180u32).divide(Self::pi()).unwrap())}
    #[inline] fn to_radians(self) -> Self {self * (Self::pi().divide(Self::one().mul_n(180u32)).unwrap())}
}

pub use crate::algebra::Exponential;

///
///An exponential ring with Real-like properties
///
///Specifically, this trait should be implemented on any [Exponential Ring](ExponentialRing)
///where the [natural logarithm](Exponential::try_ln) exists for any positive integer and is
///continuous almost everywhere[*][1], the purpose being that the above property guarantees
///a large number of [Real]-like behavior and functions for free utilizing only the exponential function.
///
///In particular, this property can be used to prove that:
/// * This ring contains a form of the positive Rationals: `exp(-ln(x)) = 1/exp(ln(x)) = 1/x`
/// * The logarithm of any positive rational exists: `ln(p/q) = ln(p) - ln(q)`
/// * We can take the nth-root of any rational with `exp(ln(x)/n)`
/// * We can raise any rational to the power of any other rational using `exp(ln(x)*y)`
/// * Any of the above can be extended to all reals using the continuity of the logarithm
///
///Now, it is worth noting that this distinction between the "Real Exponential" and "Exponential"
///is necessarily since certain exponential rings are only possible if they do not fit this description.
///In particular, the [integers](Integer) have an exponential defined as `(-1)^n` which obviously
///does not output any naturals besides 1
///
///[1]: https://en.wikipedia.org/wiki/Almost_everywhere
///
pub trait RealExponential: Exponential + UnitalRing + Divisibility {

    ///This element raised to the given power as defined by `x^y = exp(ln(x)*y)`, if `ln(x)` exists
    #[inline] fn try_pow(self, power:Self) -> Option<Self> { self.try_ln().map(move |x| (x * power).exp()) }
    ///This element taken to the given root as defined as `root(x, y) = x^(1/y)`, if `ln(x)` and `1/y` exist
    #[inline] fn try_root(self, index:Self) -> Option<Self> { index.inverse().and_then(move |x| self.try_pow(x)) }
    ///The inverse of [pow()](RealExponential::try_pow), if it exists
    #[inline] fn try_log(self, base: Self) -> Option<Self> {
        self.try_ln().and_then(move |x| base.try_ln().and_then(move |y| x.divide(y)))
    }

    ///
    ///The natural logarithm of `self`
    ///
    ///Do note that this function is allowed to panic or return an error value whenever
    ///the desired logarithm does not exist. This exception is specifically to allow primitive
    ///floats to implement this method as a wrapper for the intrinsic definition
    ///
    #[inline] fn ln(self) -> Self {self.try_ln().unwrap()}

    ///
    ///The logarithm of `self` over a specific base
    ///
    ///Do note that this function is allowed to panic or return an error value whenever
    ///the desired logarithm does not exist. This exception is specifically to allow primitive
    ///floats to implement this method as a wrapper for the intrinsic definition
    ///
    #[inline] fn log(self, base: Self) -> Self {self.try_log(base).unwrap()}

    ///
    ///The power of `self` over a specific exponent
    ///
    ///Do note that this function is allowed to panic or return an error value whenever
    ///the desired power does not exist. This exception is specifically to allow primitive
    ///floats to implement this method as a wrapper for the intrinsic definition
    ///
    #[inline] fn pow(self, p: Self) -> Self {self.try_pow(p).unwrap()}

    ///
    ///The root of `self` over a specific index
    ///
    ///Do note that this function is allowed to panic or return an error value whenever
    ///the desired root does not exist. This exception is specifically to allow primitive
    ///floats to implement this method as a wrapper for the intrinsic definition
    ///
    #[inline] fn root(self, r: Self) -> Self {self.try_root(r).unwrap()}

    ///Raises 2 to the power of `self`
    #[inline] fn exp2(self) -> Self {self.pow(Self::one().mul_n(2u32))}

    ///Raises 10 to the power of `self`
    #[inline] fn exp10(self) -> Self { self.pow(Self::one().mul_n(10u32)) }

    ///The logarithm of base 2
    #[inline] fn log2(self) -> Self {self.log(Self::one().mul_n(2u32))}

    ///The logarithm of base 10
    #[inline] fn log10(self) -> Self { self.log(Self::one().mul_n(10u32)) }

    //Takes the square-root of `self`
    #[inline] fn sqrt(self) -> Self {self.root(Self::one().mul_n(2u32))}

    //Takes the cube-root of `self`
    #[inline] fn cbrt(self) -> Self {self.root(Self::one().mul_n(3u32))}

    ///
    ///The natural logarithm of `self` plus 1.
    ///
    ///This is meant as a wrapper for f32::ln_1p and f64::ln_1p
    ///
    #[inline] fn ln_1p(self) -> Self {(self-Self::one()).ln()}

    ///
    ///The exponential of `self` minus 1.
    ///
    ///This is meant as a wrapper for f32::exp_m1 and f64::exp_m1
    ///
    #[inline] fn exp_m1(self) -> Self {self.exp()-Self::one()}

    ///The exponential of 1. Mirrors [::core::f32::consts::E]
    #[inline] fn e() -> Self {Self::one().exp()}

    ///The natural logarithm of 2. Mirrors [::core::f32::consts::LN_2]
    #[inline] fn ln_2() -> Self {Self::one().mul_n(2u32).ln()}

    ///The natural logarithm of 10. Mirrors [::core::f32::consts::LN_10]
    #[inline] fn ln_10() -> Self {Self::one().mul_n(10u32).ln()}

    ///The logarithm base 2 of e. Mirrors [::core::f32::consts::LOG2_E]
    #[inline] fn log2_e() -> Self {Self::ln_2().inverse().unwrap()}

    ///The logarithm base 10 of e. Mirrors [::core::f32::consts::LOG10_E]
    #[inline] fn log10_e() -> Self {Self::ln_10().inverse().unwrap()}

    ///The logarithm base 2 of 10. Mirrors [::core::f32::consts::LOG2_10]
    #[inline] fn log2_10() -> Self {Self::ln_10().divide(Self::ln_2()).unwrap()}

    ///The logarithm base 10 of 2. Mirrors [::core::f32::consts::LOG10_2]
    #[inline] fn log10_2() -> Self {Self::ln_2().divide(Self::ln_10()).unwrap()}

    ///The square root of 2. Mirrors [::core::f32::consts::SQRT_2]
    #[inline] fn sqrt_2() -> Self {Self::one().mul_n(2u32).sqrt()}

    ///One over the square root of 2. Mirrors [::core::f32::consts::FRAC_1_SQRT_2]
    #[inline] fn frac_1_sqrt_2() -> Self {Self::sqrt_2().inverse().unwrap()}
}

///
///An algebraic stucture that is a subset of the [Complex] numbers
///
///This trait is both meant as an ensapsulation of the [naturals](Natural), [integers](Integer),
///[real numbers](Real), and [complex numbers](Complex). This way, users can work with a particular
///set of similar-precision numeric types abstractly similarly to how they would normally.
///
pub trait ComplexSubset: PartialEq + Clone + Semiring {
    type Real: Real
        + ComplexSubset<Natural = Self::Natural, Integer = Self::Integer, Real = Self::Real>;
    type Natural: Natural
        + IntegerSubset<Signed = Self::Integer, Unsigned = Self::Natural>
        + ComplexSubset<Natural = Self::Natural, Integer = Self::Integer, Real = Self::Real>;
    type Integer: Integer
        + IntegerSubset<Signed = Self::Integer, Unsigned = Self::Natural>
        + ComplexSubset<Natural = Self::Natural, Integer = Self::Integer, Real = Self::Real>;

    ///Converts `self` to a real number, discarding any imaginary component, if complex.
    fn as_real(self) -> Self::Real;

    ///Converts `self` to a natural number, truncating when necessary.
    fn as_natural(self) -> Self::Natural;

    ///Converts `self` to an integer, truncating when necessary.
    fn as_integer(self) -> Self::Integer;

    ///Rounds the real and imaginary components of `self` to the closest integer downward
    fn floor(self) -> Self;

    ///Rounds the real and imaginary components of `self` to the closest integer upward
    fn ceil(self) -> Self;

    ///Rounds the real and imaginary components of `self` to the closest integer
    fn round(self) -> Self;

    ///Rounds the real and imaginary components of `self` by removing the factional parts
    fn trunc(self) -> Self;

    ///Removes the integral parts of the real and imaginary components of `self`
    fn fract(self) -> Self;

    ///Sets the real component of `self` to 0
    fn im(self) -> Self;

    ///Sets the imaginary component of `self` to 0
    fn re(self) -> Self;

    ///The complex conjugate of `self`
    fn conj(self) -> Self;

    ///
    ///The square of the complex absolute value of `self`
    ///
    ///This is computed as `self * self.conj()` by default
    ///
    #[inline] fn modulus_sqrd(self) -> Self { self.clone() * self.conj()}

    ///
    ///The complex absolute value of `self`
    ///
    ///This is computed as the square root of [modulus_sqrd](ComplexSubset::modulus_sqrd) by default
    ///
    #[inline] fn modulus(self) -> Self::Real { (self.clone() * self.conj()).as_real().sqrt()}
}

///A commutative semiring that is also a subset of the Complex numbers
pub trait ComplexSemiring = CommutativeSemiring + ComplexSubset;
///A commutative ring that is also a subset of the Complex numbers
pub trait ComplexRing = CommutativeRing + ComplexSubset;
///A field that is also a subset of the Complex numbers
pub trait ComplexField = Field + ComplexSubset;

///
///A type representing the real numbers
///
///Note that in order to accomidate the primitive floats, this trait does _technically_ allow for
///special values such as [infinity](::core::f32::INFINITY) and [NaN](::core::f32::NAN)
///to return from operations
///as error codes, but usage of such values is discouraged in favor of alternative functions that return
///[optional](::core::option::Option) values instead
///
pub trait Real: ArchField + ComplexSubset<Real=Self> + Trig + RealExponential {

    ///
    ///Approximates this real number as a 64-bit floating point
    ///
    ///This is meant as a convenient way to interface with code using primitives, and in most cases,
    ///this will exactly represent the given value since most real representations are 32 or 64-bit floats
    ///However, this is not always the case, and the returned value is only guaranteed to be within
    ///the precision of an f64.
    ///
    fn approx(self) -> f64;

    ///
    ///Constructs a real number from a 64-bit floating point
    ///
    ///This is meant to be a convenient way to input constants into algorithms with generics and to
    ///interface with code using primitives, and in most cases, this should constant fold and represent
    ///the given value precisely. However, there is no guarantee of this as the representation returned
    ///could have a different precision than the f64
    ///
    fn repr(f: f64) -> Self;
}

///A type representing the complex numbers
pub trait Complex: ComplexField + Trig + RealExponential + From<<Self as ComplexSubset>::Real> {
    ///The imaginary unit representing `√̅-̅1`
    fn i() -> Self;

    ///
    ///Multiplies `self` by [`i`](Complex::i)
    ///
    ///This is meant both as convenience and to be potentially faster than normal multiplication
    ///as this can be done using only data moves and negation
    ///
    fn mul_i(self) -> Self;

    ///
    ///Divides `self` by [`i`](Complex::i). This is also equivalent to multiplication by `-i`
    ///
    ///This is meant both as convenience and to be potentially faster than normal multiplication
    ///as this can be done using only data moves and negation
    ///
    fn div_i(self) -> Self;
}

#[cfg(feature = "std")]
macro_rules! float_to_option {
    ($expr:expr) => {
        {
            let result = $expr;
            if result.is_infinite() || result.is_nan() {
                None
            } else {
                Some(result)
            }
        }
    }
}

#[cfg(feature = "std")]
macro_rules! impl_real {
    ($($f:ident:$n:ident:$z:ident)*) => {$(
        impl Trig for $f {
            #[inline(always)] fn sin(self) -> Self {self.sin()}
            #[inline(always)] fn cos(self) -> Self {self.cos()}
            #[inline(always)] fn tan(self) -> Self {self.tan()}
            #[inline(always)] fn sin_cos(self) -> (Self,Self) {self.sin_cos()}

            #[inline(always)] fn sinh(self) -> Self {self.sinh()}
            #[inline(always)] fn cosh(self) -> Self {self.cosh()}
            #[inline(always)] fn tanh(self) -> Self {self.tanh()}

            #[inline] fn try_asin(self) -> Option<Self> {float_to_option!(self.asin())}
            #[inline] fn try_acos(self) -> Option<Self> {float_to_option!(self.acos())}
            #[inline(always)] fn asin(self) -> Self {self.asin()}
            #[inline(always)] fn acos(self) -> Self {self.acos()}
            #[inline(always)] fn atan(self) -> Self {self.atan()}
            #[inline(always)] fn atan2(y:Self, x:Self) -> Self {$f::atan2(y,x)}

            #[inline] fn try_asinh(self) -> Option<Self> {float_to_option!(self.asinh())}
            #[inline] fn try_acosh(self) -> Option<Self> {float_to_option!(self.acosh())}
            #[inline] fn try_atanh(self) -> Option<Self> {float_to_option!(self.atanh())}
            #[inline(always)] fn asinh(self) -> Self {self.asinh()}
            #[inline(always)] fn acosh(self) -> Self {self.acosh()}
            #[inline(always)] fn atanh(self) -> Self {self.atanh()}

            #[inline(always)] fn pi() -> Self {::core::$f::consts::PI}
            #[inline(always)] fn frac_2_pi() -> Self {::core::$f::consts::FRAC_2_PI}
            #[inline(always)] fn frac_pi_2() -> Self {::core::$f::consts::FRAC_PI_2}
            #[inline(always)] fn frac_pi_3() -> Self {::core::$f::consts::FRAC_PI_3}
            #[inline(always)] fn frac_pi_4() -> Self {::core::$f::consts::FRAC_PI_4}
            #[inline(always)] fn frac_pi_6() -> Self {::core::$f::consts::FRAC_PI_6}
            #[inline(always)] fn frac_pi_8() -> Self {::core::$f::consts::FRAC_PI_8}

            #[inline(always)] fn pythag_const() -> Self {::core::$f::consts::SQRT_2}
            #[inline(always)] fn pythag_const_inv() -> Self {::core::$f::consts::FRAC_1_SQRT_2}

            #[inline(always)] fn to_degrees(self) -> Self { self.to_degrees() }
            #[inline(always)] fn to_radians(self) -> Self { self.to_radians() }
        }

        impl Exponential for $f {
            #[inline(always)] fn exp(self) -> Self {self.exp()}
            #[inline] fn try_ln(self) -> Option<Self> { float_to_option!(self.ln()) }
        }

        impl RealExponential for $f {
            #[inline] fn try_pow(self, power:Self) -> Option<Self> { float_to_option!(self.pow(power)) }
            #[inline] fn try_root(self, index:Self) -> Option<Self> { float_to_option!(self.root(index)) }
            #[inline] fn try_log(self, base: Self) -> Option<Self> { float_to_option!(self.log(base)) }

            #[inline(always)] fn pow(self, power:Self) -> Self { self.powf(power)}
            #[inline(always)] fn exp2(self) -> Self {self.exp2()}
            #[inline(always)] fn exp10(self) -> Self {$f::from(10.0).pow(self)}

            #[inline(always)] fn log(self, base:Self) -> Self {self.log(base)}
            #[inline(always)] fn ln(self) -> Self {self.ln()}
            #[inline(always)] fn log2(self) -> Self {self.log2()}
            #[inline(always)] fn log10(self) -> Self {self.log10()}

            #[inline(always)] fn root(self, index:Self) -> Self {self.pow(index.recip())}
            #[inline(always)] fn sqrt(self) -> Self {self.sqrt()}
            #[inline(always)] fn cbrt(self) -> Self {self.cbrt()}

            #[inline(always)] fn ln_1p(self) -> Self {self.ln_1p()}
            #[inline(always)] fn exp_m1(self) -> Self {self.exp_m1()}

            #[inline(always)] fn e() -> Self {::core::$f::consts::E}
            #[inline(always)] fn ln_2() -> Self {::core::$f::consts::LN_2}
            #[inline(always)] fn ln_10() -> Self {::core::$f::consts::LN_10}
            #[inline(always)] fn log2_e() -> Self {::core::$f::consts::LOG2_E}
            #[inline(always)] fn log10_e() -> Self {::core::$f::consts::LOG10_E}
            #[inline(always)] fn log2_10() -> Self {::core::$f::consts::LOG2_10}
            #[inline(always)] fn log10_2() -> Self {::core::$f::consts::LOG10_2}
            #[inline(always)] fn sqrt_2() -> Self {::core::$f::consts::SQRT_2}
            #[inline(always)] fn frac_1_sqrt_2() -> Self {::core::$f::consts::FRAC_1_SQRT_2}
        }

        impl ComplexSubset for $f {
            type Real = $f;
            type Natural = $n;
            type Integer = $z;

            #[inline(always)] fn as_real(self) -> Self::Real {self}
            #[inline(always)] fn as_natural(self) -> Self::Natural {self as $n}
            #[inline(always)] fn as_integer(self) -> Self::Integer {self as $z}

            #[inline(always)] fn floor(self) -> Self { self.floor() }
            #[inline(always)] fn ceil(self) -> Self {self.ceil()}
            #[inline(always)] fn round(self) -> Self {self.round()}

            #[inline(always)] fn trunc(self) -> Self {self.trunc()}
            #[inline(always)] fn fract(self) -> Self {self.fract()}

            #[inline(always)] fn im(self) -> Self {self}
            #[inline(always)] fn re(self) -> Self {self}
            #[inline(always)] fn conj(self) -> Self {self}

            #[inline(always)] fn modulus_sqrd(self) -> Self { self * self }
            #[inline(always)] fn modulus(self) -> Self::Real { self.abs() }
        }

        impl ComplexSubset for $n {
            type Real = $f;
            type Natural = $n;
            type Integer = $z;

            #[inline(always)] fn as_real(self) -> Self::Real {self as $f}
            #[inline(always)] fn as_natural(self) -> Self::Natural {self}
            #[inline(always)] fn as_integer(self) -> Self::Integer {self as $z}

            #[inline(always)] fn floor(self) -> Self {self}
            #[inline(always)] fn ceil(self) -> Self {self}
            #[inline(always)] fn round(self) -> Self {self}

            #[inline(always)] fn trunc(self) -> Self {self}
            #[inline(always)] fn fract(self) -> Self {0}

            #[inline(always)] fn im(self) -> Self {self}
            #[inline(always)] fn re(self) -> Self {self}
            #[inline(always)] fn conj(self) -> Self {self}

            #[inline(always)] fn modulus_sqrd(self) -> Self { self * self }
            #[inline(always)] fn modulus(self) -> Self::Real { self as $f }
        }

        impl ComplexSubset for $z {
            type Real = $f;
            type Natural = $n;
            type Integer = $z;

            #[inline(always)] fn as_real(self) -> Self::Real {self as $f}
            #[inline(always)] fn as_natural(self) -> Self::Natural {self as $n}
            #[inline(always)] fn as_integer(self) -> Self::Integer {self}

            #[inline(always)] fn floor(self) -> Self {self}
            #[inline(always)] fn ceil(self) -> Self {self}
            #[inline(always)] fn round(self) -> Self {self}

            #[inline(always)] fn trunc(self) -> Self {self}
            #[inline(always)] fn fract(self) -> Self {0}

            #[inline(always)] fn im(self) -> Self {self}
            #[inline(always)] fn re(self) -> Self {self}
            #[inline(always)] fn conj(self) -> Self {self}

            #[inline(always)] fn modulus_sqrd(self) -> Self { self * self }
            #[inline(always)] fn modulus(self) -> Self::Real { self.abs() as $f }
        }

        impl Real for $f {
            #[inline(always)] fn approx(self) -> f64 {self as f64}
            #[inline(always)] fn repr(f: f64) -> Self {f as $f}
        }

    )*}
}

#[cfg(feature = "std")] impl_real!(f32:u32:i32 f64:u64:i64);

macro_rules! int_exp {
    ($($t:ident)*) => {
        $(
            impl Exponential for $t {
                #[inline] fn exp(self) -> Self { if self.even() {1} else {-1} }
                #[inline] fn try_ln(self) -> Option<Self> {
                    match self {
                         1 => Some(0),
                        -1 => Some(1),
                         _ => None
                    }
                }
            }
        )*
    }
}

int_exp!(i8 i16 i32 i64 isize i128);
