
use algebra::*;
use analysis::*;

///
///Functions and constants for evaluative trigonometric values
///
///For the most part, these methods are meant for struct representing [real numbers](Real),
///and so, for those, the included functions have their normal meaning. However, in order to
///include the useful generalizations of the trigonometric functions (such as the complex numbers),
///this trait also supports mathematical constructions that can satisfy other characterizations.
///
///In particular, all of the included methods should satisfy the relevant differential equation definition
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

    ///`2/π`. Mirrors [FRAC_2_PI](::std::f32::consts::FRAC_2_PI)
    #[inline] fn frac_2_pi() -> Self {Self::one().mul_n(2u32).divide(Self::pi()).unwrap()}
    ///`π/2`. Mirrors [FRAC_PI_2](::std::f32::consts::FRAC_PI_2)
    #[inline] fn frac_pi_2() -> Self {Self::pi().divide(Self::one().mul_n(2u32)).unwrap()}
    ///`π/3`. Mirrors [FRAC_PI_3](::std::f32::consts::FRAC_PI_3)
    #[inline] fn frac_pi_3() -> Self {Self::pi().divide(Self::one().mul_n(3u32)).unwrap()}
    ///`π/4`. Mirrors [FRAC_PI_4](::std::f32::consts::FRAC_PI_4)
    #[inline] fn frac_pi_4() -> Self {Self::pi().divide(Self::one().mul_n(4u32)).unwrap()}
    ///`π/6`. Mirrors [FRAC_PI_6](::std::f32::consts::FRAC_PI_6)
    #[inline] fn frac_pi_6() -> Self {Self::pi().divide(Self::one().mul_n(6u32)).unwrap()}
    ///`π/8`. Mirrors [FRAC_PI_8](::std::f32::consts::FRAC_PI_8)
    #[inline] fn frac_pi_8() -> Self {Self::pi().divide(Self::one().mul_n(8u32)).unwrap()}

    ///The length of the hypotenuse of a unit right-triangle. Mirrors [SQRT_2](::std::f32::consts::SQRT_2)
    #[inline] fn pythag_const() -> Self {Self::one().mul_n(2u32) * Self::pythag_const_inv()}

    ///The sine of [`π/4`](Trig::frac_pi_4()). Mirrors [FRAC_1_SQRT_2](::std::f32::consts::FRAC_1_SQRT_2)
    #[inline] fn pythag_const_inv() -> Self {Self::frac_pi_4().sin()}

    #[inline] fn to_degrees(self) -> Self {self * (Self::one().mul_n(180u32).divide(Self::pi()).unwrap())}
    #[inline] fn to_radians(self) -> Self {self * (Self::pi().divide(Self::one().mul_n(180u32)).unwrap())}
}

///
///Functions for computing exponential based quantities
///
/// # Definitions
///
///For real and complex numbers, there are a [multitude][1] of equivalent definitions of e<sup>x</sup>
///and its related functions, but for specificity, any implementors should use the following characterization:
/// * for any `x` and `y` where `x*y=y*x`, `exp(x+y) = exp(x)*exp(y)`
/// * `exp(x) != 0` for all `x`
/// * if applicable, `exp(x)` is continuous at all `x`
/// * if applicable, `d/dx exp(1) = 1`
///
///The advantage of such a definition is that it generalizes well for systems beyond the real and complex
///numbers, such as matrices, quaternions, and Clifford algebras; where such a function has a very
///real practical use, such as solving differential equations and interpolating rotations.
///
///Furthermore, do note that the second two requirements can be relaxed to a claim about the existence
///one _one_ such `x`, since their applicability to _all_ `x` can be proven from the existence of
///a single point using the first requirement. Additionally, given this, using simple derivative properties,
///it is easy to show that if the last requirement is fullfilled, that the second two are satisfied
///as well.
///
///The other functions included in the trait are based on e<sup>x</sup> and their definitions are
///included in the appropriate documentation
///
/// # Notable Implications on Ring Structure
///
///Given the above definition, a series of algebraic arguments show that any [Unital Ring](UnitalRing)
///with an exponential function not only has characteristic 0 (ie. 1+1+...+1 is never 0), but that
///there is a natural embedding of the rational numbers and their integral roots into the ring. As such,
///this can be assumed to be the case (within rounding error) for any implementing structs as well,
///and it is up to the implementor to guarrantee that this is the case.
///
///[1]: https://en.wikipedia.org/wiki/Characterizations_of_the_exponential_function
///
pub trait Exponential: UnitalRing + Divisibility {

    ///
    ///The exponential of this ring element
    ///
    ///Here, `exp(x)` is defined such that:
    /// * `exp(x+y) = exp(x)*exp(y)` for all `x` and `y` where `x*y=y*x`
    /// * `exp(x) != 0`
    /// * `exp(x)` is continuous (if applicable)
    /// * `d/dx exp(1) = 1` (if applicable)
    ///
    ///For most structures, this function is equivalent to the infinite series Σ x<sup>n</sup>/n!
    ///
    ///
    fn exp(self) -> Self;

    ///
    ///An inverse of [exp(x)](Exponential::exp) where `ln(1) = 0`
    ///
    ///This returns a `None` value if and only if the inverse does not exist for the given input,
    ///like with negative real numbers and the real-valued logarithm.
    ///
    /// ## Uniqueness and Continuity
    ///
    ///Do note, however, that for almost all non-[Real] structures, this function
    ///is not unique and can *never* be continuous. Of course, some of this ambiguity is resolved by
    ///stipulating that `ln(1) = 0`, but even so, some remains,
    ///so it is entirely up to the implementor to guarrantee an canonical form if one exists.
    ///
    ///A noteworthy example are the [Complex] numbers, where there are infinitely many choices as
    ///to where to have the mandatory discontinuity
    ///
    fn try_ln(self) -> Option<Self>;

    ///The [exponential](Exponential::exp) of 1
    #[inline] fn e() -> Self {Self::one().exp()}
    #[inline] fn ln_2() -> Self {Self::one().mul_n(2u32).ln()}
    #[inline] fn ln_10() -> Self {Self::one().mul_n(10u32).ln()}
    #[inline] fn log2_e() -> Self {Self::ln_2().inverse().unwrap()}
    #[inline] fn log10_e() -> Self {Self::ln_10().inverse().unwrap()}
    #[inline] fn log2_10() -> Self {Self::ln_10().divide(Self::ln_2()).unwrap()}
    #[inline] fn log10_2() -> Self {Self::ln_2().divide(Self::ln_10()).unwrap()}

    #[inline] fn sqrt_2() -> Self {Self::one().mul_n(2u32).sqrt()}
    #[inline] fn frac_1_sqrt_2() -> Self {Self::sqrt_2().inverse().unwrap()}

    ///This element raised to the given power as defined by `x^y = exp(ln(x)*y)`, if `ln(x)` exists
    #[inline] fn try_pow(self, power:Self) -> Option<Self> { self.try_ln().map(move |x| (x * power).exp()) }
    ///This element taken to the given root as defined as `root(x, y) = x^(1/y)`, if `ln(x)` and `1/y` exist
    #[inline] fn try_root(self, index:Self) -> Option<Self> { index.inverse().and_then(move |x| self.try_pow(x)) }
    ///The inverse of [pow()](Exponential::try_pow), if it exists
    #[inline] fn try_log(self, base: Self) -> Option<Self> {
        self.try_ln().and_then(move |x| base.try_ln().and_then(move |y| x.divide(y)))
    }

    #[inline] fn ln(self) -> Self {self.try_ln().unwrap()}
    #[inline] fn log(self, base: Self) -> Self {self.try_log(base).unwrap()}
    #[inline] fn pow(self, p: Self) -> Self {self.try_pow(p).unwrap()}
    #[inline] fn root(self, r: Self) -> Self {self.try_root(r).unwrap()}

    #[inline] fn exp2(self) -> Self {self.pow(Self::one().mul_n(2u32))}
    #[inline] fn exp10(self) -> Self { self.pow(Self::one().mul_n(10u32)) }

    #[inline] fn log2(self) -> Self {self.log(Self::one().mul_n(2u32))}
    #[inline] fn log10(self) -> Self { self.log(Self::one().mul_n(10u32)) }

    #[inline] fn sqrt(self) -> Self {self.root(Self::one().mul_n(2u32))}
    #[inline] fn cbrt(self) -> Self {self.root(Self::one().mul_n(3u32))}

    #[inline] fn ln_1p(self) -> Self {(self-Self::one()).ln()}
    #[inline] fn exp_m1(self) -> Self {self.exp()-Self::one()}

}

pub trait ComplexSubset: PartialEq + Clone + InvolutiveSemiring {
    type Real: Real
        + ComplexSubset<Natural = Self::Natural, Integer = Self::Integer, Real = Self::Real>;
    type Natural: Natural
        + IntegerSubset<Signed = Self::Integer, Unsigned = Self::Natural>
        + ComplexSubset<Natural = Self::Natural, Integer = Self::Integer, Real = Self::Real>;
    type Integer: Integer
        + IntegerSubset<Signed = Self::Integer, Unsigned = Self::Natural>
        + ComplexSubset<Natural = Self::Natural, Integer = Self::Integer, Real = Self::Real>;

    fn as_real(self) -> Self::Real;
    fn as_natural(self) -> Self::Natural;
    fn as_integer(self) -> Self::Integer;

    fn floor(self) -> Self;
    fn ceil(self) -> Self;
    fn round(self) -> Self;

    fn trunc(self) -> Self;
    fn fract(self) -> Self;

    fn im(self) -> Self;
    fn re(self) -> Self;
    #[inline] fn conj(self) -> Self {self.involute()}

    #[inline] fn modulus_sqrd(self) -> Self { self.clone() * self.conj()}
    #[inline] fn modulus(self) -> Self::Real { (self.clone() * self.conj()).as_real().sqrt()}
}

auto!{
    pub trait ComplexField = Field + ComplexSubset;
}

pub trait Real: ArchField + ComplexSubset<Real=Self> + Trig + Exponential {
    fn approx(self) -> f64;
    fn repr(f: f64) -> Self;
}

pub trait Complex: ComplexField + Trig + Exponential + From<<Self as ComplexSubset>::Real> {
    fn i() -> Self;
    fn mul_i(self) -> Self;
    fn div_i(self) -> Self;
}

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

macro_rules! impl_real {
    ($($f:ident:$n:ident:$z:ident)*) => {$(
        impl Trig for $f {
            #[inline(always)] fn sin(self) -> Self {$f::sin(self)}
            #[inline(always)] fn cos(self) -> Self {$f::cos(self)}
            #[inline(always)] fn tan(self) -> Self {$f::tan(self)}
            #[inline(always)] fn sin_cos(self) -> (Self,Self) {$f::sin_cos(self)}

            #[inline(always)] fn sinh(self) -> Self {$f::sinh(self)}
            #[inline(always)] fn cosh(self) -> Self {$f::cosh(self)}
            #[inline(always)] fn tanh(self) -> Self {$f::tanh(self)}

            #[inline] fn try_asin(self) -> Option<Self> {float_to_option!($f::asin(self))}
            #[inline] fn try_acos(self) -> Option<Self> {float_to_option!($f::acos(self))}
            #[inline(always)] fn asin(self) -> Self {$f::asin(self)}
            #[inline(always)] fn acos(self) -> Self {$f::acos(self)}
            #[inline(always)] fn atan(self) -> Self {$f::atan(self)}
            #[inline(always)] fn atan2(y:Self, x:Self) -> Self {$f::atan2(y,x)}

            #[inline] fn try_asinh(self) -> Option<Self> {float_to_option!($f::asinh(self))}
            #[inline] fn try_acosh(self) -> Option<Self> {float_to_option!($f::acosh(self))}
            #[inline] fn try_atanh(self) -> Option<Self> {float_to_option!($f::atanh(self))}
            #[inline(always)] fn asinh(self) -> Self {$f::asinh(self)}
            #[inline(always)] fn acosh(self) -> Self {$f::acosh(self)}
            #[inline(always)] fn atanh(self) -> Self {$f::atanh(self)}

            #[inline(always)] fn pi() -> Self {::core::$f::consts::PI}
            #[inline(always)] fn frac_2_pi() -> Self {::core::$f::consts::FRAC_2_PI}
            #[inline(always)] fn frac_pi_2() -> Self {::core::$f::consts::FRAC_PI_2}
            #[inline(always)] fn frac_pi_3() -> Self {::core::$f::consts::FRAC_PI_3}
            #[inline(always)] fn frac_pi_4() -> Self {::core::$f::consts::FRAC_PI_4}
            #[inline(always)] fn frac_pi_6() -> Self {::core::$f::consts::FRAC_PI_6}
            #[inline(always)] fn frac_pi_8() -> Self {::core::$f::consts::FRAC_PI_8}

            #[inline(always)] fn pythag_const() -> Self {::core::$f::consts::SQRT_2}
            #[inline(always)] fn pythag_const_inv() -> Self {::core::$f::consts::FRAC_1_SQRT_2}

            #[inline(always)] fn to_degrees(self) -> Self { $f::to_degrees(self) }
            #[inline(always)] fn to_radians(self) -> Self { $f::to_radians(self) }
        }

        impl Exponential for $f {

            #[inline(always)] fn exp(self) -> Self {$f::exp(self)}
            #[inline] fn try_ln(self) -> Option<Self> { float_to_option!($f::ln(self)) }

            #[inline] fn try_pow(self, power:Self) -> Option<Self> { float_to_option!(self.pow(power)) }
            #[inline] fn try_root(self, index:Self) -> Option<Self> { float_to_option!(self.root(index)) }
            #[inline] fn try_log(self, base: Self) -> Option<Self> { float_to_option!($f::log(self,base)) }

            #[inline(always)] fn pow(self, power:Self) -> Self { self.powf(power)}
            #[inline(always)] fn exp2(self) -> Self {$f::exp2(self)}
            #[inline(always)] fn exp10(self) -> Self {$f::from(10.0).pow(self)}

            #[inline(always)] fn log(self, base:Self) -> Self {$f::log(self,base)}
            #[inline(always)] fn ln(self) -> Self {$f::ln(self)}
            #[inline(always)] fn log2(self) -> Self {$f::log2(self)}
            #[inline(always)] fn log10(self) -> Self {$f::log10(self)}

            #[inline(always)] fn root(self, index:Self) -> Self {self.pow(index.recip())}
            #[inline(always)] fn sqrt(self) -> Self {$f::sqrt(self)}
            #[inline(always)] fn cbrt(self) -> Self {$f::cbrt(self)}

            #[inline(always)] fn ln_1p(self) -> Self {$f::ln_1p(self)}
            #[inline(always)] fn exp_m1(self) -> Self {$f::exp_m1(self)}

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

            #[inline(always)] fn floor(self) -> Self {$f::floor(self)}
            #[inline(always)] fn ceil(self) -> Self {$f::ceil(self)}
            #[inline(always)] fn round(self) -> Self {$f::round(self)}

            #[inline(always)] fn trunc(self) -> Self {$f::trunc(self)}
            #[inline(always)] fn fract(self) -> Self {$f::fract(self)}

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

impl_real!(f32:u32:i32 f64:u64:i64);
