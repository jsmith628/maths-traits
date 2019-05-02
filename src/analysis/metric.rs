
use analysis::*;

///
///A real-valued function on a set `X` that quantifies the "distance" between objects
///
///This is rigorously defined as a function `d:X⨯X -> R` such that
/// * `d(x,y) > 0` for all `x != y`
/// * `d(x,x) = 0` for all `x`
/// * `d(x,z) <= d(x,y) + d(y,z)` for all `x`,`y`, and `z`
///
/// ## Implementation Note
///
///Due to the fact that there are often _many_ metrics for any given space and that a given
///kind of metric often applies to a whole family of spaces, this trait has been written
///with the intent of being implemented on type _other_ than the set `X` to which it applies.
///This way, a construction can implemented only once while still having access to all applicable
///metrics.
///
///A good example of this would a struct implementing all L<sup>p</sup> norms for a single
///implementation of a given ℝ<sup>3</sup> or similar
///
///
pub trait Metric<X, R:Real> {
    fn distance(&self, x1:X, x2:X) -> R;
}

///
///A real-valued function from a [VectorSpace] that quantifies it's length, allowing for null-vectors
///
///Specifically, a seminorm ‖x‖ is a real valued function from a vector space `X` such that:
/// * `‖x‖ >= 0`
/// * `‖cx‖ = |c|‖x‖`
/// * `‖x+y‖ <= ‖x‖ + ‖y‖`
///
///This is distinct from a [NormedMetric] in that it is allowed to be 0 for non-zero vectors
///
pub trait Seminorm<X:VectorSpace<R>, R:Real> {
    #[inline] fn norm(&self, x:X) -> R;
    #[inline] fn normalize(&self, x:X) -> X {x.clone() / self.norm(x)}
}

///
///A metric on a [VectorSpace] where each vector has a length consistant with the distance function
///
///Specifically, a norm ‖x‖ is a real valued function from a vector space `X` such that:
/// * `‖x‖ > 0` for all `x != 0`
/// * `‖cx‖ = |c|‖x‖`
/// * `‖x+y‖ <= ‖x‖ + ‖y‖`
///
///This is distinct from a [Seminorm] in that it is allowed to be 0 for non-zero vectors
///
pub trait NormedMetric<X:VectorSpace<R>, R:Real>: Seminorm<X,R> + Metric<X, R> {}

///
///A metric on vector-spaces using the [inner product](InnerProductSpace) of two vectors
///
///For finite dimensional real-vector spaces, this is simply the Euclidean metric, and for functions
///on measure-spaces, this gives the L2-metric
///
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct InnerProductMetric;

impl<R:Real, V:InnerProductSpace<R>> Metric<V,R> for InnerProductMetric {
    #[inline(always)] fn distance(&self, x1:V, x2:V) -> R {x1.dist_euclid(x2)}
}

impl<R:Real, V:InnerProductSpace<R>> Seminorm<V,R> for InnerProductMetric {
    #[inline(always)] fn norm(&self, x:V) -> R {x.norm()}
}

impl<R:Real, V:InnerProductSpace<R>> NormedMetric<V,R> for InnerProductMetric {}

///
///A [VectorSpace] over a subset of the complex numbers with a "sesquilinear" binary operation
///
///Rigorously, the inner product is a function `<•,•>:V⨯V -> F` for a vector space `V` over a field
///`F⊆ℂ` such that:
/// * `<x,x> ∈ ℝ` and `<x,x> > 0` for all `x!=0`
/// * `<x,y> = conj(<y,x>)` (where conj() is the complex conjugate)
/// * `<x+y,z> = <x,z> + <y,z>`
/// * `<c*x,z> = c*<x,z>`
///
pub trait InnerProductSpace<F: ComplexField + Trig + From<<F as ComplexSubset>::Real>>: VectorSpace<F> {
    fn inner_product(self, rhs: Self) -> F;

    #[inline] fn norm_sqrd(self) -> F::Real {self.clone().inner_product(self).as_real()}
    #[inline] fn norm(self) -> F::Real {self.norm_sqrd().sqrt()}
    #[inline] fn dist_euclid(self, rhs: Self) -> F::Real {(self - rhs).norm()}
    #[inline] fn normalize(self) -> Self {self.clone() / self.norm().into()}

    #[inline] fn orthogonal(self, rhs: Self) -> bool { self.inner_product(rhs).is_zero() }
    #[inline] fn angle(self, rhs: Self) -> F {
        let l1 = self.clone().norm();
        let l2 = rhs.clone().norm();
        (self.inner_product(rhs)/(l1*l2).into()).acos()
    }
}

auto!{
    pub trait HilbertSpace<F> = InnerProductSpace<F> + ConvergentBasis<F> where F:ComplexField + Trig + From<<F as ComplexSubset>::Real>;
    pub trait EuclidianSpace<R> = InnerProductSpace<R> + FiniteBasis<R> where R:Real;
}


macro_rules! impl_metric {
    ($($f:ident)*) => {$(
        impl InnerProductSpace<$f> for $f {
            #[inline(always)] fn inner_product(self, rhs: Self) -> $f {self * rhs}
            #[inline(always)] fn norm_sqrd(self) -> $f {self * self}
            #[inline(always)] fn norm(self) -> $f {self.abs()}
            #[inline(always)] fn orthogonal(self, rhs: Self) -> bool {self==0.0 || rhs==0.0}

            #[inline(always)]
            fn angle(self, rhs: Self) -> $f {
                if self.orthogonal(rhs) {::core::$f::consts::PI} else {0.0}
            }
        }
    )*}
}
impl_metric!(f32 f64);
