
use analysis::*;

pub trait Metric<X, R:Real> {
    fn distance(&self, x1:X, x2:X) -> R;
}

pub trait SemiNormedMetric<X:VectorSpace<R>, R:Real>: Metric<X,R> {
    fn norm(&self, x:X) -> R;
    #[inline] fn normalize(&self, x:X) -> X {x.clone() / self.norm(x)}
}

pub trait NormedMetric<X:VectorSpace<R>, R:Real>: SemiNormedMetric<X,R> {}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct EuclideanMetric;

impl<R:Real, V:InnerProductSpace<R>> Metric<V,R> for EuclideanMetric {
    #[inline(always)] fn distance(&self, x1:V, x2:V) -> R {x1.dist_euclid(x2)}
}

impl<R:Real, V:InnerProductSpace<R>> SemiNormedMetric<V,R> for EuclideanMetric {
    #[inline(always)] fn norm(&self, x:V) -> R {x.norm()}
}

impl<R:Real, V:InnerProductSpace<R>> NormedMetric<V,R> for EuclideanMetric {}

pub trait InnerProductSpace<F: ComplexField + From<<F as ComplexSubset>::Real>>: VectorSpace<F> {
    fn inner_product(self, rhs: Self) -> F;

    #[inline] fn norm_sqrd(self) -> F::Real {self.clone().inner_product(self).as_real()}
    #[inline] fn norm(self) -> F::Real {self.norm_sqrd().sqrt()}
    #[inline] fn dist_euclid(self, rhs: Self) -> F::Real {(self - rhs).norm()}
    #[inline] fn normalize(self) -> Self {self.clone() / self.norm().into()}

    #[inline] fn orthogonal(self, rhs: Self) -> bool { self.inner_product(rhs).is_zero() }
    #[inline] fn angle(self, rhs: Self) -> F::Real {
        let l1 = self.clone().norm();
        let l2 = rhs.clone().norm();
        (self.inner_product(rhs).as_real()/(l1*l2)).acos()
    }
}

auto!{
    pub trait HilbertSpace<F> = InnerProductSpace<F> + ConvergentBasis<F> where F:ComplexField + From<<F as ComplexSubset>::Real>;
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
