
use analysis::*;

pub trait MetricSpace<R: Real>: Sized {
    fn distance(self, rhs: Self) -> R;
}

pub trait SemiNormedSpace<R: Real>: Sized + VectorSpace<R> {
    fn norm(&self) -> R;
    #[inline] fn normalize(self) -> Self { let l = self.norm(); self/l }
}

pub trait NormedSpace<R: Real>: SemiNormedSpace<R> + MetricSpace<R> {}

pub trait InnerProductSpace<F: ComplexField>: Sized + VectorSpace<F> + NormedSpace<F::Real> {
    fn inner_product(self, rhs: Self) -> F;
    fn norm_sqrd(&self) -> F::Real;

    #[inline] fn orthogonal(self, rhs: Self) -> bool { self.inner_product(rhs).is_zero() }

    #[inline]
    fn angle(self, rhs: Self) -> F::Real {
        let l1 = self.norm();
        let l2 = rhs.norm();
        (self.inner_product(rhs).as_real()/(l1*l2)).acos()
    }
}

auto!{
    pub trait HilbertSpace<F> = InnerProductSpace<F> + ConvergentBasis<F> where F:ComplexField;
    pub trait EuclidianSpace<R> = InnerProductSpace<R> + FiniteBasis<R> where R:Real;
}


macro_rules! impl_metric {
    ($($f:ident)*) => {$(
        impl MetricSpace<$f> for $f {
            #[inline(always)] fn distance(self, rhs: Self) -> $f {(rhs - self).abs()}
        }

        impl SemiNormedSpace<$f> for $f {
            #[inline(always)] fn norm(&self) -> $f {self.abs()}

            #[inline(always)]
            fn normalize(self) -> $f {
                if self==0.0 {panic!("Cannot normalize 0")} else {1.0}
            }
        }

        impl NormedSpace<$f> for $f {}

        impl InnerProductSpace<$f> for $f {
            #[inline(always)] fn inner_product(self, rhs: Self) -> $f {self * rhs}
            #[inline(always)] fn norm_sqrd(&self) -> $f {self * self}
            #[inline(always)] fn orthogonal(self, rhs: Self) -> bool {self==0.0 || rhs==0.0}

            #[inline(always)]
            fn angle(self, rhs: Self) -> $f {
                if self.orthogonal(rhs) {::core::$f::consts::PI} else {0.0}
            }
        }
    )*}
}
impl_metric!(f32 f64);
