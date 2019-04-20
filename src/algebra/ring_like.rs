use algebra::*;

pub trait Distributive {}

pub trait Divisibility: Sized {
    fn divides(self, rhs: Self) -> bool;
    fn divide(self, rhs: Self) -> Option<Self>;
    fn unit(&self) -> bool;
    fn inverse(self) -> Option<Self>;
}
pub trait Primality: Sized {
    fn irreducible(&self) -> bool;
    fn prime(&self) -> bool;
}
pub trait NoZeroDivisors: Sized {}
pub trait GCD: Sized {
    fn gcd(self, rhs: Self) -> Self;
    fn lcm(self, rhs: Self) -> Self;
}
pub trait Bezout: Sized {
    fn bezout_coefficients(self, rhs: Self) -> (Self, Self);
    fn bezout_with_gcd(self, rhs: Self) -> (Self, Self, Self);
}
pub trait UniquelyFactorizable: Sized {}

#[cfg(std)]
pub trait Factorizable: Sized {
    fn factors(&self) -> Vec<Self>;
}

pub trait EuclidianDiv: Sized {
    type Naturals: Natural;
    fn euclid_norm(&self) -> Self::Naturals;
    fn div_euc(self, rhs: Self) -> Self;
    fn rem_euc(self, rhs: Self) -> Self;

    #[inline]
    fn div_alg(self, rhs: Self) -> (Self, Self);

}

auto! {
    pub trait Semiring = Distributive + AddMonoid + AddCommutative + MulSemigroup;
    pub trait UnitalSemiring = Semiring + MulMonoid;
    pub trait CommutativeSemiring = UnitalSemiring + MulCommutative;
    pub trait DivisionSemiring = UnitalSemiring + MulGroup;

    pub trait Ring = Distributive + AddAbelianGroup + MulSemigroup;
    pub trait UnitalRing = Ring + MulMonoid;
    pub trait CommutativeRing = UnitalRing + MulCommutative;
    pub trait DivisionRing = UnitalRing + MulGroup;

    pub trait Semidomain = UnitalSemiring + Divisibility + NoZeroDivisors;
    pub trait IntegralSemidomain = Semidomain + MulCommutative;
    pub trait GCDSemidomain = IntegralSemidomain + GCD;
    pub trait UFSemidomain = GCDSemidomain + UniquelyFactorizable;
    pub trait EuclidianSemidomain = UFSemidomain + EuclidianDiv;

    pub trait Domain = UnitalRing + Divisibility + NoZeroDivisors;
    pub trait IntegralDomain = Domain + MulCommutative;
    pub trait GCDDomain = IntegralDomain + GCD;
    pub trait BezoutDomain = GCDDomain + Bezout;
    pub trait UFD = GCDDomain + UniquelyFactorizable;
    pub trait PID = UFD + BezoutDomain;
    pub trait EuclidianDomain = PID + EuclidianDiv;

    pub trait Field = CommutativeRing + MulGroup;

    pub trait Subsemiring<R> = Semiring + AddSubmonoid<R> + MulSubsemigroup<R> where R:Semiring;
    pub trait UnitalSubsemiring<R> = Semiring + AddSubmonoid<R> + MulSubmonoid<R> where R:UnitalSemiring;
    pub trait CommutativeSubsemiring<R> = CommutativeSemiring + UnitalSubsemiring<R> where R:UnitalSemiring;
    pub trait DivisionSubsemiring<R> = DivisionSemiring + AddSubmonoid<R> + MulSubgroup<R> where R:DivisionSemiring;

    pub trait Supersemiring<R> = Semiring + AddSupermonoid<R> + MulSupersemigroup<R> where R:Semiring;
    pub trait UnitalSupersemiring<R> = Semiring + AddSupermonoid<R> + MulSupermonoid<R> where R:UnitalSemiring;
    pub trait CommutativeSupersemiring<R> = CommutativeSemiring + UnitalSupersemiring<R> where R:CommutativeSemiring;
    pub trait DivisionSupersemiring<R> = DivisionSemiring + AddSupermonoid<R> + MulSupergroup<R> where R:DivisionSemiring;

    pub trait Subring<R> = Ring + AddAbelianSubgroup<R> + MulSubsemigroup<R> where R:Ring;
    pub trait UnitalSubring<R> = Ring + AddAbelianSubgroup<R> + MulSubmonoid<R> where R:UnitalRing;
    pub trait CommutativeSubring<R> = CommutativeRing + UnitalSubring<R> where R:UnitalRing;
    pub trait DivisionSubring<R> = DivisionRing + AddAbelianSubgroup<R> + MulSubgroup<R> where R:DivisionRing;
    pub trait Subfield<R> = Field + DivisionSubring<R> where R:DivisionRing;

    pub trait Superring<R> = Ring + AddAbelianSupergroup<R> + MulSupersemigroup<R> where R:Ring;
    pub trait UnitalSuperring<R> = Ring + AddAbelianSupergroup<R> + MulSupermonoid<R> where R:UnitalRing;
    pub trait CommutativeSuperring<R> = CommutativeRing + UnitalSuperring<R> where R:CommutativeRing;
    pub trait DivisionSuperring<R> = DivisionRing + AddAbelianSupergroup<R> + MulSupergroup<R> where R:DivisionRing;
    pub trait Superfield<R> = Field + DivisionSuperring<R> where R:Field;
}




//
//Implementation for primitives
//

macro_rules! impl_dist { ($($t:ty)*) => { $(impl Distributive for $t{})* }; }
impl_dist!(usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64);


pub fn euclidian<T>(lhs: T, rhs: T) -> T
    where T:Clone+CommutativeSemiring+EuclidianDiv
{

    fn euclid<U>(a: U, b: U) -> U where U:Clone+CommutativeSemiring+EuclidianDiv
    {
        let r = a.rem_euc(b.clone());
        if r.is_zero() {
            b
        }else{
            euclid(b, r)
        }
    }

    if lhs.is_zero() || rhs.is_zero() {return T::zero()}

    if lhs.euclid_norm() >= rhs.euclid_norm() {
        euclid(lhs, rhs)
    } else {
        euclid(rhs, lhs)
    }

}


pub fn extended_euclidian<T>(lhs: T, rhs: T) -> (T, T, T)
    where T:Clone+CommutativeRing+EuclidianDiv
{

    fn euclid<U>(a: U, b: U) -> (U, U, U) where U:Clone+CommutativeRing+EuclidianDiv
    {
        let (q, r) = a.div_alg(b.clone());
        if r.is_zero() {
            (U::zero(), U::one(), b)
        }else{
            let (x1, y1, g) = euclid(b, r);
            (y1.clone(), x1 - q * y1, g)
        }
    }

    if lhs.is_zero() || rhs.is_zero() {
        return (T::zero(), T::zero(), T::zero())
    }

    if lhs.euclid_norm() >= rhs.euclid_norm() {
        euclid(lhs, rhs)
    } else {
        let (y, x, g) = euclid(rhs, lhs);
        (x, y, g)
    }

}

pub fn miller_rabin<Z:Natural>(z:Z) -> bool {
    if z <= Z::one() { return false; }
    if z == Z::two() { return true; }
    if z.even() { return false; }

    let mut d = z.clone() - Z::one();
    let mut s = Z::zero();

    while d.even() {
        s = s + Z::one();
        d = d.div_two();
    }

    let b1:Z = Z::try_from(2047u32).unwrap_or(Z::zero());
    let b2:Z = Z::try_from(1373653u32).unwrap_or(Z::zero());
    let b3:Z = Z::try_from(9080191u32).unwrap_or(Z::zero());
    let b4:Z = Z::try_from(25326001u32).unwrap_or(Z::zero());
    let b5:Z = Z::try_from(3215031751u64).unwrap_or(Z::zero());
    let b6:Z = Z::try_from(4759123141u64).unwrap_or(Z::zero());
    let b7:Z = Z::try_from(1122004669633u64).unwrap_or(Z::zero());
    let b8:Z = Z::try_from(2152302898747u64).unwrap_or(Z::zero());
    let b9:Z = Z::try_from(3474749660383u64).unwrap_or(Z::zero());
    let b10:Z = Z::try_from(341550071728321u64).unwrap_or(Z::zero());
    let b11:Z = Z::try_from(3825123056546413051u64).unwrap_or(Z::zero());
    let b12:Z = Z::try_from(318665857834031151167461u128).unwrap_or(Z::zero());
    let b13:Z = Z::try_from(3317044064679887385961981u128).unwrap_or(Z::zero());

    #[inline]
    fn witness<N:Natural>(witness:u128, d:N, s:N, n:N) -> bool {
        _witness(N::try_from(witness).unwrap_or(N::zero()), d, s, n)
    }

    fn _witness<N:Natural>(mut a:N, mut d:N, mut s:N, n:N) -> bool {
        let mut r = a.clone();
        d = d - N::one();
        while d > N::zero() {
            if d.even() {
                d = d.div_two();
                a = (a.clone() * a) % n.clone();
            } else {
                d = d - N::one();
                r = (r * a.clone()) % n.clone();
            }
        }

        if r.is_one() {
            true
        } else {
            loop {

                if r == n.clone() - N::one() { return true; }

                if s.is_zero() {
                    break;
                } else {
                    s = s - N::one();
                    r = (r.clone() * r) % n.clone();
                }
            }
            false
        }

    }

    if b1.is_zero() || z < b1 {
        witness(2, d.clone(), s.clone(), z.clone())
    } else if b2.is_zero() || z < b2 {
        witness(2, d.clone(), s.clone(), z.clone()) &&
        witness(3, d.clone(), s.clone(), z.clone())
    } else if b3.is_zero() || z < b3 {
        witness(31, d.clone(), s.clone(), z.clone()) &&
        witness(73, d.clone(), s.clone(), z.clone())
    } else if b4.is_zero() || z < b4 {
        witness(2, d.clone(), s.clone(), z.clone()) &&
        witness(3, d.clone(), s.clone(), z.clone()) &&
        witness(5, d.clone(), s.clone(), z.clone())
    } else if b5.is_zero() || z < b5 {
        witness(2, d.clone(), s.clone(), z.clone()) &&
        witness(3, d.clone(), s.clone(), z.clone()) &&
        witness(5, d.clone(), s.clone(), z.clone()) &&
        witness(7, d.clone(), s.clone(), z.clone())
    } else if b6.is_zero() || z < b6 {
        witness(2, d.clone(), s.clone(), z.clone()) &&
        witness(7, d.clone(), s.clone(), z.clone()) &&
        witness(61, d.clone(), s.clone(), z.clone())
    } else if b7.is_zero() || z < b7 {
        witness(2, d.clone(), s.clone(), z.clone()) &&
        witness(13, d.clone(), s.clone(), z.clone()) &&
        witness(23, d.clone(), s.clone(), z.clone()) &&
        witness(1662803, d.clone(), s.clone(), z.clone())
    } else if b13.is_zero() || z < b13 {
        witness(2, d.clone(), s.clone(), z.clone()) &&
        witness(3, d.clone(), s.clone(), z.clone()) &&
        witness(5, d.clone(), s.clone(), z.clone()) &&
        witness(7, d.clone(), s.clone(), z.clone()) &&
        witness(11, d.clone(), s.clone(), z.clone()) &&
        if !b8.is_zero() && z >= b8 { witness(13, d.clone(), s.clone(), z.clone()) } else {true} &&
        if !b9.is_zero() && z >= b9 { witness(17, d.clone(), s.clone(), z.clone()) } else {true} &&
        if !b10.is_zero() && z >= b10 {
            witness(19, d.clone(), s.clone(), z.clone()) &&
            witness(23, d.clone(), s.clone(), z.clone())
        } else {true} &&
        if !b11.is_zero() && z >= b11 {
            witness(29, d.clone(), s.clone(), z.clone()) &&
            witness(31, d.clone(), s.clone(), z.clone()) &&
            witness(37, d.clone(), s.clone(), z.clone())
        } else {true} &&
        if !b12.is_zero() && z >= b12 { witness(41, d.clone(), s.clone(), z.clone()) } else {true}
    } else {
        let mut a = Z::two();
        while Z::try_from(3.pow_n(a.clone())).unwrap_or(z.clone()) < z {
            if !_witness(a.clone(), d.clone(), s.clone(), z.clone()) {return false}
            a = a + Z::one();
        }
        true
    }

}
