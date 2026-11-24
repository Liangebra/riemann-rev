"""Shared numerics and exact checks for the atlas, the book and the figures.

Everything here is computed from definitions; nothing is a recalled constant except
Euler's constant gamma (numpy.euler_gamma) and pi.

Contents
--------
* ``centered_prime_sum`` -- the archive's statistic
      G(y) = sum_{n<=y} Lambda(n) (y/n - 1) - y log y + (1 + gamma) y
  evaluated exactly (in floating point) from a sieve.
* ``zeta_em`` / ``zeta_zeros`` -- zeta on the critical line by Euler--Maclaurin summation
  and its first zeros by bisection on Hardy's Z-function (used only for illustrations).
* ``spotlight`` -- the moment kernel u^k e^{-sigma u}/k! of the localized Landau argument.
* ``window1`` -- the archive's real-variable interval lemma (UpperTheory.V.Win.window1),
  implemented recursively exactly as the induction in the reading.
* ``behrend_example`` -- the six-point digit sphere and its 1,440 relation checks.
* ``budget_rows`` -- the four-term exponent budget of the finite comparison.

Run ``python3 scripts/rhlib.py`` for a self-test (assertions only, no files written).
"""
from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
from itertools import permutations, product

import numpy as np

EULER_GAMMA = float(np.euler_gamma)
LOG_2PI = math.log(2 * math.pi)
# Under RH: sum over nontrivial zeros of 1/|rho|^2 = sum 1/(rho(1-rho)) = 2 + gamma - log(4 pi).
RH_BAND = 2.0 + EULER_GAMMA - math.log(4 * math.pi)


# --------------------------------------------------------------------------------------
# The centered prime sum G(y)
# --------------------------------------------------------------------------------------
def von_mangoldt_table(n_max: int) -> np.ndarray:
    """Lambda(n) for 0 <= n <= n_max (Lambda(0) = Lambda(1) = 0)."""
    lam = np.zeros(n_max + 1, dtype=np.float64)
    sieve = np.ones(n_max + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n_max ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p:: p] = False
    primes = np.nonzero(sieve)[0]
    for p in primes:
        lp = math.log(p)
        q = int(p)
        while q <= n_max:
            lam[q] = lp
            q *= int(p)
    return lam


@dataclass
class PrimeSums:
    """Cumulative sums S0(n)=sum_{m<=n} Lambda(m), S1(n)=sum_{m<=n} Lambda(m)/m."""

    n_max: int
    psi: np.ndarray   # psi[n] = sum_{m<=n} Lambda(m)
    a: np.ndarray     # a[n]   = sum_{m<=n} Lambda(m)/m

    @classmethod
    def build(cls, n_max: int) -> "PrimeSums":
        lam = von_mangoldt_table(n_max)
        idx = np.arange(n_max + 1, dtype=np.float64)
        idx[0] = 1.0
        # math.fsum-quality is unnecessary here; float64 cumulative sums are accurate to ~1e-9 relative.
        return cls(n_max, np.cumsum(lam), np.cumsum(lam / idx))

    def G(self, y: np.ndarray | float) -> np.ndarray:
        """G(y) = y * A(floor y) - psi(floor y) - y log y + (1+gamma) y, for 1 <= y <= n_max."""
        y = np.asarray(y, dtype=np.float64)
        n = np.floor(y).astype(np.int64)
        if np.any(n > self.n_max) or np.any(y < 1):
            raise ValueError("y outside the sieved range")
        return y * self.a[n] - self.psi[n] - y * np.log(y) + (1.0 + EULER_GAMMA) * y


def centered_prime_sum_naive(y: float) -> float:
    """Direct definition, for testing: sum_{1<=n<=y} Lambda(n)(y/n-1) - y log y + (1+gamma) y."""
    n_max = int(math.floor(y))
    lam = von_mangoldt_table(max(n_max, 1))
    s = math.fsum(lam[n] * (y / n - 1.0) for n in range(1, n_max + 1))
    return s - y * math.log(y) + (1.0 + EULER_GAMMA) * y


# --------------------------------------------------------------------------------------
# Zeta on the critical line (Euler--Maclaurin) and its first zeros
# --------------------------------------------------------------------------------------
# Bernoulli numbers B_2, B_4, ..., B_20 as exact fractions (computed, see _bernoulli()).
def _bernoulli(m: int) -> list[Fraction]:
    """B_0..B_m by the standard recurrence sum_{k=0}^{n} C(n+1,k) B_k = 0."""
    B = [Fraction(1)]
    for n in range(1, m + 1):
        s = sum(Fraction(math.comb(n + 1, k)) * B[k] for k in range(n))
        B.append(-s / (n + 1))
    return B


_B = _bernoulli(30)


def zeta_em(s: complex, N: int = 40, K: int = 12) -> complex:
    """zeta(s) by Euler--Maclaurin with N terms and K Bernoulli corrections (Re s > -2K+1)."""
    total = sum(n ** (-s) for n in range(1, N))
    total += N ** (1 - s) / (s - 1) + 0.5 * N ** (-s)
    # sum_{k=1}^{K} B_{2k}/(2k)! * s(s+1)...(s+2k-2) * N^{-s-2k+1}
    rising = s  # s(s+1)...(s+2k-2) for k=1 is s
    for k in range(1, K + 1):
        if k > 1:
            rising *= (s + 2 * k - 3) * (s + 2 * k - 2)
        total += float(_B[2 * k]) / math.factorial(2 * k) * rising * N ** (-s - 2 * k + 1)
    return total


def rs_theta(t: float) -> float:
    """Riemann--Siegel theta function by its asymptotic series (accurate for t >= 10)."""
    return (t / 2) * math.log(t / (2 * math.pi)) - t / 2 - math.pi / 8 + 1 / (48 * t) \
        + 7 / (5760 * t ** 3) + 31 / (80640 * t ** 5) + 127 / (430080 * t ** 7)


def hardy_z(t: float) -> float:
    """Hardy's Z(t) = exp(i theta(t)) zeta(1/2 + i t), real for real t."""
    n_terms = max(30, int(abs(t) / 3) + 1)   # keeps |s|/(2 pi N) < 1/2, so the EM tail converges fast
    z = complex(math.cos(rs_theta(t)), math.sin(rs_theta(t))) * zeta_em(complex(0.5, t), N=n_terms)
    return z.real


def zeta_zeros(count: int, t0: float = 10.0, step: float = 0.05) -> list[float]:
    """Ordinates of the first ``count`` zeros of Z(t) above t0, by scanning and bisection.

    The scan step is small compared with the zero spacing in the illustrated range
    (t < 250), so sign changes are not missed there; the result is checked against the
    Riemann--von Mangoldt counting function in the self-test.
    """
    zeros: list[float] = []
    t, zt = t0, hardy_z(t0)
    while len(zeros) < count:
        t2 = t + step
        z2 = hardy_z(t2)
        if zt == 0.0 or zt * z2 < 0:
            a, b, fa = t, t2, zt
            for _ in range(60):
                m = 0.5 * (a + b)
                fm = hardy_z(m)
                if fa * fm <= 0:
                    b = m
                else:
                    a, fa = m, fm
            zeros.append(0.5 * (a + b))
        t, zt = t2, z2
    return zeros


def explicit_formula_G(y: np.ndarray, gammas: list[float]) -> np.ndarray:
    """log(2 pi) - 2 Re sum_{gamma} y^rho/(rho(rho-1)), rho = 1/2 + i gamma (RH assumed for the
    plotted zeros, which are on the line by construction of Z), trivial-zero terms dropped."""
    y = np.asarray(y, dtype=np.float64)
    acc = np.zeros_like(y)
    ly = np.log(y)
    for g in gammas:
        rho = complex(0.5, g)
        c = 1.0 / (rho * (rho - 1.0))
        acc += 2.0 * np.real(c * np.exp(rho * ly))
    return LOG_2PI - acc


# --------------------------------------------------------------------------------------
# The spotlight kernel of the localized Landau argument
# --------------------------------------------------------------------------------------
def spotlight(u: np.ndarray, k: int, sigma: float) -> np.ndarray:
    """u^k e^{-sigma u}/k!, computed in logs; its maximum is at u = k/sigma."""
    u = np.asarray(u, dtype=np.float64)
    with np.errstate(divide="ignore"):
        logv = k * np.log(u) - sigma * u - math.lgamma(k + 1)
    return np.exp(logv)


def spotlight_mass_in(U: float, delta: float, k: int, sigma: float, grid: int = 20000) -> float:
    """Fraction of the kernel's total mass inside [U, (1+delta) U] (numerical quadrature)."""
    # Total mass of u^k e^{-sigma u}/k! over (0, inf) is sigma^{-(k+1)}.
    u = np.linspace(U, (1 + delta) * U, grid)
    inside = np.trapezoid(spotlight(u, k, sigma), u)
    return float(inside * sigma ** (k + 1))


# --------------------------------------------------------------------------------------
# The interval lemma window1 (finitely many forbidden logarithmic intervals [a, B a))
# --------------------------------------------------------------------------------------
def window1(starts: list[float], B: float, U: float) -> tuple[float, float]:
    """Return (y, 2y) with [y, 2y] inside [0, U] avoiding every [a, B a), following the
    induction of UpperTheory.V.Win.window1:

    * if no start a lies in (U/(2B), U], take y = U/2 (then any a <= u in [y, 2y] has
      B a <= U/2 <= u, so u is not in [a, B a));
    * otherwise delete one such a0 and solve the problem below U' = U/(2B).

    Each deletion costs a factor 2B, hence y >= U / (2^(R+2) B^R) ... the archive's bound.
    """
    if B < 1 or U <= 0:
        raise ValueError("need B >= 1 and U > 0")
    live = [a for a in starts if U / (2 * B) < a <= U]
    if not live:
        return (U / 2, U)
    a0 = max(live)
    rest = [a for a in starts if a != a0]
    return window1(rest, B, U / (2 * B))


def avoids(y: float, starts: list[float], B: float) -> bool:
    """Return whether the closed window [y, 2y] misses every nonempty [a, B*a). A nonempty [a, B*a)
    meets [y, 2y] exactly when a <= 2y and y < B*a; it is empty when B*a <= a."""
    return all(B * a <= a or a > 2 * y or B * a <= y for a in starts)


def ultrametric_exceptions(ell: int, Z: int, center: int) -> list[int]:
    """Integers 1 <= h <= Z with |h - center|_ell < ell^{-k}, k = floor(log_ell Z),
    i.e. h == center (mod ell^{k+1})."""
    k = 0
    while ell ** (k + 1) <= Z:
        k += 1
    mod = ell ** (k + 1)
    return [h for h in range(1, Z + 1) if (h - center) % mod == 0]


# --------------------------------------------------------------------------------------
# Behrend digit spheres
# --------------------------------------------------------------------------------------
def behrend_example(S: int = 3, d: int = 3, L: int = 2, norm: int = 5):
    """Vectors in {0..d-1}^S with squared norm ``norm``, encoded in base 4 L d, and an
    exhaustive check that no three distinct encodings satisfy j(s2-s1) = i(s3-s1) with
    1 <= |i|, |j| <= L and i != j.  Returns (points, encodings, number_of_checks)."""
    base = 4 * L * d
    pts = [v for v in product(range(d), repeat=S) if sum(c * c for c in v) == norm]
    enc = [sum(c * base ** i for i, c in enumerate(reversed(v))) for v in pts]
    coeffs = [c for c in range(-L, L + 1) if c != 0]
    checks = 0
    for s1, s2, s3 in permutations(enc, 3):
        for i in coeffs:
            for j in coeffs:
                if i == j:
                    continue
                checks += 1
                if j * (s2 - s1) == i * (s3 - s1):
                    raise AssertionError(f"relation found: {s1},{s2},{s3},{i},{j}")
    return pts, enc, checks


# --------------------------------------------------------------------------------------
# The four-term exponent budget of the finite comparison (in units of epsilon)
# --------------------------------------------------------------------------------------
def budget_rows() -> list[dict]:
    """Exponents a + b*eps of the four contributions to B/Q, from the size hypotheses
    a_E <= 2xb, n/u <= 2 x^{eps/8}, x^{1/2-eps} <= m <= x^{1/2+eps/2},
    x m <= k <= n^2 x^{1/2-eps}, v <= n  (all exponents exact rationals)."""
    F = Fraction
    rows = [
        {"term": "a_E/(m b)", "coef": 2, "half": F(1, 2), "eps": F(1),
         "why": "a_E/(mb) <= 2x/m and m >= x^{1/2-eps}"},
        {"term": "a_E m/(b k)", "coef": 2, "half": F(0), "eps": F(0),
         "why": "x m <= k"},
        {"term": "2 (n/u) m x^eps", "coef": 4, "half": F(1, 2), "eps": F(1, 8) + F(1, 2) + F(1),
         "why": "n/u <= 2x^{eps/8}, m <= x^{1/2+eps/2}, the explicit x^eps"},
        {"term": "(v/u)(k/n^2) x^{2 eps}", "coef": 2, "half": F(1, 2), "eps": F(1, 8) - F(1) + F(2),
         "why": "v/u <= n/u <= 2x^{eps/8}, k/n^2 <= x^{1/2-eps}, the explicit x^{2eps}"},
    ]
    return rows


def balance_exponent(a: float) -> float:
    """max(1-a, a): the larger of the exponents of x/m and m when m = x^a."""
    return max(1.0 - a, a)


# --------------------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------------------
def _selftest() -> None:
    # G agrees with the naive definition.
    ps = PrimeSums.build(20000)
    for y in (2.0, 10.5, 97.3, 1000.0, 12345.6):
        assert abs(ps.G(y) - centered_prime_sum_naive(y)) < 1e-7 * max(1.0, y), y
    # The explicit-formula constant term.
    assert abs(LOG_2PI - 1.8378770664093453) < 1e-15
    # RH band constant 2 + gamma - log 4 pi.
    assert 0.0461 < RH_BAND < 0.0463, RH_BAND
    # First zeros (checked against the counting function N(T) = theta(T)/pi + 1 + S(T)).
    zs = zeta_zeros(10)
    assert 14.13 < zs[0] < 14.14 and 21.02 < zs[1] < 21.03, zs[:2]
    # Riemann--von Mangoldt: number of zeros up to T=50 is 10.
    assert sum(1 for z in zeta_zeros(12) if z < 50) == 10
    # window1 on the book's example: C_t=2, eta=1 -> B=2; X=2^128 -> U=128 (base-2 logs);
    # exceptional twists 2^16, 2^180 -> starts a = log2(h)/C_t = 8, 90.
    y, y2 = window1([8.0, 90.0], 2.0, 128.0)
    assert (y, y2) == (16.0, 32.0), (y, y2)
    assert avoids(y, [8.0, 90.0], 2.0)
    assert avoids(2, [3], 1)       # [3, 3) is empty
    assert not avoids(2, [4], 2)   # the window includes 4
    assert avoids(2, [1], 2)       # [1, 2) excludes 2
    # Random stress test of the lemma and of the archive's lower bound U/(2^(R+2) B^R).
    import random
    rng = random.Random(20261120)
    for _ in range(2000):
        R = rng.randint(0, 6)
        B = rng.choice([1.0, 1.5, 2.0, 3.0, 7.0])
        U = rng.uniform(1.0, 1e6)
        starts = [rng.uniform(1e-3, U) for _ in range(R)]
        y, _ = window1(starts, B, U)
        assert avoids(y, starts, B) and 2 * y <= U
        assert y >= U / (2 ** (R + 2) * B ** R) * (1 - 1e-12)
    # Ultrametric separation example: ell=3, Z=80, center 1 -> only h=1 (mod 81).
    assert ultrametric_exceptions(3, 80, 1) == [1]
    # Allowing equality (mod 27) would also admit 28 and 55.
    assert [h for h in range(1, 81) if (h - 1) % 27 == 0] == [1, 28, 55]
    # Behrend example.
    pts, enc, checks = behrend_example()
    assert sorted(enc) == [26, 49, 578, 624, 1153, 1176], sorted(enc)
    assert checks == 1440 and len(pts) == 6
    # Budget: worst exponent 1/2 + 13/8 eps.
    rows = budget_rows()
    assert max(r["eps"] for r in rows if r["half"] == Fraction(1, 2)) == Fraction(13, 8)
    assert sum(r["coef"] for r in rows) == 10
    # Spotlight peaks at k/sigma.
    u = np.linspace(1, 300, 300000)
    v = spotlight(u, 150, 1.0)
    assert abs(u[np.argmax(v)] - 150.0) < 0.01
    print("rhlib self-test: all assertions passed")


if __name__ == "__main__":
    _selftest()
