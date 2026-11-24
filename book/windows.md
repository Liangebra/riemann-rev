---
jupytext:
  text_representation:
    extension: .md
    format_name: myst
    format_version: 0.13
kernelspec:
  display_name: Python 3
  language: python
  name: python3
---

# One interval for all exceptional twists: `window1` and ultrametric separation

The cohomological window ({ref}`comp-cohomology`) must hold at **every** point of an interval
$[Y,Y^2]$. The archive finds such an interval in two steps that are easy to compute with: an
ultrametric argument shows that only finitely many twists can be exceptional, and a real-variable
induction (`UpperTheory.V.Win.window1`, kernel-checked at the archive pin) finds an interval avoiding
all of them. This notebook runs both on the book's example, tests the quantitative bound of the lemma
on many random instances in exact rational arithmetic, and checks the separation lemma by brute
force.

```{code-cell} ipython3
:tags: [remove-cell]
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, '_lib')
sys.path.insert(0, '../scripts')
import bookdata as bd
import rhlib
import inspect
import random
from fractions import Fraction as F
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle
bd.plot_style()
P = bd.PALETTE
fw = bd.facts()['windows']
ax_rep = bd.axioms()['declarations']
```

## The lemma

Given finitely many starting points $a$, a ratio $B\ge1$ and $U>0$, find $[y,2y]\subset[0,U]$ that meets
none of the half-open intervals $[a,Ba)$, with $y\ge U/(2^{R+2}B^R)$ when there are $R$ starting
points. The induction: if no start lies in $(U/2B,U]$, take $y=U/2$ (any $a\le u\in[y,2y]$ then has
$Ba\le U/2\le u$); otherwise delete one such start $a_0$ and solve the problem below $U'=U/2B$ — the
new interval lies below $a_0$, so it avoids $[a_0,Ba_0)$ too. Each deletion costs a factor $2B$. In
`rhlib` it reads:

```{code-cell} ipython3
print(inspect.getsource(rhlib.window1))
```

## The book's example

With cohomology cutoff $C_t=2$, $\eta=1$ (so $B=C_t/\eta=2$), $X=2^{128}$ and exceptional twists
$2^{16}$ and $2^{180}$: in base-2 logarithms $U=128$ and the starts are $a=\log_2h/C_t$.

```{code-cell} ipython3
ex = fw['example']
Ct, eta = F(ex['Ct']), F(ex['eta'])
B = Ct / eta
U = F(128)
twists_log2 = [F(16), F(180)]
starts = [t / Ct for t in twists_log2]
trace = []
def window1_traced(starts, B, U):
    live = [a for a in starts if U / (2 * B) < a <= U]
    trace.append((U, sorted(live)))
    if not live:
        return (U / 2, U)
    a0 = max(live)
    return window1_traced([a for a in starts if a != a0], B, U / (2 * B))
y, y2 = window1_traced(starts, B, U)
for ceiling, live in trace:
    print(f"ceiling {ceiling}: starts in ({ceiling / (2 * B)}, {ceiling}] = {[str(a) for a in live]}")
print(f"interval [y, 2y] = [{y}, {y2}]  →  [Y, Y²] = [2^{y}, 2^{y2}]")
assert (y, y2) == rhlib.window1([float(a) for a in starts], float(B), float(U))
assert [float(a) for a in starts] == ex['starts'] and [float(y), float(y2)] == ex['interval_log2']
assert ex['X'] == '2^128' and ex['twists'] == ['2^16', '2^180'] and ex['interval'] == [f'2^{y}', f'2^{y2}']
assert rhlib.avoids(y, starts, B)
```

On $[2^{16},2^{32}]$ the condition "$h\le x^{C_t}\Rightarrow h\le x^{\eta}$" holds for both twists at every
point. Here $C_t=2$ and $\eta=1$ (the values of the example). The first twist, $2^{16}$, is at most $x=x^{\eta}$ for
every $x\ge2^{16}$, so the conclusion holds; the second, $2^{180}$, exceeds $x^{C_t}\le(2^{32})^2$, so the premise
fails. The grid checks this example numerically:

```{code-cell} ipython3
assert (Ct, eta) == (2, 1) and twists_log2 == [16, 180] and (y, y2) == (16, 32)   # the values named in the text above
grid = [y + (y2 - y) * F(j, 1600) for j in range(1601)]
for u in grid:
    for h in twists_log2:                          # log2 of the twist
        assert (not h <= Ct * u) or h <= eta * u  # h <= x^Ct  implies  h <= x^eta
print(f"checked {len(grid) * len(twists_log2):,} (point, twist) pairs on [2^{y}, 2^{y2}]")
```

```{code-cell} ipython3
:tags: [remove-cell]
bd.glue('n_pairs', f"{len(grid) * len(twists_log2):,}")
```

```{code-cell} ipython3
:tags: [remove-input]
fig, ax = plt.subplots(figsize=(9, 2.9))
for a in starts:
    ax.add_patch(Rectangle((float(a), 0.62), float(B * a - a), 0.26, color=P['arith'], alpha=0.85))
    ax.text(float(a + B * a) / 2, 0.93, f"[{a}, {B * a})", ha='center', va='bottom', fontsize=8.5, color=P['arith'])
ax.add_patch(Rectangle((float(y), 0.28), float(y2 - y), 0.26, color=P['ok'], alpha=0.9))
ax.text(float(y2) + 3, 0.41, f"[{y}, {y2}]  →  [Y, Y²] = [2^{y}, 2^{y2}]", va='center', fontsize=9,
        color=P['ok'], fontweight=bd.SEMIBOLD)
for i, (ceiling, live) in enumerate(trace):
    ax.plot([0, float(ceiling)], [0.12 - 0.08 * i] * 2, color=P['muted'], lw=2)
    ax.plot([float(ceiling)], [0.12 - 0.08 * i], 'o', color=P['muted'], ms=4)
    ax.text(float(ceiling) + 2, 0.12 - 0.08 * i, f"ceiling {ceiling}", va='center', fontsize=8, color=P['muted'])
ax.set_xlim(0, 200)
ax.set_ylim(-0.1, 1.1)
ax.set_yticks([])
ax.set_xlabel('u = log₂ x   (forbidden: [a, Ba) for each exceptional twist, a = log₂ h / C_t)')
ax.grid(axis='y', visible=False)
ax.set_title('Two forbidden logarithmic intervals and the interval the induction returns', loc='left')
plt.show()
```

## The quantitative bound, on random instances

The archive's bound $y\ge U/(2^{R+2}B^R)$ is tested on random instances with exact rational data:
$R\le8$ random starts in $(0,U]$, $B$ from a list of rationals, $U$ up to $10^6$. For every instance
the returned interval must lie in $[0,U]$, avoid all forbidden intervals, and satisfy the bound.

```{code-cell} ipython3
rng = random.Random(20261120)
N = 20_000
worst_ratio, worst_R = None, None
Bs = [F(1), F(3, 2), F(2), F(3), F(7), F(10)]
for _ in range(N):
    R = rng.randint(0, 8)
    Bq = rng.choice(Bs)
    Uq = F(rng.randint(1, 10**6), rng.randint(1, 50))
    st = [Uq * F(rng.randint(1, 10**6), 10**6) for _ in range(R)]
    yq, y2q = rhlib.window1(st, Bq, Uq)
    assert y2q == 2 * yq and 0 < yq and y2q <= Uq and rhlib.avoids(yq, st, Bq)
    ratio = yq / (Uq / (2 ** (R + 2) * Bq ** R))
    assert ratio >= 2
    if worst_ratio is None or ratio < worst_ratio:
        worst_ratio, worst_R = ratio, R
print(f"{N:,} random instances: all intervals valid; smallest y / bound = {float(worst_ratio):.3f} (R = {worst_R})")
```

The induction returns $y=U/[2(2B)^d]$ after $d$ deletions. Since $d\le R$, every run gives at least
twice the stated lower bound. The following starts force all $R$ deletions:

```{code-cell} ipython3
for Bq in (F(1), F(2), F(7)):
    for R in (1, 4, 8):
        Uq = F(10**6)
        st = [Uq / (2 * Bq) ** i * F(1001, 1000) / (2 * Bq) for i in range(R)]
        yq, _ = rhlib.window1(st, Bq, Uq)
        bound = Uq / (2 ** (R + 2) * Bq ** R)
        assert rhlib.avoids(yq, st, Bq) and yq / bound == 2
        print(f"B = {str(Bq):>2}, R = {R}:  y / bound = {float(yq / bound):.3f}")
```

```{code-cell} ipython3
:tags: [remove-cell]
bd.glue('N_random', f"{N:,}")
bd.glue('worst_ratio', f"{float(worst_ratio):.3f}")
```

In all {glue:text}`N_random` random instances the interval is valid and the smallest ratio of $y$
to the archive's bound is {glue:text}`worst_ratio`; in the adversarial instances the ratio is
exactly $2$. To see what can be guaranteed by *any* choice of window, fix $B>1$ and $R\ge1$.
For a positive start $a$, the window $[y,2y]$ meets $[a,Ba)$ exactly when $a/2\le y<Ba$.
Put $L=U/[2(2B)^R]$ and choose starts $a_i=2(1+\delta)L(2B)^i$ for $0\le i<R$ and $\delta>0$.
Their forbidden ranges for $y$ join end to end and cover
$[(1+\delta)L,(1+\delta)U/2)$. Since $y\le U/2$, every valid window has $y<(1+\delta)L$.
Taking $\delta$ arbitrarily small proves that $L$ is the best uniform guarantee for $B>1$.
When $B=1$, all the forbidden intervals are empty and $y=U/2$ always works, even if the induction deletes starts.

After exponentiation, $[Y,Y^2]$ lies in
$[X^{1/J},X]$ with $J=2^{R+2}B^R=4(2B)^R$: enormous, but fixed before $X$ and the auxiliary primes
are chosen, which is all the argument needs.

## Ultrametric separation

A twist $1\le h\le Z$ is exceptional for an $\ell$-adic centre $s$ if $|h-s|_\ell<\ell^{-k}$ with
$k=\lfloor\log_\ell Z\rfloor$, i.e. if $\ell^{k+1}\mid h-s$. Since $\ell^{k+1}>Z$, each centre has at most
one exceptional twist.

```{code-cell} ipython3
um = fw['ultrametric']
exc = rhlib.ultrametric_exceptions(um['ell'], um['Z'], um['center'])
weak = [h for h in range(1, um['Z'] + 1) if (h - um['center']) % um['ell'] ** 3 == 0]
print(f"ℓ = {um['ell']}, Z = {um['Z']}, centre {um['center']}:  exceptional twists {exc};"
      f"  with ≤ instead of <: {weak}")
assert exc == um['exceptional'] and weak == um['if_mod_27']
```

The same holds for every centre, prime and cutoff; a brute-force check over small parameters (the
centre only matters modulo $\ell^{k+1}$):

```{code-cell} ipython3
count = 0
for ell in (2, 3, 5, 7, 11):
    for Z in range(1, 400):
        k = 0
        while ell ** (k + 1) <= Z:
            k += 1
        mod = ell ** (k + 1)
        assert mod > Z
        for s in range(mod):
            hits = [h for h in range(1, Z + 1) if (h - s) % mod == 0]
            assert len(hits) <= 1
            count += 1
print(f"{count:,} (ℓ, Z, centre) triples: never more than one exceptional twist per centre")
```

```{code-cell} ipython3
:tags: [remove-cell]
bd.glue('n_triples', f"{count:,}")
assert ax_rep['Atlas.Separation.at_most_one_per_centre'] == ['propext', 'Quot.sound']
assert ax_rep['Atlas.Separation.eq_of_dvd_sub'] == ['propext', 'Quot.sound']
from IPython.display import Markdown
bd.glue('sep_axioms', Markdown(', '.join(f"`{a}`" for a in ax_rep['Atlas.Separation.at_most_one_per_centre'])))
```

The integer core of this argument — two integers in $[1,Z]$ congruent modulo some $m>Z$ are equal —
is proved in this repository's Lean library (`Atlas.Separation.at_most_one_per_centre`, quoted in
{ref}`lean-separation`), including the example above and the failure of the weak inequality. Its
transitive axioms, from `verification/logs/axioms.json`, are {glue:md}`sep_axioms`.
