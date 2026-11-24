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

# The arithmetic supply

```{code-cell} ipython3
:tags: [remove-cell]
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, '_lib')
import bookdata as bd

m = bd.model()
fx = bd.facts()
expected = {11: 'The cohomological window', 12: 'Auxiliary primes and Behrend towers', 13: 'The Galois row',
            14: 'Seven inputs at the decisive call'}
assert {c['n']: c['title'] for c in bd.comps('arith')} == expected
# constants and examples quoted below
coh = bd.comp('cohomology')
assert 'x^{401}' in coh['statement'] and '\\sqrt{\\exp(x^{\\varepsilon})}' in coh['statement']
assert 'J=4(2B)^R' in coh['explanation'][1] and 'U/(2^{R+2}B^R)' in coh['explanation'][1]
ex = fx['windows']['example']
assert (ex['Ct'], ex['eta'], ex['B'], ex['X']) == (2, 1, 2, '2^128')
assert ex['twists'] == ['2^16', '2^180'] and ex['starts'] == [8.0, 90.0] and ex['interval'] == ['2^16', '2^32']
um = fx['windows']['ultrametric']
assert (um['ell'], um['Z'], um['center'], um['exceptional'], um['if_mod_27']) == (3, 80, 1, [1], [1, 28, 55])
be = fx['behrend']
assert (be['S'], be['d'], be['L'], be['norm'], be['base'], be['checks']) == (3, 3, 2, 5, 24, 1440)
pr = bd.comp('primes')
assert 'z=Y^{\\varepsilon/5}' in pr['explanation'][0]
assert 'q\\equiv3\\ (8)' in pr['statement'] and 'd\\equiv7\\ (16)' in pr['statement']
assert 'y^{1/2+\\varepsilon/2}' in pr['statement']
seven = bd.node('seven')['assumptions']
assert len(seven) == 7 and len(m['audit']) == 5
assert {a['node'] for a in m['audit']} >= {'row-prod', 'definite'}
bd.glue('n_seven_mod', len(bd.node('seven')['assumptions']))
gal = bd.comp('galois')
import re
bd.glue('behrend_checks', f"{be['checks']:,}")
bd.glue('behrend_enc', ', '.join(str(e) for e in be['encodings']))
```

```{code-cell} ipython3
:tags: [remove-input]
bd.show(f"{bd.stratum_badge('arith')} {bd.esc(bd.stratum('arith')['blurb'])}")
```

This stratum is where the deep arithmetic lives: Galois representations attached to automorphic
representations, theta correspondences, and a bound for Galois cohomology along cyclotomic towers
that the announcement describes as a weakening of Vandiver's conjecture. It is also where the two
premises of the second verified cut, `TopG` and `VWinAt ψ 401`, are produced. Most of it is, in the
imported record, **source-read** rather than separately replayed; the kernel-checked steps are
implications with explicit premises:

```{code-cell} ipython3
:tags: [remove-input]
# declarations of this stratum (component Lean lists and blueprint nodes) that a native scope checked
arith = set()
for c in bd.comps('arith'):
    arith |= {l['name'].split()[0] for l in c['lean']}
    arith |= {bd.node(n)['declaration'] for n in c['nodes'] if bd.node(n)['declaration']}
match = lambda name: any(name == a or name.endswith('.' + a) for a in arith)
rows = []
for sc in bd.scopes():
    if sc['lean_version'] == '4.35.0':
        continue
    hits = [d['name'] for d in sc['declarations'] if match(d['name'])]
    if hits:
        rows.append(f"* **{bd.esc(sc['title'])}** ({sc['original_project_module_count']:,} original modules): "
                    + ", ".join(f"`{h}`" for h in hits) + f". *Premises:* {bd.esc(sc['assumption'])} "
                    f"*Conclusion:* {bd.esc(sc['conclusion'])}")
assert rows
bd.show("\n".join(rows))
```

(comp-cohomology)=
## 11 · The cohomological window

```{code-cell} ipython3
:tags: [remove-input]
bd.show(bd.card('cohomology'))
```

### The quantity that is bounded

For a number field $E$ in a prescribed family, a prime $\ell$ and a twist $h$, let $s_{\ell,h}(E)$ be
the $\mathbf Z_\ell$-length of the locally trivial part of $H^1$ of $E$ with coefficients in
$\mathbf Q_\ell/\mathbf Z_\ell$ twisted by the $h$-th power of the inverse cyclotomic character (the
archive's `shaLen`). The predicate `VVle E t B` asks that all these lengths be **finite** for
$1\le h<t$ — a separate clause, because converting an extended natural number to a natural number
sends $\infty$ to $0$ in Lean — and that $\sum_{\ell\in S}\log\ell\sum_{1\le h<t}s_{\ell,h}(E)\le B$ for
every finite set of primes $S$. The window `VWinAt ψ 401` asks for this with $t=\lfloor x^{401}\rfloor$
and $B=\sqrt{\exp(x^{\varepsilon})}$, at **every** real $x$ of an interval $[Y,Y^2]$, uniformly over the
fields attached to $\psi$, the layer $e(x)$ and the auxiliary primes $q,d$. The bound is enormous;
what matters is that it is uniform, finite, and sub-exponential in the scale that the
estimate stratum can absorb.

### How many twists can be expensive

In one tower the relevant length is a cokernel length for a twisted operator, and an $\ell$-adic
determinant estimate supplies centres $s_1,\dots,s_{R'}$, the same for every twist $h$ and every
layer $m$, with

$$
\operatorname{twLen}(h,m)\le\sum_{i=1}^{R'}\big(\max(m,j_0)+c+v_\ell(s_i-h)\big).
$$

A twist $1\le h\le Z$ is *exceptional* if $|h-s_i|_\ell<\ell^{-k}$ for some $i$, where
$k=\lfloor\log_\ell Z\rfloor$. Each centre accounts for at most one exceptional twist: two of them would
satisfy $\ell^{k+1}\mid a-b$ with $0<|a-b|<Z<\ell^{k+1}$. So there are at most $R$ exceptions however
large $Z$ is — this integer core is proved in this repository's Lean file `Atlas/Separation.lean`
(see {ref}`lean-separation`). The strict inequality matters: for $\ell=3$, $Z=80$ and centre $1$ only
$h=1$ is exceptional, while with "$\le$" the twists $28$ and $55$ would also qualify
({doc}`windows`). The total count $R=R_0(M)+\sum_{\ell\in B'}R_\ell(L_\ell)$ is fixed before the
auxiliary primes are chosen; the rank bounds behind it use the archive's Ferrero–Washington
formulation.

### Why one interval survives

Put $\eta=\varepsilon/(2C_K)$, $u=\log x$, $a=(\log h)/C_t$ and $B=C_t/\eta$ with $C_t=401$. An exceptional
twist $h$ is harmless at $x$ if $h\le x^{C_t}\Rightarrow h\le x^{\eta}$, and this fails exactly for
$u\in[a,Ba)$. The real-variable lemma `UpperTheory.V.Win.window1` (kernel-checked) finds $[y,2y]$
inside $[0,U]$, $U=\log X$, missing all $R$ forbidden intervals, with $y\ge U/(2^{R+2}B^R)$: if no
start lies in $(U/2B,U]$ take $y=U/2$; otherwise delete one such start and recurse below
$U/2B$. Exponentiating gives $[Y,Y^2]\subset[X^{1/J},X]$ with $J=4(2B)^R$. In the computed example
($C_t=2$, $\eta=1$, $X=2^{128}$, exceptional twists $2^{16}$ and $2^{180}$) the induction deletes
the start $90$, lowers the ceiling from $128$ to $32$ and returns $[Y,Y^2]=[2^{16},2^{32}]$; a
randomized test of the lower bound is in {doc}`windows`.

On the surviving interval, unexceptional twists have valuations at most $\lfloor\log_\ell Z\rfloor$, and
each exceptional twist that is still active is small ($h\le x^{\eta}$) and is handled by a fixed-layer
estimate; the choice of $\eta$ keeps that secondary cost at $x^{O(\varepsilon)}$. The positive part,
the negative part and the prime $2$ are then evaluated on the same field at the same $x$, and an
elementary comparison absorbs their sum into $\sqrt{\exp(x^\varepsilon)}$.

:::{dropdown} From the two tower bounds to a uniform twist sum

The tower estimates have different uses. The first controls almost every twist at once; the
second controls the exceptional twists by comparison with a reference layer. The latter is
where Lemma K enters, and the logarithmic window is what makes its cost affordable.

**A bound at a point.** Write $L_m/L_0$ for a layer of degree $\ell^m$,
$j=\lfloor\log_\ell R\rfloor+3$ (using the integer logarithm, with value $0$ at $R=0$), and $s(h,m)=s_{\ell,h}(L_m)$.
The two estimates from the tower give an exceptional set $T_Z\subset\{1,\ldots,Z\}$,
$|T_Z|\le R$, and

$$
\begin{aligned}
 s(h,m)&\le R(\max(m,j)+c+\lfloor\log_\ell Z\rfloor)
                  &&(h\notin T_Z,\ 1\le h\le Z),\\
 s(h,m)&\le v(h,j)+R(m-j)_+
                  &&(h\ge1).
\end{aligned}
$$

Here $v(h,j)=\operatorname{length}_{\mathbf Z_\ell}H^2(G_{L_j,S},
\mathbf Z_\ell(h+1))$, with $S$ the places over $\ell$, and $(m-j)_+=\max(m-j,0)$.
The integer $c$ comes from the centres estimate: $L_0$ contains a primitive
$\ell^c$-th root. These are the contracts FirstBound and SecondBound, not an
additional claim that the determinant bound is finite at a centre.

Suppose $L_0$ contains a primitive $\ell$-th root for odd $\ell$, or a primitive
fourth root for $\ell=2$. Then the reference layer $L_j$ is totally imaginary and
inherits the required roots. Let $n=[L_j:\mathbf Q]$ and $D=|\operatorname{disc}L_j|$.
The archive's Lemma K, with constant $C_K>0$, gives finiteness of the group defining
$v(h,j)$ and

$$
 v(h,j)\log\ell
 \le \exp\big((2hn)^{C_K}\log(2D)\big).
$$

Indeed a finite $\mathbf Z_\ell$-module of length $v$ has order $\ell^v$.
Since $\log\ell>1/2$, this yields the factor $2$ in the length bound.

Fix $X>1$, $C_t\ge1$, $Z=\lfloor X^{C_t}\rfloor$ and
$\eta=\varepsilon/(2C_K)$. Suppose that $1\le x\le X$, that $x$ satisfies
the window condition for $T_Z$, and that

$$
 n\le n_0,\qquad
 \log(2D)\le c_0x^{\varepsilon/4},\qquad
 m\le a(1+\log x).
$$

If $1\le h\le x^{C_t}$ is exceptional, the window condition gives
$h\le x^\eta$. Consequently

$$
 (2hn)^{C_K}\log(2D)
 \le (2n_0)^{C_K}c_0 x^{3\varepsilon/4}.
$$

This is the source of the exponent $3\varepsilon/4$: the twist costs
$\varepsilon/2$, the discriminant costs $\varepsilon/4$, and the reference-layer
degree is bounded independently of $x$. For a nonexceptional twist the
first tower estimate applies, since $h\le Z$. Combining the two cases,
every active length is finite, and

$$
 s(h,m)\le R(m+j+c+\lfloor\log_\ell Z\rfloor)
          +2\exp\big(B_0x^{3\varepsilon/4}\big),
 \qquad B_0=(2n_0)^{C_K}c_0.
$$

The separate finiteness conclusion is needed before converting extended lengths
to ordinary integers.

**The sum over twists.** The lower endpoint $X^{1/J}\le x$ gives
$\log X\le J\log x$. Since $\log\ell>1/2$,

$$
 \lfloor\log_\ell Z\rfloor\le 2C_tJ\log x.
$$

For a uniform bound $c\le c_1$, take
$C=R(a+j+c_1+2C_tJ)+1+B_0$. The preceding inequality implies

$$
 s(h,m)+1\le C(1+\log x)+2\exp(Cx^{3\varepsilon/4}).
$$

The extra unit also accommodates the comparison with the fields in the
two-adic part of the window. For an integer cutoff $t(x)\le x^{C_t}$,
the sum over $1\le h<t(x)$ is bounded by $x^{C_t}$ times this expression.
Its logarithm is $O(\log x+x^{3\varepsilon/4})=o(x^{4\varepsilon/5})$
as $x\to\infty$, with the parameters fixed. Thus, after increasing the
threshold in $x$,

$$
 \sum_{1\le h<t(x)}s(h,m)\le \exp(x^{4\varepsilon/5}).
$$

The difference $4\varepsilon/5-3\varepsilon/4=\varepsilon/20>0$ absorbs
both the constants and the number of twists. No extra factor proportional
to the number of exceptional twists is needed at this stage: the window
condition has made the *pointwise* estimate valid for every active twist.

**Uniformity in the auxiliary primes.** For a fixed odd coefficient prime
in the finite auxiliary set, the reference layer of its fixed base field
has fixed degree and discriminant. For $\ell=2$, the base field depends on
$q,d$. The hypothesis TwoBase bounds its degree by $8\deg M$ and embeds
it in $\mathbf Q(\zeta_{4M.mqd})$, with the notation for the abelian field
$M$ used by the archive. One must bound the degree and discriminant of
the reference layer independently of those primes.

Here is the elementary conductor argument. More generally suppose
$L_0\subset\mathbf Q(\zeta_{N_0P})$, $[L_0:\mathbf Q]\le n_1$,
where $P$ varies. The layer $L_j$ is generated over $L_0$ by roots of
unity of order $\ell^k$ for some $k$. It embeds in
$\mathbf Q(\zeta_{\ell^kN_0P})$. Since $\varphi(\ell^k)\ge \ell^k/2$
and $L_j$ contains these roots,

$$
 [L_j:\mathbf Q]\le n_1\ell^j,\qquad
 \ell^k\le 2[L_j:\mathbf Q].
$$

For any subfield $E$ of $\mathbf Q(\zeta_N)$ the discriminant tower formula
and the cyclotomic discriminant formula give
$|\operatorname{disc}E|\le N^{[E:\mathbf Q]}$: the absolute norm of the
relative different is at least one, and the cyclotomic discriminant has
absolute value at most $N^{\varphi(N)}$. Taking
$n_0=(n_1+1)\ell^j$, it follows that

$$
 \log(2|\operatorname{disc}L_j|)
 \le \log 2+n_0\log(2n_0N_0)+n_0\log P.
$$

In the two-adic application $P=qd$, $N_0=4M.m$, and the auxiliary-prime
hypothesis gives $\log P\le X^{\varepsilon/(4J)}\le x^{\varepsilon/4}$.
As $x\ge1$, the constant term is absorbed by the same power of $x$.
Hence the required $c_0$ and $n_0$ depend on the base degree bound and
the fixed reference-layer index, not on $q,d$. The bound on $c$ follows
from the same totient inequality in $L_0$. The moving layer has
$m\le e(x)+2$; the admitted upper bound on $2^{e(x)}$ gives the required
logarithmic bound on $m$. The comparison in TwoBase transfers the result
to the actual field, with at most one extra unit of length per twist.

This is why a bound on each individual tower is not enough. The rank for
the moving two-adic tower is chosen uniformly in $q,d$, and the rank for
each fixed odd-prime tower is chosen before the window. Their sum bounds
the cardinality of the union of exceptional sets. With $J$ chosen from
that total rank, all pointwise thresholds may be enlarged to one threshold
before $X,q,d$ are chosen. The exceptional sets themselves may depend on
$X$ and the moving base field; the surviving interval is chosen only after
these sets have been formed. This order of choices is the content of the
assembly theorem, and ensures that the two-adic and fixed odd-prime
estimates hold throughout the *same* interval.

| Step | Archive reference |
| --- | --- |
| Two estimates and the prime-dependent base-field contracts | [SecondBound, ABound, FirstBound, TwoBase, TwoIn](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/SecondBound.lean#L14-L44) |
| Extraction of a finite exceptional set | [exc](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Exc.lean#L8-L41) |
| Finiteness and conversion of Lemma K to a length bound | [klen](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Klen.lean#L24-L46) |
| Exponent budget and the two cases | [kexp](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Kexp.lean#L8-L37), [point](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/ImportsAlt.lean#L9-L61) |
| Fixed constant and the sum over twists | [point2](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Point2.lean#L8-L49), [final](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Final.lean#L8-L68), [vvat](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Vvat.lean#L8-L21) |
| Uniform conductor and discriminant estimates | [rootdeg](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Rootdeg.lean#L8-L27), [layeremb](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Layeremb.lean#L8-L35), [disc](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Imports.lean#L8-L45), [layerdisc](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Layerdisc.lean#L9-L71) |
| Moving two-adic and fixed odd-prime towers | [partA](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/PartA.lean#L24-L84), [partB](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/PartB.lean#L52-L100) |
| Choice of ranks, common threshold and common window | [thmBab_of](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/ThmBabOf.lean#L11-L103) |

:::

### Where the bound itself comes from

The window is produced through the call `vwin_of_row` from the Galois row of {ref}`comp-galois`.
Along the way, tower estimates (for each prime $\ell$, lengths controlled away from finitely many
centres and in terms of a fixed layer) are combined into one record of constants valid for every
cutoff exponent, and counting cases I, II, III and V bound the lengths over arbitrary finite sets of
coefficient primes. One of the reading project's itineraries follows exactly this path; each step is
listed with its contract and tier (the premises of the checked steps — global Poitou–Tate duality,
local finiteness and local Tate duality, a Ferrero–Washington rank bound, a uniform exponent for a
reference layer — are among the source-read steps):

```{code-cell} ipython3
:tags: [remove-input]
its = m['itineraries']
best = max(its, key=lambda it: sum(bd.node(n)['component'] == 'cohomology' for n in it['nodes']))
assert sum(bd.node(n)['component'] == 'cohomology' for n in best['nodes']) >= 3
bd.show(f"**{bd.esc(best['title'])}.** " + bd.itinerary_md(best))
```

This is the precise place to compare the announcement's "weakening of Vandiver" with the
mathematics: the window bounds *sums of lengths*, for a selected family of fields and a bounded range
of twists. Positive finite lengths are compatible with it, and the announcement's further remarks
about individual $K$-groups would require additional theorems.

(comp-primes)=
## 12 · Auxiliary primes and Behrend towers

```{code-cell} ipython3
:tags: [remove-input]
bd.show(bd.card('primes'))
```

### What the two primes buy

```{code-cell} ipython3
:tags: [remove-input]
scope = next(s for s in bd.scopes() if s['id'] == 'suppliers-primes')
bd.show(f"The kernel-checked theorem `QH.pairEx` (scope “{bd.esc(scope['title'])}”, "
        f"{scope['original_project_module_count']:,} original modules) assumes: *{bd.esc(scope['assumption'])}* "
        f"It concludes: *{bd.esc(scope['conclusion'])}*")
```

The primes $q$ and $d$ enter the definition of the fields over which the cohomological window is
taken (through the admissibility condition `WinPair`) and the host fields. The twists of a
character modulo $M$ by the quadratic characters at $q$, at $d$, or at both, have square-root
prime-sum bounds on $[Y,Y^A]$; bounds of this shape are what the finite comparison assumes for the
characters it discards, and how exactly the chosen primes feed the window for a fixed target
character is listed as still to be checked (card above). The choice is sequential: a counting theorem gives a positive share of
admissible first primes, and for each of them a positive share of second primes; taking the share
parameter $\tfrac12$ leaves at least one choice at each stage. Changing $Y$ may change both primes,
hence the twisted characters; applying the analytic criterion to a *fixed* $L$-function still
requires the host construction on arbitrarily late windows.

### The Behrend set in the tower

The choice of the tower uses an additive-combinatorial construction. Take the integer vectors in
$\{0,\dots,d-1\}^S$ of a fixed squared norm and encode them in base $4Ld$. A relation
$j(s_2-s_1)=i(s_3-s_1)$ between encodings, with $1\le|i|,|j|\le L$ and $i\neq j$, forces the same
relation between the vectors, because the large base prevents carries; and three distinct points
of a sphere cannot satisfy it, because a line meets a sphere at most twice. In the computed example
($S=3$, $d=3$, $L=2$, squared norm $5$) the sphere consists of the six permutations of $(0,1,2)$,
their base-$24$ encodings are {glue:text}`behrend_enc`, and all {glue:text}`behrend_checks`
relations fail ({doc}`behrend`). Choosing the most populous sphere gives the quantitative lower bound
of `hostThickExists`, and the property `HostThickOrbit` bounds the intersection of a translate
with a short segment of a high-order orbit by two points. The archive's theorems `sphere_rel`,
`noRel_image` and `hostThickExists` are kernel-checked; this repository's independent proof of the
sphere lemma is `BehrendReading.sphere_rel` ({ref}`lean-teaching`).

(comp-galois)=
## 13 · The Galois row

```{code-cell} ipython3
:tags: [remove-input]
bd.show(bd.card('galois'))
```

### Inputs and outputs

Fix a CM field $E$, an algebraic closure $\Omega/E$, a prime $\ell$, an isomorphism
$\iota:\overline{\mathbf Q}_\ell\simeq\mathbf C$ and $a\ge1$. An input is a cuspidal automorphic
representation $\pi$ of $\mathrm{GL}_a(\mathbf A_E)$ — in Lean a nonzero, invariant, irreducible space of
cusp forms — which is **regular algebraic** (at each embedding the infinitesimal-character exponents
are distinct and lie in $\tfrac{a-1}2+\mathbf Z$) and **polarized** (a Hecke character $\chi$ of the
maximal totally real subfield $E^+$ with the right sign at the real places, and an equivariant
nondegenerate pairing between $\pi\otimes(\chi\circ N_{E/E^+})^{-1}$ and $\pi$).

The output is a continuous semisimple $r:G_E\to\mathrm{GL}_a(\overline{\mathbf Q}_\ell)$, an integer
$w_\pi$ and Hodge–Tate multisets $H_\tau$ with $H_{\tau\circ c}=w_\pi-H_\tau$, such that for all but
finitely many places $v$, with $q=Nv$ and $\sigma$ a Frobenius lift,

$$
\iota\big(\operatorname{charpoly}\rho(\sigma^{-1})\big)=\prod_{\alpha\in B_v}\big(X-q^{(a-1)/2}\alpha\big),
$$

where $B_v$ is the (unique) multiset of Satake parameters of $\pi_v$, characterized through the
eigenvalues of the spherical Hecke operators on a nonzero spherical vector. The exported row also
records local–global compatibility at $v\nmid\ell$ under stated conditions on the local parameter,
and crystalline, de Rham and potentially semistable comparisons above $\ell$.

### The construction, as the source organizes it

The producer `galoisLocalGlobalStrong_recParameter` feeds two inputs into the construction: a
geometric seed (`geoOne_holds`, built from a holomorphic Lefschetz formula) and a theta-lifting
theorem (`tLiftK`, with hypotheses on Hermitian and skew-Hermitian spaces, characters and weights).
It then climbs through three domains: a restricted case with a prescribed polarizing character and
extra field and place conditions; the general "good" case, reached by **twisting** $\pi$ by a Hecke
character to meet the prescription and untwisting the Galois side; and the general case, reached by
**quadratic descent**. For the last step one takes primes $p\equiv-1$ modulo a modulus $M$ collecting
the finitely many bad primes, adjoins $\sqrt{-p}$ — inertia at $p$ moves it, so $K=E(\sqrt{-p})$ is a
new quadratic CM extension — base-changes $\pi$ to $K$, applies the good case, and patches the
resulting $r_K$ by an index-two theorem on conjugation-invariant trace identities that agree on
pairwise intersections. The result is one $\rho$ over $E$ whose restriction to $G_K$ is $r_K$ for all
but finitely many $K$; for each place $v$ a good $K$ (depending on $v$) transfers the Frobenius
formula to $\rho$. A rank-one example with the constant cuspidal line shows that the hypotheses are
inhabited and that the polarization sign matters.

### What this component is, and is not

The row is stated for **all** regular algebraic polarized cuspidal $\pi$ on $\mathrm{GL}_a$ over CM
fields; it is the input that both the cohomological window and the automorphic assembly consume. Its
verification status is the one on the card above. A proof of this local–global statement would still
leave the global estimates of the other strata to be justified, and conversely a mathematical
assessment of the theta lift, the geometric seed, base change and trace patching is a larger task
than reading their types.

(comp-inputs)=
## 14 · Seven inputs at the decisive call

```{code-cell} ipython3
:tags: [remove-input]
bd.show(bd.card('inputs'))
```

### The seven groups of hypotheses

The theorem `UpperTheory.Lit.every_character_of_theta_integrals_local_matching` takes exactly
{glue:text}`n_seven_mod` arguments, as recorded in the blueprint:

```{code-cell} ipython3
:tags: [remove-input]
meaning = ["the unitary-group hypotheses at an auxiliary place (the eigenvalue package)",
           "the local theta inputs (the local theta package)",
           "agreement of theta integrals",
           "local matching",
           "a covolume bound",
           "existence of local Langlands parameters",
           "the cohomological window"]
items = [f"{k}. `{a}` — {meaning[k - 1]}" for k, a in enumerate(seven, 1)]
assert [a.split(':')[0].strip() for a in seven] == ['P', 'F', 'hA', 'hM', 'hX', 'hL', 'hV']
bd.show("\n".join(items))
```

From them it constructs a nonempty package of definite-side data (test vectors, grids of Fourier
coefficients, linked bundles) and a "Green" input about characters of finite general linear groups,
and passes them to `every_character_of_green_v_win`, which fixes the window width $3/2$, obtains the
primitive half-plane statement through the second verified cut's chain (`TopG` from the family
shape, hosts from the window) and descends to all characters.

### How the type loses its premises

`UpperTheory.FinalTheorems.everyCharacter_of_row` takes one hypothesis, the Galois row `Row0b`
(with the archive's local-parameter convention). It inserts that same term into two fields of the
literature record `OpenLiteratureStatements` (whose fields are a row, a local-parameter
statement and a row again), adds the existence of local Langlands parameters, and obtains the
cohomological window `VWin` from the same row. The next line, `everyCharacter`, supplies the row by
name — `galoisLocalGlobalStrong_recParameter` — so the half-plane theorem, and with it the five
exports, have **no explicit arithmetic premise in their types**.

That is a statement about types, not about mathematics. Names such as `published_results_eigen`,
`published_results_first` or `theta_integrals_agree_and_local_matching_of_literature` are where to
start verifying what the supplied terms establish; they are not explanations. Two of the five open
audit questions of the reading project sit exactly here: the source comparison of the Galois input,
and the existence of nonempty compatible data for one geometric family ({doc}`verification`).
