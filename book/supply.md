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

### A closer look: the compact trace in Poitou–Tate duality

One of the arithmetic inputs just listed is global duality. To see how it is built, consider the
trace in degree three of compactly supported cohomology. This part can be reconstructed without
using global Poitou–Tate duality itself. We give the proof from the earlier arithmetic inputs and
keep the assumptions of the archive's trace theorem explicit.

Let $F$ be a number field, $\ell$ a prime, $n=\ell^k$ with $k\ge1$, and $S$ a finite set of finite
places containing all the places above $\ell$. Suppose $n$ is odd or $F$ is totally imaginary.
Write $F_S$ for the maximal extension unramified at finite places outside $S$,
$G_S=\operatorname{Gal}(F_S/F)$ and $D=\mu_n(F_S)$, with its natural Galois action.
All the $n$-th roots of unity lie in $F_S$. Let
$P^i(D)=\prod_{v\in S}H^i(F_v,D)$, where the local action is obtained by restriction.
We use the finite-place compact complex, the shifted cone of the localization map $f$:
its degree-$i$ term is $C^i(G_S,D)\oplus\prod_{v\in S}C^{i-1}(F_v,D)$ and its
differential is $(a,b)\mapsto(da,f(a)-db)$. Its exact sequence contains

$$
H^2(G_S,D)\xrightarrow{\mathrm{res}}P^2(D)
 \xrightarrow{\partial}H_c^3(D)\longrightarrow H^3(G_S,D).
$$

Here cohomology is continuous. We use the local Brauer invariant with arithmetic
Frobenius, identifying $\mathbf Z/n\mathbf Z$ with the $n$-torsion in $\mathbf Q/\mathbf Z$
by $a\mapsto a/n$. Denote the local invariant on $H^2(F_v,D)$ in this convention by $t_v$.

**Arithmetic inputs.** The trace theorem in the archive assumes $H^3(G_S,D)=0$ and
bijectivity of each $t_v$. These are separate inputs, not consequences of the argument below.
The archive also has a specialization in which all the $n$-th roots of unity already lie in $F$;
in that case it supplies the local bijectivity by the local duality theorem. The following
$S$-unit comparison is the main additional arithmetic ingredient.

Put $U=\mathcal O_{F_S,S}^{\times}$ (the union of the $S$-unit groups in the finite
subextensions) and let $b:H^2(G_S,U)\to\bigoplus_w\operatorname{Br}(F_w)$ be the
map through the global Brauer group. The archive proves that on the $\ell$-primary
subgroup this map is an isomorphism onto the group of $\ell$-primary families
of local Brauer classes which vanish at finite places outside $S$ and whose invariant
sum is zero. The archimedean places are included in this comparison. The $S$-unit Kummer
sequence is exact: an $n$-th root of an $S$-unit is again an $S$-unit, and adjoining it is
unramified outside $S$ since $n$ is invertible there. Thus
$1\to D\to U\xrightarrow{(\cdot)^n}U\to1$ gives a map $H^2(G_S,D)\to H^2(G_S,U)$
with image $H^2(G_S,U)[n]$.

For orientation, the primary comparison itself factors through the global Brauer group.
The Albert–Brauer–Hasse–Noether exact sequence identifies the global Brauer group with
the kernel of the sum of local invariants. A local family killed by a power of $\ell$ lifts
to a global Brauer class killed by the same power, by injectivity of localization. If the
family vanishes at finite places outside $S$, the archive's $S$-unit lifting theorem supplies
a preimage in $H^2(G_S,U)$. That group is torsion, so one can project a preimage onto its
$\ell$-primary component without changing its primary Brauer image. Injectivity on the
primary subgroup is a separate $S$-unit theorem. Together these facts give the comparison.
In particular, the lifting and injectivity results for $S$-units are genuine arithmetic
inputs; they do not follow just from exactness of the compact complex.

**Why the sum descends.** For a class $x\in H^2(G_S,D)$, its image in $H^2(G_S,U)$
is killed by $n$. By the primary comparison its local Brauer family vanishes at finite places outside $S$.
At a complex place the Brauer group is zero; at a real place it is killed by $2$, hence its
$n$-torsion is zero when $n$ is odd. Global Brauer reciprocity now gives
$\sum_{v\in S}t_v(\mathrm{res}_v x)=0$.
In particular the sum $t=\sum_{v\in S}t_v$ kills the image of $\mathrm{res}$. Since
$H^3(G_S,D)=0$, the connecting map $\partial$ is onto, and exactness gives a unique
homomorphism $T:H_c^3(D)\to\mathbf Z/n\mathbf Z$ satisfying $T\partial=t$.

**Why the trace is an isomorphism.** Surjectivity follows by putting a class with any prescribed
invariant at one place of $S$ and zero at the others. Such a place exists because $S$
contains the places above $\ell$.

For injectivity write an element in the kernel as $\partial\xi$, with $\xi\in P^2(D)$.
Then $t(\xi)=0$. Map $\xi$ to its family of local Brauer classes $\beta$, extended by
zero outside $S$. This is an $\ell$-primary family killed by $n$ with invariant sum zero.
The $S$-unit comparison gives an $\ell$-primary lift $y\in H^2(G_S,U)$ with $b(y)=\beta$.
It is important that this lift need not initially be known to be killed by $n$.
But $b(ny)=n\beta=0$, and $ny$ is still primary; injectivity of the comparison gives $ny=0$.
Kummer exactness now lifts $y$ to $x\in H^2(G_S,D)$. By compatibility with localization,
$\mathrm{res}_v x$ and $\xi_v$ have the same local invariant for each $v\in S$.
Local injectivity gives $\mathrm{res}(x)=\xi$. Exactness gives $\partial\xi=0$,
proving the trace isomorphism

$$
H_c^3(D)\ \xrightarrow[\quad T\quad]{\sim}\ \mathbf Z/n\mathbf Z.
$$

This proof separates the global arithmetic comparison from the elementary cone argument:
the nontrivial lifting step is to recover an $n$-torsion global class from a primary Brauer lift.
In particular, the resulting sequence

$$
H^2(G_S,D)\xrightarrow{\mathrm{res}}
\prod_{v\in S}H^2(F_v,D)\xrightarrow{\sum_v t_v}\mathbf Z/n\mathbf Z\longrightarrow0
$$

is exact at the local product and the last term. If a global degree-two class restricts to
zero at all but one place of $S$, it must restrict to zero there as well. This last
consequence uses only reciprocity and local injectivity, not the full trace isomorphism
or perfectness of the other Poitou–Tate pairings. The trace itself supplies the target
for compact cup-product pairings in the subsequent duality argument; it is not by itself
the uniform length bound in the cohomological window.

**A use of the last local invariant.** The archive uses this last-place argument in its
odd-prime reciprocity calculation. Here the coefficients are written additively as
$A=\mathbf Z/\ell^r\mathbf Z$ with $r>0$ and cyclotomic action $\chi$, and $\ell$ is odd.
Consider a continuous two-cocycle $w$ on the absolute Galois group of a number field.
Suppose it is constant on the cosets of the restricted-ramification kernel in each
variable, and that the finite set $S$ contains the places above $\ell$.
Then $w$ descends to a continuous two-cocycle of $G_S$ for this action: the cocycle identity
descends because the cyclotomic action also factors through $G_S$.
If its local restrictions at all $v\ne v_0$ in $S$ are coboundaries, the sum-of-invariants
arrow forces its restriction at $v_0$ to be a coboundary as well.
The archive invokes the nine-term Poitou–Tate interface for this assertion, with its
local invariant isomorphisms; this is not a claim that the compact trace theorem alone
supplies that entire interface.

The specific cocycle is a cup product. Let $B$ be a commutative $A$-algebra and
$\lambda:B\to A$ an $A$-linear map. Write $\alpha,\beta$ for the two characters
into $B^\times$ whose product is $\chi$ (viewed in $B$), and let $c,z$ be continuous
one-cocycles with actions $\alpha,\beta$ respectively. In particular,

$$
 c(gh)=c(g)+\alpha(g)c(h),\qquad
 z(gh)=z(g)+\beta(g)z(h).
$$

Set $w(g,h)=\lambda(z(g)\alpha(g)c(h))$. To check the two-cocycle identity, expand

$$
\begin{aligned}
(\mathrm dw)(g,h,j)
={}&\chi(g)w(h,j)-w(gh,j)+w(g,hj)-w(g,h).
\end{aligned}
$$

The two one-cocycle identities make the terms involving $z(h)c(j)$ cancel,
using $\alpha(g)\beta(g)=\chi(g)$; the remaining terms involving $z(g)c(h)$
and $z(g)c(j)$ cancel separately. If on a local decomposition group
$c(g)=\alpha(g)m-m$ for a fixed $m\in B$, an explicit local primitive is

$$
 b(g)=-\lambda(z(g)\alpha(g)m).
$$

Indeed $\chi(g)b(h)-b(gh)+b(g)=\lambda(z(g)\alpha(g)(\alpha(h)m-m))=w(g,h)$.
This supplies the coboundaries away from the distinguished auxiliary prime in the
archive's calculation; at that prime the last-place argument supplies the missing
coboundary. The subsequent local orthogonality argument, which is a separate input,
converts it into a constraint on the two one-cocycles. Thus the arithmetic use of
reciprocity is not merely a reference to a general duality theorem: it transfers a
specific local vanishing condition to a place where it is needed.

**Concordance with the archive.** The links below refer to the same original archive
revision as the rest of this book. The argument above reconstructs the trace theorem
from its arithmetic inputs, rather than re-proving the preceding comparison or all of global duality.

| Step | Declaration in the archive |
| --- | --- |
| Primary injectivity, lifting and restriction to the primary part | [eq_zero_of_sUnitsBrauer_eq_zero, exists_sUnitsBrauer_eq_iff, sUnitsBrauerPrimary_bijective](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/Brauer.lean#L282-L365) |
| Primary $S$-unit comparison and its map | [sUnitsH2PrimaryEquiv, coe_sUnitsH2PrimaryEquiv_apply](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/Brauer.lean#L376-L421) |
| Local invariant comparison and the roots-in-$F$ specialization | [gsLocalInvRoots_eq, bijective_gsLocalInvRoots](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseLocal.lean#L188-L214) |
| Vanishing of the sum on global classes | [sum_brauerInvZ_gsLocalRes_sUnits, gsSumInvRoots_globalToLocal](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseDefs.lean#L256-L291) |
| Descending the sum through the cone | [localToCompact_two_surjective, gsCompactInv, gsCompactInv_localToCompact](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseDefs.lean#L293-L321) |
| Surjectivity of the trace | [surjective_gsCompactInv](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseInv.lean#L97-L108) |
| Primary lift, Kummer step and bijectivity | [exists_sUnits_of_mem_localPrimaryKernel, injective_gsCompactInv, bijective_gsCompactInv, bijective_gsCompactInv_of_mem](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseInv.lean#L196-L270) |
| Use of the trace in the pairing | [compactZmodDualityMap](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseFormal.lean#L25-L36) |
| Last-place reciprocity for a descended cocycle | [glob](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimitiveFrobeniusFixed/OverIff.lean#L23-L53) |
| Cup product and the explicit local primitive | [core](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimitiveFrobeniusFixed/OverIff.lean#L225-L295) |

### From the compact trace to the duality pairing

Keep the preceding arithmetic setting, and for this part assume that $F$ contains the $n$-th
roots of unity. Put $A=\mathbf Z/n\mathbf Z$ with trivial action. We shall prove that

$
H^i(G_S,A)\ \times\ H_c^{3-i}(D)\ \longrightarrow\ A,
\qquad (x,y)\longmapsto T(y\smile x)
$

is perfect for $0\le i\le3$, from the earlier arithmetic results specified below.
Perfect means that either group is identified with the group of additive homomorphisms
from the other to $A$. The compact argument of the cup product comes first. In addition
to the trace isomorphism, the proof uses local Tate duality, the vanishing of the global
degree-three groups for $A$ and $D$, the finiteness of $H^1(G_S,A)$ and $H_c^2(D)$,
and the compatibility of compact cup products with the localization sequence.
The nontrivial arithmetic step is perfectness in degree one.

**Compact Kummer theory.** For $U=\mathcal O_{F_S,S}^{\times}$ as above, the notation
$H_c^i(U)$ now uses local coefficient groups $\overline{F_v}^{\,\times}$, not just the
restriction of $U$; the localization map includes the natural embeddings into these
groups. The same cone construction and its long exact sequence apply.
The global and local Kummer sequences form a compatible pair, giving a connecting map
$\delta_n:H_c^1(U)\to H_c^2(D)$.

This map is onto. Indeed, the primary subgroup of $H_c^2(U)$ is zero:
if $y$ is killed by a power of $\ell$, its image in $H^2(G_S,U)$ has zero local Brauer
components at places in $S$ by compact exactness, outside $S$ by the $S$-unit comparison,
and at infinity by the odd-or-totally-imaginary hypothesis. Primary injectivity of that
comparison gives zero global image. Compact exactness now expresses $y$ as the image
of a tuple of classes in $H^1(F_v,\overline{F_v}^{\,\times})$; all are zero by Hilbert 90.
Consequently the map $H_c^2(D)\to H_c^2(U)$ is zero, since its source is killed by $n$.
The compact Kummer sequence then gives the claimed surjectivity. Its kernel in degree one
is $nH_c^1(U)$.

**The idelic presentation of compact classes.** Write $C_S$ for the quotient of the idele
class group in which local units outside $S$ and the archimedean factors are killed.
It has a presentation by the local multiplicative groups at $v\in S$ and divisors at
finite places outside $S$, modulo the diagonal principal presentation.
Here multiplicative groups will also be written additively when they are arguments of
a cochain or an additive homomorphism.

A datum $d=(t,(a_v)_{v\in S})$ consists of $t\in F_S^\times$ whose Galois ratios
$\sigma(t)/t$ belong to $U$, and elements $a_v\in F_v^\times$.
The divisor of $t$ away from $S$ descends to a divisor of $F$: the extension is
unramified there and the valuations of $t$ at primes over a given prime agree.
Write this divisor as $\operatorname{div}_{\bar S}(t)$.
The datum gives a compact class $q(d)\in H_c^1(U)$ represented by
$(dt,(t_v+a_v)_v)$ in additive notation, where $t_v$ is the local image of $t$
and $dt$ is its Galois coboundary. Its idele class $c(d)\in C_S$ is represented
by $( (a_v)_v,-\operatorname{div}_{\bar S}(t))$.

Three properties are needed, and their strength matters.

1. Every compact degree-one class has such a datum. A global one-cocycle with values
   in $U$ is a coboundary in $F_S^\times$ by Hilbert 90; its local null-homotopies
   then differ from the local images of that cobounding element by local invariants
   $a_v\in F_v^\times$.
2. If $c(d)=0$, then $q(d)=0$. In the principal presentation there is $x\in F^\times$
   with local entries $a_v$ and divisor $-\operatorname{div}_{\bar S}(t)$.
   Thus $tx$ is an $S$-unit and the cone representative of $q(d)$ is exactly the
   compact coboundary of $tx$.
3. For every $a\in C_S$ there is a datum $d$ and a positive integer $m$ prime to
   $\ell$ with $c(d)=ma$. In the divisor presentation of $a$, the class of the
   outside-$S$ divisor has finite order $\ell^j m$. The archive's divisor-lifting
   theorem realizes $m$ times this divisor by a Galois-invariant divisor of an
   element of $F_S^\times$ (using the principal multiple $\ell^j m$ and that
   $\ell$ is invertible outside $S$). Taking the inverse of that element for $t$
   and multiplying the local entries by $m$ gives the datum.
   This property is weaker than surjectivity of the datum-to-idele-class map.

Class field theory identifies $H^1(G_S,A)=\operatorname{Hom}_{\rm cont}(G_S,A)$ with
$\operatorname{Hom}(C_S,A)$. The archive uses *all additive homomorphisms* on the
idelic side of this isomorphism. Let $\chi_x$ denote the character attached to $x$.

**Why the pairing is evaluation.** The central arithmetic identity is

$
 T(\delta_n q(d)\smile x)=\chi_x(c(d)).
$

Here $\delta_n$ includes the comparison between the local root modules and $D$.
We explain the signs and the global correction in the archive's proof. Use the embedding
$A\hookrightarrow\mathbf Q/\mathbf Z$, so all invariants in this argument can be
added in $\mathbf Q/\mathbf Z$. Let $z:G_S\to A$ represent $x$, take integer lifts
$\tilde z(g)$ between $0$ and $n-1$, and let

$
 B_z(g,h)=\frac{\tilde z(g)+\tilde z(h)-\tilde z(gh)}{n}.
$

This represents the integral Bockstein of $x$ and its class is killed by $n$.
The compact Kummer/Bockstein product identity says that the image of
$\delta_n q(d)\smile x$ in $H_c^3(U)$ is $q(d)\smile[B_z]$.
The sign is positive: the connecting-map product rule in compact degree one
gives the difference of these two expressions.

The global part of this latter cup is $dt\smile B_z$. Its cohomology class in
$H^3(G_S,U)$ is killed by $n$; the archive's separate vanishing theorem for the
$\ell$-primary part of this group therefore gives a two-cochain $Q$ in $U$ with
$dQ=dt\smile B_z$. In the larger multiplicative module $F_S^\times$ put
$W=t\smile B_z-Q$ in additive notation. The cochain $W$ is a cocycle, since
$d(t\smile B_z)=dt\smile B_z$.
Subtracting the compact coboundary of $(Q,0)$ from the product leaves global
component zero and local components $\operatorname{res}_v W+a_v\smile B_z$.
Thus the two local terms come from the global divisor and the local entries,
respectively.

Choose a local degree-two tuple $\xi$ representing the original compact
root-valued cup, using the surjectivity of the local-to-compact map in degree
two. Let $\xi^U_v$ be its image in the local Brauer group. By cone exactness,
the two local tuples $(\xi^U_v)_v$ and
$(\operatorname{res}_v W+a_v\smile B_z)_v$ differ by restrictions of a global
$S$-unit degree-two class. Its Brauer invariants vanish at finite places outside $S$.
At a finite place $w$ outside $S$, the valuation of $W$ is
$\operatorname{ord}_w(t) B_z$ because $Q$ is $S$-unit-valued. The unramified
local reciprocity formula identifies its invariant with the character on
that divisor. On the other hand local reciprocity identifies
$\operatorname{inv}_v(a_v\smile B_z)$ with $\chi_x$ on the idele supported at $v$
with entry $a_v$.

For precision, subtract a global $S$-unit correction from $W$ so that its local
restrictions inside $S$ equal $\xi^U_v-a_v\smile B_z$ in the Brauer group.
This does not change the outside-$S$ invariants. The sum of the inside-$S$
invariants of this corrected global Brauer class is killed by $n$: both
the root-valued tuple and the local Bockstein terms have $n$-torsion invariants.
Global reciprocity expresses this sum as minus the outside-$S$ sum and minus
the archimedean sum. The outside-$S$ sum is also killed by $n$, by the divisor
formula. Hence the archimedean sum is killed by $n$, as well as by $2$; it
vanishes if $n$ is odd, and is zero in the totally imaginary case.
This argument only needs the *sum* at infinity to vanish, not each individual
component of the corrected class.

Adding the local-entry contributions gives the value of the character on
$((a_v)_v,-\operatorname{div}_{\bar S}(t))$. This proves the evaluation identity,
including the minus sign in the divisor component. The calculation uses the
earlier local reciprocity and global $S$-unit vanishing theorems, not the
Poitou–Tate pairing being constructed.

**Nondegeneracy in both variables.** For a nonzero $x$, choose $a\in C_S$ with
$\chi_x(a)\ne0$. Property 3 gives $c(d)=ma$ with $(m,\ell)=1$, so
$T(\delta_n q(d)\smile x)=m\chi_x(a)\ne0$.

Conversely, let $y\in H_c^2(D)$ annihilate all of $H^1(G_S,A)$.
By compact Kummer surjectivity and property 1, write $y=\delta_n q(d)$.
The evaluation identity says that every homomorphism $C_S\to A$ kills $c(d)$.
For any abelian group $C$, such homomorphisms separate points of $C/nC$:
if an element of the quotient is nonzero, map its cyclic subgroup nontrivially
to $\mathbf Q/\mathbf Z$ and extend using injectivity of $\mathbf Q/\mathbf Z$.
The image lies in its $n$-torsion, hence in $A$. Therefore $c(d)=na$ for some $a$;
no finiteness of $C_S/nC_S$ has been assumed.
Choose $d'$ with $c(d')=ma$, $(m,\ell)=1$. Then $c(md-nd')=0$,
so property 2 yields $mq(d)=nq(d')$. Applying $\delta_n$ gives $my=0$.
Since $ny=0$ and $(m,n)=1$, we get $y=0$.
Both cohomology groups are finite, and their character duals have the same
cardinalities as the original groups, so the two zero-kernel assertions
give perfectness in degree one.

**The formal part: degrees zero, two and three.** Let $\partial$ denote each
local-to-compact map and $j$ each compact-to-global map, with coefficients and
degrees understood. In degrees zero and three, scalar multiplication and the
trace give the degree-zero pairing, while both groups in the degree-three
pairing are zero: $H^3(G_S,A)=0$ and $H_c^0(D)=0$, the latter because $S$ is
nonempty and localization is injective on invariants.

In degree two use local duality and the compact cup product identities.
For a local tuple $u$ and a global class $x$ of complementary degree,
$T(\partial u\smile x)$ is the sum of the local invariants of
$u\smile\operatorname{res}x$. For $y_c\in H_c^1(D)$ and $x_c\in H_c^2(A)$,
the signed compact cup comparison gives

$
 T(y_c\smile j x_c)=T(x_c\smile j y_c).
$

The sign is $(-1)^{1\cdot2}=+1$; the archive proves this identity for its compact
complex rather than invoking commutativity of an ordinary cup product.
Since $D$ is now trivial cyclic, choose an identification $D\simeq A$.
Perfectness in degree one also gives perfectness of the pairing between
$H_c^2(A)$ and $H^1(G_S,D)$ under the corresponding coefficient transport.

Suppose $x\in H^2(G_S,A)$ annihilates $H_c^1(D)$. Testing against
$\partial P^0(D)$ and applying local duality gives $\operatorname{res}x=0$.
Choose $x_c$ with $jx_c=x$. The functional $z\mapsto T(x_c\smile z)$ on
$H^1(G_S,D)$ vanishes on the kernel of localization: there $z=jy_c$ and
the compact cup comparison reduces the value to $T(y_c\smile x)=0$.
It therefore descends to the image in $P^1(D)$ and extends to that entire
group, by the same $\mathbf Q/\mathbf Z$ extension argument above.
By local duality the extension is represented by a tuple $\eta\in P^1(A)$,
using local products in the order $\eta_v\smile z_v$.
The class $x_c-\partial\eta$ now annihilates all of $H^1(G_S,D)$,
so degree-one perfectness makes it zero. Its global image is $x$, proving
injectivity in degree two.

To prove surjectivity, let $\lambda:H_c^1(D)\to A$ be any functional.
Its restriction along $\partial:P^0(D)\to H_c^1(D)$ is represented by
a tuple $\xi\in P^2(A)$ by local duality, with local products in the order
$u_v\smile\xi_v$. The functional kills the diagonal invariants
$H^0(G_S,D)$ by exactness. Testing a generator of the trivial cyclic $D$
shows that the sum of the invariants of $\xi$ after coefficient identification
$A\simeq D$ is zero. The trace isomorphism and exactness therefore give a lift
$x_0\in H^2(G_S,A)$ of $\xi$.
Subtract from $\lambda$ the functional given by $x_0$.
The difference vanishes on $\partial P^0(D)$ and hence descends to the image
of $j:H_c^1(D)\to H^1(G_S,D)$. Extend it to all of $H^1(G_S,D)$ and apply
degree-one perfectness to obtain a representing $x_c\in H_c^2(A)$.
The compact cup comparison shows that $x_0+jx_c$ represents the original
$\lambda$. This completes all four degrees over a field containing the
roots of unity.

**Archive concordance for the pairing.** The proof follows the arithmetic
calculation and the subsequent formal completion in the original archive.
The preceding vanishing, local duality, divisor lifting, and cochain comparison
theorems are the inputs at this level; the general finite-coefficient theorem
still requires passage to open subgroups and dévissage.

| Step | Declaration or proof in the archive |
| --- | --- |
| Compact primary vanishing and Kummer surjectivity | [eq_zero_of_gsUnitsCompact_two](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseKummer.lean#L228-L266), [surjective_gsKummerCompactδ](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseKummerDelta.lean#L38-L64) |
| Datum representation and prime-to-$\ell$ realization | [exists_gsUnitsDatum, gsUnitsData_surjective](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseClassIdele.lean#L197-L224), [gsUnitsClass, gsUnitsData_eq_zero_of_gsUnitsClass_eq_zero, exists_coprime_gsUnitsClass_eq](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseClassIdele.lean#L260-L332) |
| All idelic characters | [charEquiv](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/ClassFieldGSFull.lean#L77-L82) |
| Compact Kummer/Bockstein identity | [gsKummerCompactδ_cup](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseCupKummer.lean#L296-L319) |
| Global correction cocycle | [exists_gsUnitsData_cup_bock](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseCupGlobal.lean#L219-L277) |
| Local tuple and divisor correction | [gsRootsToUnitsCompact_cup_eq](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/GsRootsToUnitsCompactComparisonCup.lean#L60-L104), [zmodToQZ_gsCompactInv_gsCupClass](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/ZmodToQZGsCompactInvLocalToCompactEqLocalInvU.lean#L100-L150) |
| Evaluation and the two kernels | [gsCompactInv_gsCupClass, gsCompactInv_ker_left, exists_nsmul_eq_of_forall_zmod, gsCompactInv_ker_right](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BasePairing.lean#L87-L202) |
| Compact cup interchange | [compactCupRes_zmodMulPairingRight_swap](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseSwap.lean#L33-L52) |
| Degree zero, one and three | [bijective_three, bijective_zero, bijective_one](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseFormal.lean#L395-L440) |
| Degree two, both directions | [injective_two, surjective_two](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BaseFormal.lean#L536-L751) |
| Assembly over the base field | [BaseDualityHypotheses.of_gs, bijective_gs_compactZmodDualityMap](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/GroundTheory/ProfiniteCohomology/RestrictedRamification/BijectiveGsCompactZmodDualityMap.lean#L23-L73) |

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
