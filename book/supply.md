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
$j=\operatorname{NatLog}_\ell(R)+3$, where $\operatorname{NatLog}_\ell$ is the integer logarithm (zero at $R=0$),
and $s(h,m)=s_{\ell,h}(L_m)$.
For every integer $Z\ge1$ the two estimates from the tower give an exceptional set $T_Z\subset\{1,\ldots,Z\}$,
$|T_Z|\le R$, and

$$
\begin{aligned}
 s(h,m)&\le R(\max(m,j)+c+\lfloor\log_\ell Z\rfloor)
                  &&(h\notin T_Z,\ 1\le h\le Z),\\
 s(h,m)&\le v(h,j)+R(m-j)_+
                  &&(h\ge1).
\end{aligned}
$$

Here $v(h,j)=\operatorname{length}_{\mathbf Z_\ell}H^2(G_{L_j,S},\mathbf Z_\ell(h+1))$,
with $S$ the places over $\ell$, and $(m-j)_+=\max(m-j,0)$.
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
from the same totient inequality in $L_0$: $2^c\le2[L_0:\mathbf Q]\le16\deg M$,
so in particular $c\le16\deg M$. The moving layer has $m\le e(x)+2$. The admitted upper bound
$2^{e(x)}\le x^{A_1}$ gives $m\le(2|A_1|+2)(1+\log x)$, using
$\log 2>1/2$. The comparison in TwoBase transfers the result
to the actual field, with at most one extra unit of length per twist.

This is why a bound on each individual tower is not enough. The rank for
the moving two-adic tower is chosen uniformly in $q,d$, and the rank for
each fixed odd-prime tower is chosen before the window. Their sum bounds
the cardinality of the union of exceptional sets. If $R_*$ denotes that total rank, take $J=4(2C_t/\eta)^{R_*}$.
The finitely many pointwise thresholds may then be enlarged to a common
$x_1\ge1$ before choosing $X,q,d$. Taking $X\ge\max(2,x_1^J)$ ensures
that the entire surviving window lies above every threshold. The exceptional sets themselves may depend on
$X$ and the moving base field; the surviving interval is chosen only after
these sets have been formed. This order of choices is the content of the
assembly theorem, and ensures that the two-adic and fixed odd-prime
estimates hold throughout the *same* interval.

| Step | Archive reference |
| --- | --- |
| Two estimates and the prime-dependent base-field contracts | [SecondBound, ABound, FirstBound, TwoBase, TwoIn](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/SecondBound.lean#L11-L50) |
| Extraction of a finite exceptional set | [exc](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Exc.lean#L8-L41) |
| Finiteness and conversion of Lemma K to a length bound | [klen](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Klen.lean#L24-L46) |
| Exponent budget and the two cases | [kexp](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Kexp.lean#L8-L37), [point](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/ImportsAlt.lean#L9-L61) |
| Fixed constant and the sum over twists | [point2](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Point2.lean#L8-L49), [final](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Final.lean#L8-L68), [vvat](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Vvat.lean#L8-L21) |
| Uniform conductor and discriminant estimates | [rootdeg](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Rootdeg.lean#L8-L27), [layeremb](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Layeremb.lean#L8-L35), [disc](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Imports.lean#L8-L45), [layerdisc](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/Layerdisc.lean#L9-L71) |
| Moving two-adic and fixed odd-prime towers | [partA](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/PartA.lean#L24-L78), [partB](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/PartB.lean#L50-L95) |
| Choice of ranks, common threshold and common window | [thmBab_of](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LayeredIsomorphisms/ThmBabOf.lean#L11-L103) |

:::

:::{dropdown} Case I: a common integer for the coefficient primes

The joint bound in Case I is stronger than a collection of local length
bounds. Its arithmetic content is that the local contributions, grouped by
character kernel, are controlled by the valuations of an integer constructed
before the coefficient prime is chosen.

**The trace difference.** Fix an imaginary quadratic field $K$, a level
$N$, a twist $h\ge1$, and a rational prime $p\nmid30N|\operatorname{disc}K|$.
Choose a place $w$ above $p$ and let $q_w=|\kappa(w)|=p^f$, where $f\le2$.
The archive uses inverse arithmetic Frobenius. The reference trace for a
character $\psi$ is the trace of the reducible representation with diagonal
characters $\Psi,1,\Psi^{-1}$, where $\Psi=\chi_\ell^h\psi$ and
$\chi_\ell$ is the cyclotomic character. At inverse Frobenius it becomes
the complex number

$$
 E(z)=q_w^{-h}z+1+q_w^hz^{-1},
 \qquad z=\psi(q_w)^{-1}.
$$

The admissible representations belong to the rank-three unitary family
or to the rank-two descent family, realized in dimension three. The
counting input supplies a finite set $D$ of eigensystem labels, with a
trace $t_d$ for every $d\in D$. The essential properties of these data
are as follows:

- $|t_d|\le3$ and $q_w^ht_d$ is an algebraic integer.
- Complex field automorphisms permute the labels compatibly with their
  traces.
- For every odd coefficient prime $\ell\ne p$, the admissible
  representations can be classified by labels in $D$, with matching
  inverse Frobenius traces under the chosen field isomorphism to
  $\mathbf C$. Equality of labels implies isomorphism of representations.

In particular $D$ is a set of labels, not a set of distinct trace values.
Two nonisomorphic representations may have the same trace at $w$;
discarding such multiplicities would not give the required bound.

Put $Q_w=q_w^h\ge7$. Since $z$ is a root of unity, the cleared difference

$$
 A(z,d)=Q_w(t_d-E(z))
       =Q_wt_d-z-Q_w-Q_w^2z^{-1}
$$

is an algebraic integer. It is nonzero, because
$|Q_wt_d-z-Q_w|\le4Q_w+1<Q_w^2$. The same triangle inequality gives
$|A(z,d)|\le2Q_w^2$, hence

$$
 \log|A(z,d)|\le2h\log q_w+1.
$$

This separation uses the complex bound on the normalized trace and the
strict lower bound on the residue cardinality; it requires no
nonvanishing conjecture about a particular congruence.

**An integral product.** Let $G=(\mathbf Z/N\mathbf Z)^\times$, and let
$H'$ be a subgroup occurring as the kernel of a character of $G$.
Write $\mathcal C_{H'}$ for all complex characters with exactly that
kernel. If $m=[G:H']$, the quotient is cyclic of order $m$, and
$|\mathcal C_{H'}|=\varphi(m)$: its faithful characters are obtained by
sending a generator to each primitive $m$-th root of unity. Form

$$
 I_{H',p}=
 \prod_{\psi\in\mathcal C_{H'}}\prod_{d\in D}
          A(\psi(q_w)^{-1},d).
$$

All factors are nonzero algebraic integers. Their indexed family is
permuted by Galois automorphisms, since automorphisms preserve character
kernels and permute $D$. Thus the product is rational and integral,
so $I_{H',p}\in\mathbf Z\setminus\{0\}$. Equivalently, work inside a
finite normal number field containing the factors and extend its
automorphisms to the algebraic closure (and to $\mathbf C$).
The empty product is $1$. The archimedean bound gives

$$
 \log|I_{H',p}|
 \le\varphi(m)|D|(2h\log q_w+1).
$$

The actual construction in KeepNumU uses the disjoint union of the
rank-three and rank-two trace data. Write $\Delta=|\operatorname{disc}K|$
and $Y=N(h+1)$. The first set has cardinality at most $c_1Y^{A_1}$;
the second is counted at level $N\Delta$ and has cardinality at most
$c_2(\Delta Y)^{A_2}$. Thus $|D|\le(c_1+c_2\Delta^{A_2})Y^{A_1+A_2}$.
Since $\log q_w\le2\log p$ and $\log p\ge1$,

$$
 2h\log q_w+1\le 5Y\log p .
$$

Taking $c_K=5(c_1+c_2\Delta^{A_2})$ and $A_K=A_1+A_2+1$,
the interface NumberU3U_s packages the resulting bound as

$$
 \log|I_{H',p}|
 \le c_K\varphi(m)(N(h+1))^{A_K}\log p,
$$

with $c_K,A_K$ fixed for $K$. The trace calculation above explains
the integer construction underlying that interface; the existence,
classification and cardinality bounds for the admissible eigensystems
are its automorphic inputs. In the rank-three count, twisting by the
inverse cyclotomic character shifts the weights from $(h,0,-h)$ to
$(h-1,-1,-h-1)$; the traces are then transported back to inverse
Frobenius. The rank-two trace count uses the descent at level $N\Delta$.
The actual input families are narrowed by the admissibility and level
conditions of KeepNumU, not all representations of dimensions two and three.

**From the integral product to a local length.** Fix an odd $\ell\ne p$
and a coefficient ring as in the character reduction. A nonempty
character family with kernel $H'$ corresponds bijectively to
$\mathcal C_{H'}$ under the chosen coefficient embedding into
$\mathbf C$: all faithful characters of the cyclic quotient are
powers of any one of them with exponents prime to $m$. In particular
the ring need not contain roots of unity for unrelated character orders.
The hypotheses GD on one character imply GD on the whole family.
Indeed its other members are these coprime powers; the character order,
parity and quadratic local component are preserved, as is the kernel
of the character with its local component removed. The remaining
conditions in GD concern the field, level, prime and twist.

For each such $\psi$, the one-character theorem (OneCharU_s) gives
finiteness and a set $X_\psi$ of pairwise nonisomorphic admissible
representations with

$$
 v_\ell(\psi,h)
 \le 2\sum_{\rho\in X_\psi}
             v_\ell(\operatorname{tr}\rho(\operatorname{Frob}_w^{-1})
                         -E_\psi).
$$

Here $E_\psi$ is the reference trace transported to the coefficient
field, and on scalars $v_\ell(\ell)=1$. This theorem is proved by
bounding the character cohomology length by the cotangent length of
a graded deformation model (vlen_le), and applying Lemma M to the
weight-zero trace difference (model_upper). The trace difference
vanishes at the reducible base point and is nonzero at the relevant
two-sided points by the trace separation. The rigidity and
automorphy inputs identify their specializations with the two
admissible families. The representatives in model_upper are taken
modulo the grading torus action; the argument in oneChar_unramU
shows that isomorphic restrictions to $G_K$ come from the same
representative. This is what permits the use of the classification
by eigensystem labels, with no uncontrolled multiplicity. The initial
reduction to unramified coefficients uses the prime-to-$\ell$ order
of $\psi$ and coefficient independence of normalized length.

To compare the sum with $I_{H',p}$, use the injection of $X_\psi$ into
the labels $D$ for each $\psi$. Every cleared difference is integral,
so all of its valuations are nonnegative. Also $Q_w$ is an
$\ell$-adic unit. It follows that

$$
 \sum_{\psi}\sum_{\rho\in X_\psi}
 v_\ell(\operatorname{tr}\rho(\operatorname{Frob}_w^{-1})-E_\psi)
 \le v_\ell(I_{H',p}).
$$

No injectivity between the label sets for *different* characters
is required: the full product is indexed by the character-label
pairs. Consequently the sum of normalized lengths over the
kernel family is at most $2v_\ell(I_{H',p})$. This is PropGK.

**Two auxiliary primes.** The preceding argument cannot use the prime
$p$ as its own coefficient prime. Choose distinct auxiliary primes
$p,p'$ satisfying the same coprimality requirements. For any finite
set $S$ of relevant coefficient primes, the one-character finiteness
statement and the valuation bound at each $\ell$ follow from the
integer for $p$ if $\ell\ne p$, and from the integer for $p'$ otherwise.
By unique factorization,

$$
 \sum_{\ell\in S}v_\ell(I)\log\ell\le\log|I|
 \qquad(I\in\mathbf Z\setminus\{0\}).
$$

It follows that, for the primes in which the kernel family contains
a GD character,

$$
 \sum_{\ell\in S}\log\ell
          \sum_{\ker\psi=H'}v_\ell(\psi,h)
 \le 2c_K\varphi([G:H'])(N(h+1))^{A_K}
                    (\log p+\log p').
$$

Thus CorGK is a bound over arbitrary finite sets, even though the
construction of the individual representations depends on $\ell$.

**Returning to the host.** In Case I the quadratic field is fixed
as $K=\mathbf Q(\sqrt{-p_K})$ by the original character $\chi$.
The conditions outside $B_\chi$ ensure $\ell$ is prime to the
character order and to the discriminant and class number of $K$.
The field cut out by the residual cyclotomic character together
with the local-component-removed character is unramified at $p_K$,
whereas $K$ is ramified there. Thus it cannot contain $K$, giving
the remaining disjointness condition of GD. The other GD conditions
are the host parity, the local quadratic-component condition,
even level and $\ell-1\nmid2h$. These implications are gdOfHost.

Choose the two auxiliary primes larger than $30Qp_K$, with $Q$ the
original conductor, and require the moving primes $q,d$ to exceed
both. Since $N=\operatorname{lcm}(2^{e(x)+2},Q)qd$, neither auxiliary
prime divides $30N|\operatorname{disc}K|$. They may therefore be
fixed before the host is chosen.

Let $\mathcal H$ be the distinct character kernels occurring among
the chosen coefficient primes. Each quotient $G/H'$ for
$H'\in\mathcal H$ is cyclic. The sets of complex characters with
these kernels are disjoint, and the character group of $G$ has
order $|G|$. Hence

$$
 \sum_{H'\in\mathcal H}\varphi([G:H'])
 \le |G|=\varphi(N)\le N.
$$

Summing the joint bound over kernels gives at most
$A_0N(N(h+1))^{A_K}$, where
$A_0=2c_K(\log p+\log p')$ is fixed. Since $h+1\le t$ and $N\ge16$,
choose an integer $k\ge0$ with $A_0\le16^k$. The sum is then at most
$(Nt)^{k+1+A_K}$. This is CountI, with finiteness already established
for each character. The essential uniformity is supplied by the
integer product and the partition by kernels, not by a separate
estimate for every possible coefficient prime.

| Step | Archive reference |
| --- | --- |
| Construction of the counting data and constants | [numberU3U_of_adm2A_imp_adm2B, numberU3U_of_prints](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/KeepNumU.lean#L25-L80), [rank-two and rank-three trace counts](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/FrobeniusTraceCountBoundOfCmEigensystemCount.lean#L348-L466) |
| Actual counting and one-character interfaces | [NumberU3U_s, OneCharU_s](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/NumberU3US.lean#L27-L59) |
| Cleared trace difference and the integer product | [eisenstein_trace_difference_log_bound](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/BuildingsResidueChars/EisensteinTraceDifferenceLogBound.lean#L4-L61), [frobenius_trace_norm_nonzero_log_bound](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/BuildingsResidueChars/FrobeniusTraceNormNonzeroLogBound.lean#L7-L58) |
| Integral Galois-invariant product and the injection of label sets | [exists_int_eq_prod_of_galois_permuted_integral](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/BuildingsResidueChars/ExistsIntEqProdOfGaloisPermutedIntegral.lean#L6-L22), [adicNorm_prod_le_prod_of_injective_classes](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/BuildingsResidueChars/AdicNormProdLeProdOfInjectiveClasses.lean#L5-L20) |
| Cotangent comparison and one-character reduction | [vlen_le](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/VlenLe.lean#L47-L68), [model_upper](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/ModelUpper.lean#L112-L251), [oneChar_unramU and its coefficient descent](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/FOneCharU.lean#L19-L96) |
| Transport to the kernel family and the common integer | [propGK_of_numberU3U_of_oneCharU](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/FPropGKU.lean#L110-L173), [gdFacts](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/GdFacts.lean#L29-L102) |
| Two-prime argument | [corGK](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/CorGSumLog.lean#L8-L74) |
| Host hypotheses and the sum over kernels | [gdOfHost](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/GdOfHost.lean#L37-L95), [orbSum](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/OrbSum.lean#L44-L59), [countI](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/CountI.lean#L25-L137) |
| The actual call to these results | [count_i_of_printed_bound_k_kato_automorphy](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/LinkedUnlE.lean#L49-L54) |

:::

:::{dropdown} From character counts to the sum over all coefficient primes

The tower window supplies two bounds: one at $2$ on the moving field, and
one on a fixed reference layer for each odd prime in the finite set
$B_\chi$. It remains to control the odd-prime part of the cohomology of the
moving field itself. This is a different summation problem from the
separation of exceptional twists: the set of coefficient primes over which
we sum is arbitrary.

**Character reduction and the cases.** Fix the primitive character $\chi$,
of conductor $Q$ and order $o$. In the following argument $N$ is the host
conductor, $t\ge2$ is the twist cutoff and $M=Nt$. The set $B_\chi$ is
fixed before the moving field is chosen. Assume throughout the host size
conditions in the counting hypotheses: in particular, the auxiliary primes
$q,d$ exceed $2t+1$ and the fixed quantities defining $B_\chi$. It consists of $3$ and the odd
prime factors of $oQp_K h_*p_1$, where $p_K,h_*,p_1$ are the fixed auxiliary
quantities in the definition of [Bchi](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean#L54-L67).
Let $c$ be the action of complex conjugation on the locally trivial
cohomology of the moving CM field at twist $h$. The positive part is the
$(-1)^h$-eigenspace of $c$ (not always its $+1$-eigenspace), and the negative
part is the $(-1)^{h+1}$-eigenspace. Write $a_\ell(h)$ for the positive
length, with all lengths initially allowed to be infinite.

Let $H$ be the host subgroup of $(\mathbf Z/N\mathbf Z)^\times$.
At each odd $\ell$ choose a coefficient discrete valuation ring $O$
finite over $\mathbf Z_\ell$ and containing the requisite character values. Write $X_h$ for the characters
of $(\mathbf Z/N\mathbf Z)^\times$ trivial on $H$ and of parity
$\psi(-1)=(-1)^h$. Put $v_\ell(\psi,h)$ equal to the character length
Vlen divided by the ramification index of $O/\mathbf Z_\ell$
(the archive's normalized length Vn). The character reduction theorems give,
once the character lengths have been shown finite,

$$
 a_\ell(h)\le
 \begin{cases}
 \displaystyle\sum_{\psi\in X_h}v_\ell(\psi,h),&\ell\notin B_\chi,\\[4pt]
 \displaystyle\sum_{\psi\in X_h}
       (v_\ell(\psi,h)+\lambda_\ell(N,h)),&\ell\in B_\chi,
 \end{cases}
$$

where $\lambda_\ell(N,h)=\operatorname{lossAll}(\ell,N,[G:H],h)$
with $G=(\mathbf Z/N\mathbf Z)^\times$. The same inequalities in extended
lengths imply finiteness of $a_\ell(h)$; they do not presume it.
The first inequality uses $\ell\nmid[G:H]$, which holds outside $B_\chi$
under the host's size conditions. The second allows the loss of the
integral character decomposition when the index is divisible by $\ell$.
The bound used below is $\lambda_\ell(N,h)\le(Nh)^6$.
There are at most $N$ characters in $X_h$, and also at most $N$ in
$X_0\cup X_1$, which contains every $X_h$.

Here is the case division in the archive. The notation $\chi_\ell'(\psi)$
denotes its prime-to-$\ell$, local-component-removed character chiP;
$R_1$ and $c_2$ are the conductor quantities in Case V.

| Coefficient prime | Twist and character condition | Bound used |
| --- | --- | --- |
| Outside $B_\chi$ | $\ell-1\nmid2h$ | I |
| Outside $B_\chi$ | $\ell-1\mid2h$, $\psi=1$ | Z |
| Outside $B_\chi$ | $\ell-1\mid2h$, $\psi$ of even order | II |
| Outside $B_\chi$ | $\ell-1\mid2h$, $\psi\ne1$ of odd order | III |
| Inside $B_\chi$ | $h\ge2$, $\chi_\ell'(\psi)$ of even order | II |
| Inside $B_\chi$ | $h\ge2$, $\chi_\ell'(\psi)$ of odd order | IV |
| Inside $B_\chi$ | $h=1$, $R_1\le2^{c_2}$ | V |
| Inside $B_\chi$ | $h=1$, $R_1>2^{c_2}$ | Vs |

Outside $B_\chi$ the character $\chi_\ell'(\psi)$ equals $\psi$ when
$\ell-1\mid2h$. The two inequalities in the last rows cover equality
on the V side. This table describes sufficient cases for the reduction,
not a claim that all the underlying counting predicates are disjoint.
In particular Case IV's bound is valid for all twists of a character
of the specified odd order. The archive supplies IV and Vs separately,
rather than taking them as additional automorphic counting hypotheses.

**Primes outside $B_\chi$.** Let $S$ be any finite set of odd primes
outside $B_\chi$. For a fixed $1\le h<t$, split $S$ according to whether
$\ell-1$ divides $2h$. On the part where $\ell-1\nmid2h$, CountI bounds the entire weighted
sum by $M^{C_1}$, with $C_1$ independent of $S$ and $h$. The two auxiliary
primes required by that theorem are chosen depending on $\chi$ before
the host is chosen. A pointwise estimate growing with $\ell$ could not
replace this joint bound.

For the remaining primes, $\ell-1\mid2h$ implies $\ell\le 2t$.
Set $K=\max(C_Z,C_{II},C_{III})$. The corresponding pointwise bounds
include finiteness and give

$$
 v_\ell(\psi,h)\log\ell\le(\ell Nh)^K\le M^{3K},
$$

since $\ell Nh\le 2tM\le M^3$ for $t\le M$ and $M\ge2$.
Each prime contributes at most $NM^{3K}$, and there are at most $2t$
such primes. Thus

$$
 \sum_{\ell\in S}\log\ell\sum_{1\le h<t}a_\ell(h)
 \le t(M^{C_1}+2M^{3K+1})
 \le M^{C_1+3K+4}.
$$

For the last inequality use $t\le M$, $M\ge2$, and absorb the two terms
in the indicated power. All lengths are finite by the same case division.
Neither the maximum prime nor the cardinality of $S$ occurs in the final
bound.

**Primes inside $B_\chi$.** Fix $\ell\in B_\chi$ and suppose that its
reference-layer twist sum is at most $B\ge0$, including finiteness.
Let $K'=\max(C_{II},C_V,C_{Vs})$. Since $\ell\le N$ by the host's size
conditions, the three pointwise counts give $v_\ell(\psi,h)\log\ell\le M^{2K'}$
whenever their respective cases apply.

The remaining characters are collected in one set
$\mathcal O=\bigcup_{1\le h<t}\{\psi\in X_h:\operatorname{ord}\chi_\ell'(\psi)\text{ is odd}\}$.
The arithmetic of the host shows that
these characters have conductor dividing $Q$, so $|\mathcal O|\le Q$,
not merely $Nt$. Case IV gives a bound on the whole twist sum for each
such character:

$$
 \sum_{1\le h<t}v_\ell(\psi,h)\le B+M^{C_4}.
$$

The coefficient of $B$ is important: summing this bound separately for
each twist would introduce an unnecessary factor of $t$.
Using nonnegativity and exchanging the two finite sums gives instead

$$
 \log\ell\sum_{1\le h<t}\sum_{\psi\in X_h}v_\ell(\psi,h)
 \le Q\log\ell(B+M^{C_4})+tN M^{2K'}.
$$

Indeed the terms in $\mathcal O$ are bounded by their complete twist
sums, and there are at most $N$ of the other terms at each twist.
The character-reduction loss adds at most
$(\log\ell)Nt M^6\le M^8$. Consequently

$$
 \sum_{1\le h<t}\log\ell\, a_\ell(h)
 \le M^{C_\ell}+C_\ell B,\qquad
 C_\ell=C_4+2K'+9+\ell Q.
$$

To see the last inequality, bound the coefficient $Q\log\ell$ by
$\ell Q\le C_\ell$, and bound the remaining terms by
$M^{C_4+2}$, $M^{2K'+1}$ and $M^8$. Their sum is at most $M^{C_\ell}$
because $M\ge3$ and each exponent is at most $C_\ell-1$.
This is the reason for keeping a bound on the number of characters
independent of the cutoff: the tower budget is multiplied only by
a constant depending on $\chi$ and $\ell$.

**The two remaining arithmetic estimates.** Case IV uses the fixed field
$L_j$ above $\mathbf Q(\zeta_{\ell Q})$. It is Galois over $\mathbf Q$,
contains the field cut out by $\psi$, and has degree at most
$n_4=\ell Q\ell^j$. Character transport from that field gives
$v_\ell(\psi,h)\le s_{\ell,h}(L_j)+n_4\nu_\ell(N,h)$, with
$\nu_\ell(N,h)\le2Nh$. The reference-layer hypothesis bounds the sum
of the first terms by $B$. The second terms sum to at most
$2n_4Nt^2\le(Nt)^{n_4+3}$. This gives Case IV with $C_4=n_4+3$,
including finiteness. The transport inequality is an arithmetic input
here, not a consequence of the finite-sum rearrangement.

In Vs, the strict reverse conductor threshold and $h=1$ allow a different
field $L$, containing the character field and $\ell$-th roots of unity,
of degree at most $n_0(\chi)$, embedded in
$\mathbf Q(\zeta_{\ell N})$. The degree bound uses the character-order
estimate vsOrd; the field construction is vsField. By the discriminant
inequality above,
$\log|\operatorname{disc}L|\le n_0\log(\ell N)$.
Increase the Lemma K exponent to a nonnegative integer $k$. At twist
one its exponential expression is bounded by the polynomial

$$
 \exp((2[L:\mathbf Q])^k\log(2|\operatorname{disc}L|))
 \le(\ell N)^{A},\qquad A=(2n_0)^k(n_0+1).
$$

Here $\ell N\ge2$. Duality and character transport then give a finite
normalized length at most $2(\ell N)^A+2n_0N$. Multiplication by
$\log\ell\le\ell$ yields a polynomial bound, for example
$(\ell N)^{A+n_0+3}$. This is the bound used in Vs. Its uniformity
comes from the bounded degree and twist one, rather than from excluding
a further set of exceptional twists.

**The positive part on the common interval.** Combine the outside bound
$M^{C_0}$ with the inside bounds. Write $b=|B_\chi|$ and
$D=\sum_{\ell\in B_\chi}C_\ell$. For every finite set of odd primes the
positive-part sum is at most

$$
 M^{C_0}+bM^D+bDB\le M^C+CB,
 \qquad C=C_0+D+b+bD.
$$

Indeed $b+1\le2^b\le M^b$ and $bD\le C$. The exponents and the
two auxiliary primes from CountI are fixed before the host. In the
tower window take $B=\exp(x^{4\varepsilon/5})$.
The host conductor is the conductor of the moving field (hostCond);
hence $M=(\operatorname{cond}E)t(x)$. The positive-part estimate
applies to *every* interval satisfying the tower-window hypotheses.
The assembly jointWin_of uses the interval already selected by
ThmBab, not an intersection of two independently selected intervals.

| Step | Archive reference |
| --- | --- |
| Counting hypotheses and exhaustive case division | [Counts](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Counts.lean#L53-L73), [cases](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/Cases.lean#L8-L48), [bchiFacts](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/BchiFacts.lean#L8-L101) |
| Integral character reduction and its loss | [redPrime](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/RedPrime.lean#L11-L57), [redAll](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/RedAll.lean#L6-L21), [lossLe](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/LossLe.lean#L8-L54) |
| Sum outside the fixed set | [sumOut](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/SumOut.lean#L50-L231) |
| Normalization and finiteness of character reduction | [nrm, SumLe](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/ShaFamMono.lean#L71-L78), [sumBack](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CharacterLevelBounds/SumBack.lean#L7-L59) |
| Character conductor and fixed-layer estimate | [hostOdd](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/HostOdd.lean#L1-L111), [countIV](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/CountIV.lean#L39-L89) |
| Fields for the two exceptional character estimates | [ivField](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/IvField.lean#L32-L82), [vsOrd](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/PowTotientConductor.lean#L26-L48), [vsField](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/VsField.lean#L24-L126) |
| Strict reverse threshold at twist one | [countVs](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/CountVs.lean#L86-L171) |
| Inside-set sum and combined positive part | [sum_split, sumIn](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/FinalLe.lean#L14-L263), [point](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/PointArith.lean#L36-L92) |
| Host conductor and evaluation on a tower interval | [hostCond](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/HostCond.lean#L256-L323), [thmHV](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/ThmHV.lean#L6-L40), [jointWin_of](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean#L145-L158) |

:::

:::{dropdown} The final exponential comparison

On the joint interval the prime $2$ contributes at most
$(\log2)\exp(x^{4\varepsilon/5})$. The odd positive part contributes
$u^C+C\exp(x^{4\varepsilon/5})$, where $u=(\operatorname{cond}E)t(x)$.
The negative-part theorem ThmBcFree gives the separate bound minusBound;
its conversion to an exponential uses the fixed character order, not the
number of coefficient primes in the test set.

Write $n=[E:\mathbf Q]$, $N=\operatorname{cond}E$ and $o=\deg M_\chi$,
where $M_\chi$ is the abelian field cut out by the original character.
In the notation of minusBound the negative bound is

$$
 3nt^2\log(Nt)
 +C_b\sum_{\ell\mid o,\ \ell\ne2}\ell n^2t^2\log(\ell Nt)^2 .
$$

The sum is over distinct odd prime divisors of $o$. Since $n\le N$,
$t\ge1$ and $\log z\le z$ for $z\ge1$, the first term is at most
$3u^4$, and each summand before multiplication by $C_b$ is at most
$\ell^3u^4$. Thus the negative bound is at most $K_bu^4$, with
$K_b=3+|C_b|\sum_{\ell\mid o,\ell\ne2}\ell^3$.

The conductor bound and PageN give

$$
 \begin{aligned}
 N&\le 2^{e(x)+2}Qqd,\\
 2^{e(x)}&\le 2x^{2+8\varepsilon},\qquad t(x)\le x^{C_t}.
 \end{aligned}
$$

Together with $\log(qd)\le x^{\varepsilon/4}$, these imply
$\log u\le x^{\varepsilon/4}+(2+8\varepsilon+C_t)\log x+\log(8Q)$.
For sufficiently large $x$ this is at most $2x^{\varepsilon/4}$.
The choice of threshold is uniform in the auxiliary primes and in $E$.
In particular $K_bu^4\le K_b\exp(8x^{\varepsilon/4})$.

For odd $\ell$, put $s=(-1)^h$. Since $2$ is invertible, the two projectors
$(1+sc)/2$ and $(1-sc)/2$ split the locally trivial module into its two
sign parts. Additivity of extended length gives the sum of their lengths;
no such splitting is used at $2$. The sign decomposition and the separate
two-adic bound now give,
for every finite set of coefficient primes, finiteness and the upper bound

$$
 (\log2+C)\exp(x^{4\varepsilon/5})
     +K_b\exp(8x^{\varepsilon/4})+u^C .
$$

All constants are fixed and $\log u\le2x^{\varepsilon/4}$.
The logarithm of this positive upper bound is $O(x^{4\varepsilon/5})$,
hence $o(x^\varepsilon)$. It is therefore at most $x^\varepsilon/2$
eventually, giving the required $\sqrt{\exp(x^\varepsilon)}$ bound.
The final threshold is chosen before $X$; increasing $X$ ensures that
every $x$ on the selected interval exceeds it. The finiteness clauses
come from the three component estimates and the sign decomposition,
not from the numerical inequality alone.

This last step uses the already established negative-part theorem as an
input. Its proof of the underlying reciprocity and local estimates is a
separate question.

| Step | Archive reference |
| --- | --- |
| Negative bound and its exponential form | [minusBound](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean#L69-L71), [minusBound_le_exp_of_log_le](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/minusle.lean#L6-L76) |
| Conductor budget | [log_conductor_mul_height_le_of_pageN](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/LogConductorMulHeightLeOfPageN.lean#L6-L57) |
| Final comparison | [error_terms_le_sqrt_exp_rpow](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/ErrorTermsLeSqrtExpRpow.lean#L6-L89) |
| Sign decomposition and summation over arbitrary finite prime sets | [shaLen_eq_add, vvle_of_parts](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean#L88-L193) |
| Assembly of the three parts and VWin | [vwinAt_of_joint, vwin_of_joint](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CMFieldExponentialBounds/AdmissibleOfPageN.lean#L41-L134), [vwin_of_counts](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/HeightAndVanishing/JointWinOfCounts.lean#L16-L33) |

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
