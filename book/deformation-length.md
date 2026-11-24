# The deformation length and graded Euler characteristics

The following proof notes isolate the commutative algebra used in the one-character bound.
They follow the pinned archive, using its chart and rigidity theorems explicitly, and replace
the finite-difference calculation by a generating-function argument.

## The deformation length behind Case I

The one-character estimate of {doc}`cohomological-window` follows from two
commutative-algebra comparisons: the cohomological length is bounded by a
saturated cotangent length (Lemma M'), which in turn is bounded by twice a sum
of valuations on characteristic-zero points (Lemma M).

**From cocycles to derivations.** Let $O$ be the complete coefficient
DVR with uniformizer $\varpi$, fraction field $F$ and finite residue
field. Let $\mathcal S$ be the locally trivial character cohomology
module of length Vlen. It is torsion: a continuous cocycle from a compact
group to the discrete torsion coefficient module has finite image,
hence is killed by a common nonzero scalar. Thus $\mathcal S$ is the
union of its $\varpi^n$-torsion layers.

The reducible base representation $r_0$ has diagonal characters
$\Psi,1,\Psi^{-1}$ and a quadratic multiplier. Conjugation by
$\operatorname{diag}(t,1,t^{-1})$ gives entry $(i,j)$ weight $w_i-w_j$,
where $(w_1,w_2,w_3)=(1,0,-1)$. Weight $-1$ consists of entries
$(2,1)$ and $(3,2)$. The normalization theorem sha_inj injects each
torsion layer additively into matrix cocycles of this weight, subject
to the prescribed local coboundary and global vanishing conditions.

Over the square-zero extension $O\oplus O/(\varpi^n)$, put
$r_\gamma(g)=(1+\gamma(g))r_0(g)$, with $\gamma$ taking values in the
square-zero ideal. Multiplication gives the cocycle equation

$$
 \gamma(gh)=\gamma(g)+\operatorname{Ad}(r_0(g))\gamma(h),
$$

with the adjoint action of the semidirect representation when the
multiplier is nontrivial. The universal property of the normalized
deformation ring $R$ identifies such a deformation with an algebra
map $f\mapsto(x_0(f),D(f))$, where $x_0:R\to O$ is the base point and

$$
 D(fg)=x_0(f)D(g)+x_0(g)D(f).
$$

On an entry of the universal representation in column $j$, the
derivation has value $\Psi(g)^{w_j}\gamma(g)_{ij}$. Since these scalars
are units and the entries determine the deformation, the assignment
is injective on the normalized cocycles and additive by uniqueness.

The model has a graded algebra $A=\bigoplus_j A_j$, augmentation
$x:A\to O$ and a map $A\to R$ killing its homogeneous equations. Every matrix
entry of the universal representation is in the image of this map, which
suffices for the injectivity of the pulled-back derivations.
The construction main_der lifts the local coboundary to characteristic
zero using the local chart and the model's lifting property.
Consequently the pullback of each derivation above is the reduction
of a weight-$-1$ derivation $A\to O$ at $x$. This integral lifting
assertion is essential for the saturated cotangent comparison.

**The saturated cotangent lattice (Lemma M').** Put $\mathfrak a=\ker x$
and let

$$
 \mathfrak a^{[2]}=\{f\in A:\exists\,0\ne b\in O,\ bf\in\mathfrak a^2\}.
$$

Since $A/\mathfrak a\simeq O$ is torsion-free, this saturation lies in
$\mathfrak a$, and $\mathfrak a/\mathfrak a^{[2]}$ is torsion-free.
Let $P$ be the image of $A_{-1}\cap\mathfrak a$ in that quotient and
$L$ the $O$-span of the images of the weight-$-1$ equations
$F_0,\ldots,F_r$. Put $C=P/L$; its extended length is cotLen.

An $O$-valued derivation kills $\mathfrak a^2$ by Leibniz, and kills
$\mathfrak a^{[2]}$ because $O$ is torsion-free. Its reduction kills
$\mathfrak a^{[2]}$ as well. Vanishing on the equations gives a map
$C\to O/(\varpi^n)$. A weight-$-1$ derivation is determined by its
restriction to that weight, so the normalized cocycles give an
injection

$$
 \mathcal S[\varpi^n]\longrightarrow
                    \operatorname{Hom}_O(C,O/(\varpi^n)).
$$

If $C$ has finite length, write $C\simeq\bigoplus_i O/(\varpi^{b_i})$.
The target has length $\sum_i\min(n,b_i)\le\sum_i b_i$.
Only injectivity as a map of sets is needed: a finite-length
$O$-module of length $b$ has $q_O^b$ elements, where $q_O$ is the
residue cardinality. The injection into a finite set makes each torsion layer finite as a set,
hence of finite length; comparison of cardinalities gives the length bound. If $C$ has infinite length
the inequality is automatic. Taking the supremum over $n$ gives

$$
 \operatorname{length}_O\mathcal S\le\operatorname{length}_O C.
$$

Indeed each finite strict chain in the torsion module can be tested
by finitely many elements, all in one torsion layer. This proves the
length comparison of mprime_holds and the directed-union step of
vlen_le, given the cocycle injection and derivation lift. Arbitrary
derivations with torsion coefficients need not kill the saturated
square; replacing the lift condition by their mere existence would
not prove the assertion.

**The upper-bound hypotheses.** For Lemma M, $O$ is a complete DVR of
characteristic zero. Fix an algebraically closed extension of its fraction
field with a valuation normalized by $v_O(\varpi)=1$. The weight-zero ring
$B=A_0$ is a complete Noetherian local $O$-algebra with the same residue field
(the condition `IsCO`); the augmentation restricts to a local retraction
$B\to O$. The graded algebra is generated over $A_0$ by finitely many
elements of weights $-2,-1,1,2$,
with $x$ killing nonzero weights. A formal chart over $F$ identifies
the rational cotangent space by linear coefficients. The dimensions
in weights $-2,-1,0,1,2$ are respectively $s,r,m,r'+1,s'+1$, where
$r\ge1$. The homogeneous equation ideal $J_0$ has generators
$r+1$ equations $F_i$ of weight $-1$, $s$ equations $G_i$ of weight
$-2$, $r'$ equations $E_i$ of weight $1$, $s'$ equations $E'_i$ of
weight $2$, and $m$ weight-zero equations $Z_i$ vanishing at $x$.
The $F_i,G_i,Z_i$ span their rational cotangent spaces (M1).

The image of $A_0$ in $A/J_0$ is finite over $O$ (M2). At a fixed
point of $A/J_0$ other than $x$, there cannot be both a positive-only
and a negative-only point with the same weight-zero restriction
(M3). At a two-sided point (nonzero values in both signs), the
derivations killing $J_0$ have dimension at most one (M4).
Finally a separating element $a\in A_0$ vanishes at $x$ but at
no two-sided point (M5). The deformation model supplies these
hypotheses through its finiteness, point and rigidity theorems.
The trace difference is the element $a$; it is constant on
grading-torus orbits.

**Smith invariants and the comparison.** The chart and finite generation theorem `rk_holds` make $P$ a finite free
$O$-module of rank $r$, and the spanning condition makes $L$ a full-rank sublattice.
Smith normal form permits an invertible change of the $r+1$ equations:
their images are now $\varpi^{b_i}y_i$ for $1\le i\le r$ and zero for
the last equation $F_*$, where the $y_i$ are a basis of $P$.
The equation ideal is unchanged, $F_*\in\mathfrak a^{[2]}$, and
$\operatorname{length}_O C=\sum_i b_i$.

The implicit-function construction eliminates the $m$ weight-zero
variables using the $Z_i$. The resulting chart $\phi$ satisfies
$\phi(Z_i)=0$. We can arrange $\phi(a)\ne0$ without changing its
values on $A/J_0$: if $\phi(a)=0$, add a product of a weight-$1$
element and one of the $F_i$ having nonzero images under $\phi$.
Such elements exist by the chart and spanning condition, and their
product is nonzero in the power-series domain. It lies in $J_0$,
has weight zero and vanishes at $x$.

The proof uses the multigraded Rees algebra over $A_0$ of the
submodules

$$
 N_0=A_{-2},\quad N_1=A_2,\quad
 N_2=A_0F_*^2+A_{-2}^2A_2 .
$$

The component of multidegree $d=(d_0,d_1,d_2)$ is
$N_0^{d_0}N_1^{d_1}N_2^{d_2}$ with formal multigrading tags.
Quotient by the coefficientwise kernel of $\phi$ to obtain $U$.
Let $\mathbf f$ be the list of sections consisting of the first
$r$ squares $F_i^2$ and the $G_i$ in degree $(1,0,0)$,
the $E_i^2,E'_i$ in degree $(0,1,0)$ and $F_*^2$ in degree $(0,0,1)$.
Multiplication by $a$ on $U$ is injective since $\phi(a)\ne0$.

Write $\chi_{\mathbf f}(V;d)$ for the graded Koszul Euler
characteristic of the sections on $V$ in degree $d$. Admissibility
ensures finiteness of the relevant homology lengths in large
multidegrees. The lower and upper comparisons give, for all sufficiently large $d$
in the coordinatewise order,

$$
 \begin{aligned}
 2^{r+r'}\sum_i b_i
 &\le\chi_{\mathbf f}(U/aU;d)\\
 &\le\chi_{(a)}(U/(\mathbf f)U;d)\\
 &\le 2^{r+1+r'}\sum_{\xi\in T}v_O(\xi(a)).
 \end{aligned}
$$

Here $T$ is a finite cover of the two-sided orbits over an
algebraically closed valued extension of $F$ (fin_holds).
The middle inequality uses regularity of $a$, permutation
invariance of Koszul Euler characteristics, and the upper-bound
rule for replacing the sections by their quotient. It does not
require the sections themselves to form a regular sequence.
The following sections compute the outer multiplicities.

**The lower multiplicity.** In the leading-term quotient the
first $r$ squared equations have leading terms
$\varpi^{2b_i}y_i^2$, by the negative-weight filtration and
$F_i-\varpi^{b_i}y_i\in\mathfrak a^{[2]}$.
The Hilbert function of that quotient modulo $\varpi$ counts
monomials of total negative and positive weights

$$
 (u,v)=(2d_0+4d_2,\,2d_1+2d_2).
$$

The corresponding generating series is

$$
 H(X,Y)=\frac{1}{(1-X)^r(1-X^2)^s
                       (1-Y)^{r'+1}(1-Y^2)^{s'+1}} .
$$

A backward difference in the first multigrading direction
corresponds to multiplication by $1-X^2$; the other directions
give $1-Y^2$ and $1-X^4Y^2$.
The scalar-peeling argument proved below, applied to the leading-term
quotient, gives a lower bound of $\sum_i2b_i$
times the Hilbert function after $r-1+s$ differences in the
first direction, $r'+s'$ in the second, and one in the third.
After cancellation its generating series is

$$
 \frac{(1+X)^{r-1}(1+Y)^{r'}(1-X^4Y^2)}
      {(1-X)(1-Y)(1-Y^2)}.
$$

For $u\ge4$ and $v\ge2$, the coefficient of $X^uY^v$ in the
fraction without the two factors $(1+X)^{r-1}(1+Y)^{r'}$ is

$$
 (\lfloor v/2\rfloor+1)-(\lfloor(v-2)/2\rfloor+1)=1.
$$

For sufficiently large $u,v$, multiplication by the two
polynomials multiplies this constant by $2^{r-1+r'}$.
This proves the finite-difference identity num_holds directly
by generating functions. Hence the lower multiplicity is
$(\sum_i2b_i)2^{r-1+r'}=2^{r+r'}\sum_i b_i$.
The leading-term passage and its Hilbert function use lk_holds
and hf_holds, and the lower inequality uses Euler monotonicity
for that quotient, rather than equality with the original
model's Hilbert function.

**The upper multiplicity.** On sufficiently large graded
pieces the support theorem leaves only the characteristic-zero
primes given by weight-zero restrictions of two-sided points.
Rigidity gives localized length at most one for each weight
piece of $A/J_0$ at these primes.
Replacing a homogeneous equation $f$ by $f^2$ at most doubles
a uniform localized length bound: the quotient by $f^2$ has a
filtration by the image of $f$ and the quotient by that image.
Both are quotients of the module with relation $f=0$, the first
with its degree shifted by the degree of $f$. Applying this
successively to the $r+1$ negative and $r'$ positive equations
gives the bound $2^{r+1+r'}$. The Rees-piece comparison transfers
it to the localized pieces of $U/(\mathbf f)U$.

For a large piece $W$, the Euler characteristic of multiplication
by $a$ is

$$
 \theta_a(W)=\operatorname{length}_{A_0}(W/aW)
                   -\operatorname{length}_{A_0}W[a].
$$

Both lengths are finite. The norm identity (`th_holds`) expresses this difference as a sum over
$O$-algebra maps $\sigma:B\to K$, where $K$ is the chosen algebraically closed
valued field. The summand is the length of $W_{\ker\sigma}$ over
$B_{\ker\sigma}$ times $v_O(\sigma(a))$. Indeed $B/\operatorname{Ann}_B W$
is finite over $O$ by the support theorem. Filter $W$ by prime quotients.
The snake lemma gives additivity of the kernel-cokernel difference, and
localization gives additivity of the localized lengths. For a prime factor
$D=B/\mathfrak p$ meeting $O$ nontrivially, $D$ is finite over the residue field
of $O$ and contributes zero to both sides. Otherwise $D$ is a finite free
$O$-module, a domain whose fraction field is a finite extension of $F$.
The support hypothesis makes $a$ nonzero there. Multiplication by $a$ is
injective, and Smith normal form gives the $O$-length of its cokernel as the
valuation of its determinant, namely the field norm. Finite $B$-length equals
$O$-length because their residue fields agree. The norm is a product over
all embeddings of the fraction field into $K$, each corresponding to a map
$B\to K$ with kernel $\mathfrak p$; each localized prime factor has length one.
This proves the identity, including the multiplicity of distinct embeddings
with the same kernel. The multiplicity
bound and the fact that $a$ is constant on torus orbits now give
the upper bound. Repeated weight-zero restrictions in a cover
can only enlarge the sum, since these evaluations are integral
and have nonnegative valuation.

Dividing the outer bounds by $2^{r+r'}$ gives

$$
 \operatorname{length}_O C\le2\sum_{\xi\in T}v_O(\xi(a)).
$$

The constant $2$ is thus the ratio of the upper multiplicity
$2^{r+1+r'}$ to the lower multiplicity $2^{r+r'}$. For coefficient
valuation $v_O=e(O/\mathbf Z_\ell)v_\ell$, division by the
ramification index gives the normalized one-character bound.

The next section proves the graded Euler comparisons. The chart construction,
local rigidity and support comparisons remain the geometric inputs.

| Step | Archive reference |
| --- | --- |
| Normalized cocycles and torsion layers | [sha_inj](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/ShaInj.lean#L27-L38), [vlen_le](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/VlenLe.lean#L46-L68) |
| Derivations and integral lifting | [main_der, model_lower](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/ModelLower.lean#L296-L402), [mprime_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/Mprime.lean#L6-L81) |
| Hypotheses and statement | [M1–M5, LemmaM, LemmaM'](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/OrbitVanishingLocal.lean#L21-L131) |
| Trace difference | [model_upper](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/ModelUpper.lean#L103-L251), [oneChar_unramU](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/FOneCharU.lean#L19-L74) |
| Smith normalization and chart | [sm_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/SmHolds.lean#L55-L113), [cut_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/CutHolds.lean#L101-L132), [nz_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/NzCoeffMul.lean#L33-L90), [main_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/MainCotSpan.lean#L32-L71) |
| Rees algebra and lower bound | [mN, ts, cnt](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/ToDegInjective.lean#L187-L234), [lk_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/LkHolds.lean#L8-L80), [hf_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/ReesGradedPieceSurjection.lean#L199-L271), [la_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/LaDifPerm.lean#L77-L125), [low_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/AdmissibleMonoIdeal.lean#L191-L323) |
| Numerical finite differences | [num_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/FrobeniusInclusionXEqMulQ.lean#L206-L284) |
| Local multiplicity and norm | [locLen_quotientWeightPiece_le_one](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/LocLenQuotientWeightPieceLeOne.lean#L70-L149), [locLen_aPiece_ideal2_le_two_pow](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/LocLenAPieceIdeal2LeTwoPow.lean#L69-L116), [th_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/HerbrandFinLen.lean#L189-L260), [up_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/TwoSigned.lean#L17-L96) |
| Finite orbit cover and comparison | [fin_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/FinHolds.lean#L49-L99), [core_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/AlgMemCoef.lean#L92-L144) |

## The graded Euler-characteristic argument

The comparison in Lemma M uses Euler characteristics of homogeneous
sections rather than lengths of intersections of regular sequences.

**Admissibility and finite lengths.** Let $(B,\mathfrak m)$ be a
Noetherian local ring and $R$ a standard $\mathbf N^k$-graded $B$-algebra:
$R_0$ is the image of $B$, each $R_{e_i}$ is finite over $B$, and
$R_{d+e_i}=R_dR_{e_i}$ for $d\ge0$. All modules below are finitely
generated $\mathbf Z^k$-graded $R$-modules. Put $I_i=(R_{e_i})$ and
$I_{\rm irr}=\prod_i I_i$. The ring $R$ is Noetherian, since it is
generated by finitely many elements from the $R_{e_i}$.

For homogeneous sections $\mathbf s=(s_1,\ldots,s_n)$ of nonnegative
multidegrees $\delta_i$, the pair $(\mathbf s,M)$ is admissible if

$$
 (\mathfrak m R\,I_{\rm irr})^N
 \subseteq\operatorname{Ann}_R M+(s_1,\ldots,s_n)
$$

for some $N$. Write $d\gg0$ for all degrees above a fixed threshold
in the coordinatewise order.

Choose finite homogeneous generators $u_j$ of $M$ of degrees $a_j$.
Then $M_d=\sum_j R_{d-a_j}u_j$ is finite over $B$. For $d\gg0$ all
coordinates of $d-a_j$ are at least $N$, so $M_d\subseteq I_{\rm irr}^N M$.
If the empty list is admissible, $\mathfrak m^N M_d=0$ in this range
and $M_d$ has finite $B$-length. If $I_{\rm irr}^N M=0$, then $M_d=0$
in this range. These observations give RuleFin and RuleIrr.

In the graded Koszul complex $K(\mathbf s;M)$ multiplication by each
$s_i$ is null-homotopic, using exterior multiplication by the
corresponding generator. Its homology is thus annihilated by
$\operatorname{Ann}_R M+(\mathbf s)$ and is finitely generated.
Admissibility makes its graded pieces finite-length for $d\gg0$.
Consequently we may form

$$
 \chi_{\mathbf s}(M;d)=
 \sum_{j=0}^n(-1)^j\operatorname{length}_B H_j(K(\mathbf s;M))_d .
$$

Finiteness of these homology lengths does not imply finiteness
of the lengths of the terms of the complex.

**Recursion and additivity.** Use $M(-\delta)_d=M_{d-\delta}$.
The two-term complex on a section $s$ of degree $\delta$ has homology
$M/sM$ in degree zero and $M[s](-\delta)$ in degree one. The spectral
sequence obtained by first taking homology in the $s$ direction of
the Koszul bicomplex on $(s,\mathbf t)$ has these two rows, followed
by Koszul homology for $\mathbf t$. Both pairs are admissible, since
their annihilators contain $\operatorname{Ann}M+(s)$.
Their second-page homology pieces have finite length for $d\gg0$;
the alternating sum is preserved on subsequent pages and equals
that of total homology. Hence

$$
 \chi_{(s,\mathbf t)}(M;d)=
 \chi_{\mathbf t}(M/sM;d)-\chi_{\mathbf t}(M[s](-\delta);d).
$$

Induction identifies this expression with the recursive chi of the
archive in sufficiently large degrees, where every terminal length
is finite. If $s$ acts injectively the second term vanishes (RuleNzd).

A graded short exact sequence $0\to M'\to M\to M''\to0$ gives a short
exact sequence of Koszul complexes and a long exact sequence of
homology. Admissibility passes to $M',M''$ because their annihilators
contain that of $M$. Taking alternating sums of finite lengths gives

$$
 \chi_{\mathbf s}(M;d)=\chi_{\mathbf s}(M';d)+
                       \chi_{\mathbf s}(M'';d)\qquad(d\gg0).
$$

Permuting the exterior generators gives an isomorphic Koszul
complex, proving order independence. Shifting a module shifts
the degree of its homology; replacing a section by one of the
same degree congruent modulo $\operatorname{Ann}M$ leaves the
complex unchanged. These identities hold for the recursive
invariant in its eventual range.

**Positivity.** We prove RulePos by induction on the length of the
list, starting with ordinary length. Use a finite homogeneous
prime filtration of $M$, with factors $(R/\mathfrak p)(-\alpha)$.
For completeness, choose a nonzero homogeneous element with
maximal annihilator among homogeneous elements in the current
quotient. Its annihilator is homogeneous. If homogeneous $u,v$
have product in it and $v$ is outside it, maximality applied to
the element multiplied by $v$ forces $u$ into it. This implies
primality by taking leading homogeneous terms modulo the ideal
in a translation-invariant total order on $\mathbf Z^k$.
Repeating in the quotient terminates by Noetherianity of $M$.
Each prime in the filtration contains $\operatorname{Ann}M$.

By additivity and shifts it suffices to prove positivity on
$D=R/\mathfrak p$. If $I_{\rm irr}\subseteq\mathfrak p$, the
large graded pieces of $D$ and its Koszul complex vanish.
Otherwise choose $u_i\in R_{e_i}\setminus\mathfrak p$ for every
$i$. For any nonnegative degree $\delta$, their product
$\prod_i u_i^{\delta_i}$ is a section of degree $\delta$ outside
$\mathfrak p$. Let $s$ be the first section, of degree $\delta$.
If $s\notin\mathfrak p$, it acts injectively on $D$ and the
recursion reduces to the shorter list on $D/sD$.
If $s\in\mathfrak p$, it acts by zero, so admissibility already
holds for the tail $\mathbf t$ on $D$. Choose a section $\sigma$
of the same degree outside $\mathfrak p$ as above. The exact
sequence

$$
 0\to D(-\delta)\xrightarrow{\sigma}D\to D/\sigma D\to0
$$

and additivity give

$$
 \begin{aligned}
 \chi_{(s,\mathbf t)}(D;d)
 &=\chi_{\mathbf t}(D;d)-\chi_{\mathbf t}(D;d-\delta)\\
 &=\chi_{\mathbf t}(D/\sigma D;d).
 \end{aligned}
$$

The induction hypothesis applies to the right side. In degree
zero one can take $\sigma=1$. Summing over the finite filtration
and absorbing shifts into the threshold proves eventual
nonnegativity. Neither a generic section nor an infinite
residue field is needed.

**Quotient comparisons.** For a graded quotient $M\twoheadrightarrow Q$
with kernel $L$, additivity and positivity give

$$
 \chi_{\mathbf s}(M;d)-\chi_{\mathbf s}(Q;d)
 =\chi_{\mathbf s}(L;d)\ge0\qquad(d\gg0).
$$

This is RuleMono. The recursion and positivity on the shifted
kernel give $\chi_{(s,\mathbf t)}(M;d)\le\chi_{\mathbf t}(M/sM;d)$.
Repeating for a prefix $\mathbf f$ gives RuleUB:

$$
 \chi_{(\mathbf f,\mathbf t)}(M;d)
 \le\chi_{\mathbf t}(M/(\mathbf f)M;d).
$$

At each step the quotient remains admissible for the remaining
list. The inequality does not follow by simply discarding
positive-degree Koszul homology, which has alternating signs.

**Finite differences and products.** When the empty list is
admissible on $M$, all large graded pieces have finite length.
In that range we can take the alternating sum of the terms
of the Koszul complex, rather than its homology. With
$h_M(d)=\operatorname{length}_B M_d$ and
$\Delta_\delta h(d)=h(d)-h(d-\delta)$, this gives RuleSmall:

$$
 \chi_{\mathbf s}(M;d)=
 \Delta_{\delta_1}\cdots\Delta_{\delta_n}h_M(d).
$$

Admissibility of the list alone does not suffice for this formula.

Let $b,c$ have degrees $\beta,\gamma$ and suppose $(bc,\mathbf t)$
is admissible on $M$. The kernel-cokernel sequence of the
composition of multiplication by $c$ and by $b$ is

$$
 \begin{aligned}
 0&\to M[c](-\beta-\gamma)\to M[bc](-\beta-\gamma)\\
 &\xrightarrow{c} M[b](-\beta)\to (M/cM)(-\beta)\\
 &\xrightarrow{b} M/bcM\to M/bM\to0 .
 \end{aligned}
$$

The map from the kernel of $b$ to $M/cM$ is reduction modulo
$cM$. Each module is killed by $bc$ and $\operatorname{Ann}M$,
so the tail is admissible on each. Additivity along this
sequence gives the product rule

$$
 \chi_{(bc,\mathbf t)}(M;d)=
 \chi_{(b,\mathbf t)}(M;d)+\chi_{(c,\mathbf t)}(M;d-\beta).
$$

For a degree-zero factor $b$ there is no shift.

**Application to Lemma M.** Let $V$ be the leading-term
quotient of the Rees module from the preceding note.
Multiplication by $\varpi$ is injective and the empty list
is admissible on $V/\varpi V$. The first $r$ sections in $V$
are $\varpi^{2b_i}z_i$, where $z_i$ is the section corresponding
to $y_i^2$, of multidegree $e_0=(1,0,0)$. For an exponent
$n_i\ge0$, the degree-zero product rule and regularity of
$\varpi$ give

$$
 \begin{aligned}
 \chi_{(\varpi^{n_i}z_i,\mathbf u)}(V;d)
 ={}& n_i\chi_{\mathbf u}(V/\varpi V;d)\\
 &+\chi_{(z_i,\mathbf u)}(V;d).
 \end{aligned}
$$

Here $\mathbf u$ denotes the rest of the list. Replacing a
scaled equation by its unscaled version enlarges the
equation ideal, so admissibility persists. RuleSmall makes
the first term depend only on the degrees of $\mathbf u$,
not on which of its sections have already been unscaled.
Permute and peel each scaled section, then apply positivity
to the final unscaled list. With $n_i=2b_i$ this yields

$$
 \chi_{\mathbf f}(V;d)\ge
 \left(\sum_{i=1}^r2b_i\right)
 \Delta_{e_0}^{r-1+s}\Delta_{e_1}^{r'+s'}
             \Delta_{e_2}h_{V/\varpi V}(d).
$$

The finite-difference calculation in the preceding section evaluates the last
factor to $2^{r-1+r'}$. This recovers la_holds in the required
case. The leading-term ideal contains the coefficientwise
chart kernel and the degree-zero element $a$ vanishing at $x$.
Thus $U/aU$ surjects onto $V$ and RuleMono transfers the lower
bound to $U/aU$. In the other direction regularity of $a$ on
$U$, order independence and RuleUB give

$$
 \begin{aligned}
 \chi_{\mathbf f}(U/aU;d)
 &=\chi_{(a,\mathbf f)}(U;d)\\
 &=\chi_{(\mathbf f,a)}(U;d)\\
 &\le\chi_{(a)}(U/(\mathbf f)U;d).
 \end{aligned}
$$

These are the two uses of positivity in the comparison.
The geometric input is admissibility of the Rees sections together with $a$.
The theorem `admissibility_holds` establishes the radical inclusion by
considering primes containing the chart-kernel and section ideals. For primes
not containing $I_{\rm irr}$, the weight-zero contraction is
either the maximal ideal or the kernel of a characteristic-zero
point. In the latter case the contraction contains the weight-zero equation ideal.
If some product of a weight-$-2$ and a weight-$2$ element is nonzero at the
point, the lifting theorem produces a two-sided point of the equation scheme,
contradicting M5 since $a$ vanishes there. Thus all such products vanish.
The one-sided support comparison forces the prime to contain the extended
maximal ideal. Finite generation
turns the radical inclusion into a power inclusion. The
support and chart theorems are the remaining geometric inputs;
the general Euler comparisons above require only admissibility.

| Step | Archive reference |
| --- | --- |
| Grading, admissibility and recursion | [Std, admitted, chi](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/EulerVanishingBelowDimension.lean#L66-L119), [ruleFin](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/RuleFin.lean#L345-L365), [ruleIrr](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/RuleIrr.lean#L9-L22) |
| Additivity, order and regular sections | [euler_additivity_of_rules](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/EulerAdditivityExactSequence.lean#L378-L428), [EulerIndependenceOfOrder](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/EulerIndependenceOfOrder.lean#L580-L621), [ruleNzd](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/RuleNzd.lean#L29-L42) |
| Homogeneous prime filtration and replacement | [ruleDev](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/RuleDev.lean#L352-L372), [exists_sec](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/VanishingBelowDimensionRule.lean#L177-L198), [dev_reduce, prime_step](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/VanishingBelowDimensionRule.lean#L260-L337), [rulePos](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/RulePos.lean#L22-L48) |
| Quotient inequalities | [ruleMono](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/RuleMono.lean#L11-L25), [ruleUB](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/RuleUB.lean#L20-L45) |
| Differences and products | [ruleSmall](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/RuleSmall.lean#L124-L141), [euler_rule_product_zero](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/ValuationFrobeniusEpsilon/LeastPrimeTwists/QuotientShiftIrreducible/NoetherianQuotientCalc/EulerRuleProductZero.lean#L17-L69) |
| Rees application | [admissibility_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/AdmissibilityHolds.lean#L30-L78), [la_peel, la_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/LaDifPerm.lean#L49-L125), [low_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/AdmissibleMonoIdeal.lean#L191-L323), [core_holds](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/AutomorphicVarieties/CommutativeAlgebra/GradedModulesLength/AlgMemCoef.lean#L92-L144) |

