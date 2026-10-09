# CoarseDeGiorgi

[![Build and verify](https://github.com/scottnarmstrong/CoarseDeGiorgi/actions/workflows/build.yml/badge.svg)](https://github.com/scottnarmstrong/CoarseDeGiorgi/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/CoarseDeGiorgi/actions/workflows/comparators.yml/badge.svg)](https://github.com/scottnarmstrong/CoarseDeGiorgi/actions/workflows/comparators.yml)

A machine-checked **Lean 4** formalization of the manuscript
*Coarse ellipticity and De Giorgi–Nash–Moser theory in the optimal range*
(Scott Armstrong, Benny Avelin, Tuomo Kuusi and Aatu Turpeinen), available as
[arXiv:2610.11879](https://arxiv.org/abs/2610.11879) and included in this
repository as a [PDF](paper/coarse-grained-dgnm.pdf).
It proves local boundedness, the weak Harnack inequality and the Harnack
inequality for divergence-form elliptic equations whose symmetric
coefficients may be degenerate and unbounded. It also proves, by explicit
examples, that the Besov-type condition on the coefficients under which these
results hold is sharp in its whole range, boundary included, in every
dimension $`d\ge3`$, that the powers of the coarse ellipticity ratio in the
local bound are optimal, and that the range of exponents in the weak
Harnack inequality cannot be enlarged.
It is built on
[`mathlib`](https://github.com/leanprover-community/mathlib4) and the public
[`CoarseGraining`](https://github.com/scottnarmstrong/CoarseGraining)
homogenization library.

## The two main results

Let $`d\ge3`$ and $`\square_0=(-\tfrac12,\tfrac12)^d`$, and write $`\rho\square_0`$
for the concentric cube of side $`\rho`$. The coefficient field $`\mathbf a`$ is
measurable, symmetric and positive definite almost everywhere, with **no lower
bound and no upper bound**. Solutions of $`-\nabla\cdot\mathbf a\nabla u=0`$ and
the corresponding sub- and supersolutions are taken in the weighted energy
space $`H^1_{\mathbf a}(\square_0)`$. The estimates depend on the
coefficients through a single number $`\Theta\ge1`$, the coarse ellipticity
ratio, which plays the role of the ratio of the ellipticity constants. The
hypothesis, described in the [next section](#the-hypothesis),
is that $`\Theta`$ is finite for exponents with a slack $`\theta\gt0`$.

**1. Subsolutions are bounded ($`L^\infty`$ bound).** Every weak subsolution of
$`-\nabla\cdot\mathbf a\nabla u\le0`$ in $`\square_0`$ is locally bounded above.
Quantitatively, for $`\tfrac12\le\rho_1\lt\rho_2\le1`$,

```math
\lVert u_+\rVert_{L^\infty(\rho_1\square_0)}\le C(\rho_2-\rho_1)^{-\gamma}\,\Theta^{\frac{d-1}{4\theta}}\lVert u_+\rVert_{L^2(\rho_2\square_0)},
```

and the same holds with any $`L^\eta`$ norm, $`0\lt\eta\lt2`$, on the right:

```math
\lVert u_+\rVert_{L^\infty(\rho_1\square_0)}\le C_\eta(\rho_2-\rho_1)^{-\frac{2\gamma}\eta}\,\Theta^{\frac{d-1}{2\eta\theta}}\lVert u_+\rVert_{L^\eta(\rho_2\square_0)}.
```

The numerator $`d-1`$ (in place of $`d`$) is the dimension of the cube boundaries
on which the proof takes place (Theorem A and Corollary B of the manuscript).
Both powers of $`\Theta`$ are optimal: for every fixed choice of the
exponents, no smaller power works, even for fixed $`\rho_1`$ and $`\rho_2`$
(Proposition 11.2, [below](#optimal-powers-in-the-local-bound)).

**2. The Harnack inequality.** Every nonnegative solution satisfies

```math
\mathrm{ess\,sup}_{\frac12\square_0}u\le\exp\bigl(C\sqrt\Theta\bigr)\mathrm{ess\,inf}_{\frac12\square_0}u,
```

and every nonnegative supersolution satisfies the weak Harnack inequality

```math
\Bigl(\frac1{|\tfrac58\square_0|}\int_{\frac58\square_0}u^{\eta}\Bigr)^{\frac1{\eta}}\le\exp\bigl(C\sqrt\Theta\bigr)\mathrm{ess\,inf}_{\frac12\square_0}u\qquad\text{for every }0\lt\eta\le\frac{r^*}2,
```

where $`r=\frac{2q}{q+1}`$ and $`r^*=\frac{dr}{d-(1-t)r}`$ is the Sobolev exponent of
$`W^{1-t,r}`$, so that $`\frac{r^*}2=\frac d{d-2+2t+d/q}`$ (Theorem C of the
manuscript). The endpoint $`\eta=\frac{r^*}2`$ is included, and for each
choice of the exponents of the hypothesis no larger $`\eta`$ is possible
([below](#the-exponent-of-the-weak-harnack-inequality)). The growth
$`\exp(C\sqrt\Theta)`$ cannot be improved, even for constant coefficients.

In both results the constants $`C`$, $`C_\eta`$ and $`\gamma\gt0`$ depend only on the
dimension and the exponents of the hypothesis, and on $`\eta`$ for $`C_\eta`$ and
for the constant of the weak Harnack inequality. They do not depend on the
coefficient field or on the solution.

## The hypothesis

### In general: coarse ellipticity

The hypothesis is not pointwise. It sees $`\mathbf a`$ only through the energy
of solutions. For every $`k\ge0`$ the triadic triangulation
$`\mathscr T_k`$ splits $`\square_0`$ into $`d!\,3^{kd}`$ simplices of diameter
comparable to $`3^{-k}`$, and each simplex $`\triangle`$ carries two
coarse-grained matrices, the two classical subadditive quantities of
quantitative homogenization:

- the matrix $`\mathbf a(\triangle)`$, the normalized energy of
  $`\mathbf a`$-harmonic functions with affine boundary values,

  $`\displaystyle e\cdot\mathbf a(\triangle)e=\min\Bigl\{\frac1{|\triangle|}\int_\triangle\nabla w\cdot\mathbf a\nabla w\ :\ w-e\cdot x\in H^1_{\mathbf a,0}(\triangle)\Bigr\};`$

- the matrix $`\mathbf a_{\ast}(\triangle)`$, through its inverse
  $`\mathbf a_{\ast}^{-1}(\triangle)`$: the smallest matrix controlling mean
  gradients by energy,

  $`\displaystyle \bigl|e\cdot(\nabla w)_\triangle\bigr|^2\le\bigl(e\cdot\mathbf a_{\ast}^{-1}(\triangle)e\bigr)\frac1{|\triangle|}\int_\triangle\nabla w\cdot\mathbf a\nabla w\qquad(w\in H^1_{\mathbf a}(\triangle)).`$

For a constant matrix $`\mathbf A`$ they equal $`\mathbf A`$ and $`\mathbf A^{-1}`$.
In general they are bounded by the averages $`(\mathbf a)_\triangle`$ and
$`(\mathbf a^{-1})_\triangle`$, and they can be much smaller: a very large or very
small conductivity on a small inclusion changes them only by a bounded
factor. For $`s,t\gt0`$ and $`1\lt p,q\lt\infty`$ the hypothesis bounds the
coarse ellipticity constants, discounted spatial moments of these matrices:

```math
\Lambda_{s,1,p}(\square_0)=\Bigl((1-3^{-s})\sum_{k\ge0}3^{-ks}\Bigl(\frac1{|\mathscr T_k|}\sum_{\triangle\in\mathscr T_k}|\mathbf a(\triangle)|^p\Bigr)^{\frac1{2p}}\Bigr)^2,
```

```math
\lambda_{t,1,q}(\square_0)=\Bigl((1-3^{-t})\sum_{k\ge0}3^{-kt}\Bigl(\frac1{|\mathscr T_k|}\sum_{\triangle\in\mathscr T_k}|\mathbf a_{\ast}^{-1}(\triangle)|^q\Bigr)^{\frac1{2q}}\Bigr)^{-2},
```

where $`|\cdot|`$ is the operator norm. A coarse-grained matrix that is large on
a few small simplices counts in proportion to their volume, and fine scales
are discounted. The two main results hold, with constants depending only on
$`d,p,q,s,t`$, whenever

```math
\Lambda_{s,1,p}(\square_0)\lt\infty,\qquad\lambda_{t,1,q}(\square_0)\gt0,\qquad \theta=1-s-t-\frac{d-1}2\Bigl(\frac1p+\frac1q\Bigr)\gt0,
```

with $`\Theta=\Lambda_{s,1,p}(\square_0)/\lambda_{t,1,q}(\square_0)\ge1`$. In the
notation of the manuscript, $`\theta=1-\sigma-\sigma_*`$ with
$`\sigma=s+\frac{d-1}{2p}`$ and $`\sigma_*=t+\frac{d-1}{2q}`$. The only
qualitative assumption, $`\mathrm{tr}\mathbf a,\mathrm{tr}\mathbf a^{-1}\in L^1(\square_0)`$,
makes $`H^1_{\mathbf a}(\square_0)`$ well defined; no estimate depends on these
integrals.

**Cubes instead of simplices.** The same constants can be computed on the
$`3^{kd}`$ triadic subcubes $`z+\square_{-k}`$ of $`\square_0`$ in place of the
simplices of $`\mathscr T_k`$, which gives $`\widetilde\Lambda_{s,1,p}(\square_0)`$,
$`\widetilde\lambda_{t,1,q}(\square_0)`$ and their ratio $`\widetilde\Theta`$. If
$`s\lt\frac12(1-\frac1p)`$ and $`t\lt\frac12(1-\frac1q)`$, the two versions are
comparable,

```math
\widetilde\Lambda_{s,1,p}\le\Lambda_{s,1,p}\le C\widetilde\Lambda_{s,1,p},\qquad C^{-1}\widetilde\lambda_{t,1,q}\le\lambda_{t,1,q}\le\widetilde\lambda_{t,1,q},\qquad\widetilde\Theta\le\Theta\le C\widetilde\Theta,
```

with $`C`$ depending only on $`d,p,q,s,t`$ (Proposition 3.4 and (3.20) of the
manuscript), so both main results also hold under the cubical hypothesis, with
$`\widetilde\Theta`$ in place of $`\Theta`$. The inequalities with constant one hold
for all $`s,t\gt0`$.

### Conditions on the coefficients

Averages of $`\mathbf a`$ and $`\mathbf a^{-1}`$ dominate the coarse-grained
matrices, so the coarse ellipticity constants are controlled by the
coefficient field itself (Theorem D of the manuscript, parts (i)–(iii)).

**Integrability.** If $`|\mathbf a|\in L^p(\square_0)`$ and
$`|\mathbf a^{-1}|\in L^q(\square_0)`$, then, for all $`s,t\gt0`$,

```math
\Lambda_{s,1,p}(\square_0)\le\lVert\mathbf a\rVert_{L^p(\square_0)},\qquad\lambda_{t,1,q}(\square_0)^{-1}\le\lVert\mathbf a^{-1}\rVert_{L^q(\square_0)},\qquad\Theta\le\lVert\mathbf a\rVert_{L^p(\square_0)}\lVert\mathbf a^{-1}\rVert_{L^q(\square_0)}.
```

**Negative regularity.** For a matrix field $`\mathbf b`$ with
$`|\mathbf b|\in L^1(\square_0)`$, $`s\gt0`$ and $`1\le p\lt\infty`$, the manuscript
defines the cube quasi-norm

```math
\lVert\mathbf b\rVert_{\mathring{\underline B}^{-2s}_{p,1/2}(\square_0)}=\Bigl(\sum_{k\ge0}3^{-ks}\Bigl(\frac1{3^{kd}}\sum_{z\in3^{-k}\mathbb Z^d\cap\square_0}|(\mathbf b)_{z+\square_{-k}}|^p\Bigr)^{\frac1{2p}}\Bigr)^2,
```

where $`z+\square_{-k}`$ are the triadic subcubes of $`\square_0`$ of side
$`3^{-k}`$. It measures $`\mathbf b`$ through its averages over these cubes,
discounted by $`3^{-2ks}`$, and, like $`\Lambda_{s,1,p}`$, sums square roots over
the scales; for positive semidefinite fields it is comparable to the
quasi-norm of the Besov space $`B^{-2s}_{p,1/2}(\mathbb R^d)`$ of the extension
by zero. If the quasi-norms of $`\mathbf a`$ and $`\mathbf a^{-1}`$ are finite, then

```math
\Lambda_{s,1,p}(\square_0)\le d!\,(1-3^{-s})^2\lVert\mathbf a\rVert_{\mathring{\underline B}^{-2s}_{p,1/2}},\qquad\lambda_{t,1,q}(\square_0)^{-1}\le d!\,(1-3^{-t})^2\lVert\mathbf a^{-1}\rVert_{\mathring{\underline B}^{-2t}_{q,1/2}},
```

and $`\Theta\le(d!)^2\lVert\mathbf a\rVert_{\mathring{\underline B}^{-2s}_{p,1/2}}\lVert\mathbf a^{-1}\rVert_{\mathring{\underline B}^{-2t}_{q,1/2}}`$.
So both main results hold under the Besov-type condition

```math
\lVert\mathbf a\rVert_{\mathring{\underline B}^{-2s}_{p,1/2}(\square_0)}\lt\infty,\qquad\lVert\mathbf a^{-1}\rVert_{\mathring{\underline B}^{-2t}_{q,1/2}(\square_0)}\lt\infty,\qquad s+t+\frac{d-1}2\Bigl(\frac1p+\frac1q\Bigr)\lt1,
```

with the indices of the quasi-norms themselves. In terms of the orders
$`\alpha=2s`$ and $`\beta=2t`$ of negative regularity, the condition reads
$`\frac{\alpha+\beta}2+\frac{d-1}2(\frac1p+\frac1q)\lt1`$. The condition is
sharp in its whole range: for every choice of the parameters outside it, in
every dimension $`d\ge3`$ and including its boundary, there are scalar
coefficients with finite quasi-norms for which local boundedness and the
Harnack inequality fail (Theorem F, [below](#the-coefficient-range)).

**Negative Sobolev norms.** For an open set $`U`$, an order $`\beta=m+\sigma\ge0`$
with an integer $`m\ge0`$ and $`0\le\sigma\lt1`$, and $`1\le\xi\lt\infty`$, the norm
$`\lVert w\rVert_{W^{\beta,\xi}(U)}`$ combines the $`L^\xi`$ norms of the arrays
$`\nabla^jw`$ of weak derivatives, $`j\le m`$, with the fractional seminorm of
order $`\sigma`$ of $`\nabla^mw`$. For $`1\lt p\lt\infty`$ and $`p'=\frac p{p-1}`$, the
negative Sobolev norm of a matrix field $`\mathbf b`$ with $`|\mathbf b|\in L^1(U)`$
is the dual norm tested on bounded functions,

```math
\lVert\mathbf b\rVert_{W^{-\beta,p}(U)}=\sup\Bigl\{\Bigl|\int_Ug\,\mathbf b\Bigr|\ :\ g\in L^\infty(U),\ \lVert g\rVert_{W^{\beta,p'}(U)}\le1\Bigr\}.
```

For positive semidefinite fields, the cube quasi-norm of order $`-2s`$ is
bounded by the negative Sobolev norm of any order $`-2s+\varepsilon`$,
$`0\lt\varepsilon\le2s`$ (Lemma B.2 of the manuscript; its proof tests with
Gaussian averages and compares them with the averages over cubes, Proposition
B.1). With part (ii) this gives part (iii) of Theorem D: if
$`0\lt\varepsilon\le2\min\{s,t\}`$ and the norms on the right are finite, then

```math
\Lambda_{s,1,p}(\square_0)\le C\lVert\mathbf a\rVert_{W^{-2s+\varepsilon,p}(\square_0)},\qquad\lambda_{t,1,q}(\square_0)^{-1}\le C\lVert\mathbf a^{-1}\rVert_{W^{-2t+\varepsilon,q}(\square_0)},
```

with $`C`$ depending only on $`d,p,q,s,t,\varepsilon`$, and
$`\Theta\le C^2\lVert\mathbf a\rVert_{W^{-2s+\varepsilon,p}}\lVert\mathbf a^{-1}\rVert_{W^{-2t+\varepsilon,q}}`$.
Corollary E follows. Let $`1\lt p,q\lt\infty`$ and $`\alpha,\beta\ge0`$ with

```math
\theta=1-\frac{\alpha+\beta}2-\frac{d-1}2\Bigl(\frac1p+\frac1q\Bigr)\gt0,
```

let $`\mathbf a\in W^{-\alpha,p}(\square_0)\cap L^1(\square_0)`$ and
$`\mathbf a^{-1}\in W^{-\beta,q}(\square_0)\cap L^1(\square_0)`$, and write
$`N=\lVert\mathbf a\rVert_{W^{-\alpha,p}(\square_0)}\lVert\mathbf a^{-1}\rVert_{W^{-\beta,q}(\square_0)}`$.
Then every subsolution satisfies, for $`\tfrac12\le\rho_1\lt\rho_2\le1`$,

```math
\lVert u_+\rVert_{L^\infty(\rho_1\square_0)}\le C(\rho_2-\rho_1)^{-\gamma}N^{\frac{d-1}{2\theta}}\lVert u_+\rVert_{L^2(\rho_2\square_0)},
```

and every nonnegative solution satisfies
$`\mathrm{ess\,sup}_{\frac12\square_0}u\le\exp\bigl(C\sqrt N\bigr)\mathrm{ess\,inf}_{\frac12\square_0}u`$,
with $`C`$ and $`\gamma\gt0`$ depending only on $`d,p,q,\alpha,\beta`$. The proof
applies part (iii) with $`s=\frac\alpha2+\frac\theta4`$, $`t=\frac\beta2+\frac\theta4`$
and $`\varepsilon=\frac\theta2`$, for which the slack of the hypothesis is
$`\frac\theta2`$, and then Theorems A and C. The negative Sobolev criterion of the
earlier coarse-grained theory
([arXiv:2601.05690](https://arxiv.org/abs/2601.05690)) has $`d`$ in place of
$`d-1`$ and requires $`\alpha\lt1-\frac1p`$ and $`\beta\lt1-\frac1q`$. To the authors'
knowledge, no local boundedness or Harnack inequality was known before under
negative regularity of $`\mathbf a`$ and $`\mathbf a^{-1}`$ in a range involving
$`d-1`$.

### The Bella–Schäffner range

For the integrability condition, indices $`s,t\gt0`$ with $`\theta\gt0`$ exist
exactly when

```math
\frac1p+\frac1q\lt\frac2{d-1}.
```

Both main results then hold with
$`\Theta\le\lVert\mathbf a\rVert_{L^p}\lVert\mathbf a^{-1}\rVert_{L^q}`$, and with
constants depending only on $`d,p,q`$; in particular the Harnack constant is
$`\exp\bigl(C(\lVert\mathbf a\rVert_{L^p}\lVert\mathbf a^{-1}\rVert_{L^q})^{1/2}\bigr)`$.
This is the range of Bella and Schäffner
([arXiv:1901.07958](https://arxiv.org/abs/1901.07958)), and it cannot be
enlarged: in every dimension $`d\ge3`$ there are coefficients with
$`\frac1p+\frac1q\gt\frac2{d-1}`$, and for $`d\ge4`$ also with equality, and
unbounded weak subsolutions (Bella and Schäffner, *Local boundedness for
$`p`$-Laplacian with degenerate coefficients*, Math. Eng. 5 (2023)), and for
$`d\ge4`$ the examples of Franchi, Serapioni and Serra Cassano (*Irregular solutions of
linear degenerate elliptic equations*, Potential Anal. 9 (1998)) give
unbounded weak solutions. The case $`\alpha=\beta=0`$ of Theorem F
([below](#the-coefficient-range)) gives scalar coefficients with
$`\lvert\mathbf a\rvert\in L^p`$, $`\lvert\mathbf a^{-1}\rvert\in L^q`$ and
$`\frac1p+\frac1q\ge\frac2{d-1}`$, and unbounded positive solutions, in every
dimension $`d\ge3`$. This includes the endpoint $`\frac1p+\frac1q=1`$ in dimension
three, where, as Bella and Schäffner note, their construction does not apply.
Trudinger's classical range, which is also the reach of the earlier
coarse-grained theory, is $`\frac1p+\frac1q\lt\frac2d`$. Bella and Schäffner also
treat nonsymmetric coefficients, dimension two and infinite exponents, in a
different solution class; the two solution classes are not compared.

### Uniformly elliptic coefficients

If $`\lambda|\xi|^2\le\xi\cdot\mathbf a\xi\le\Lambda|\xi|^2`$, the integrability
condition gives $`\Theta\le\Lambda/\lambda`$ for every admissible choice of the
exponents. The Harnack constant is $`\exp(C\sqrt{\Lambda/\lambda})`$, that of
Bombieri and Giusti; the weak Harnack inequality holds with constants of the
same form for every exponent $`0\lt\eta\lt d/(d-2)`$, the union of the ranges
$`0\lt\eta\le r^*/2`$ over the admissible exponents; and the $`L^\infty`$ bound
holds with every power $`\kappa\gt(d-1)/4`$ of $`1+\Lambda/\lambda`$. These
statements are checked against Mathlib-only restatements
([`HarnackUniform`](comparators/HarnackUniform.json),
[`WeakHarnackUniform`](comparators/WeakHarnackUniform.json),
[`LocalBoundednessUniform`](comparators/LocalBoundednessUniform.json)), with
these constants and ranges. See also the
[relation to DeGiorgi](#relation-to-coarsegraining-and-to-degiorgi).

### How the proof works

The Caccioppoli inequalities are not proved by testing with a cutoff times
the function. Smooth approximations are restricted to the boundary of a cube
$`\tau\square_0`$ with a good radius $`\tau`$. Outside the cube, averages of
their traces over boundary patches are prescribed at the vertices of a
Whitney decomposition of the exterior into simplices, interpolated to a
continuous function that is affine on every Whitney simplex, and replaced
simplex by simplex by $`\mathbf a`$-harmonic functions. The energy of this
extension on a simplex is computed exactly by the matrix $`\mathbf a(\triangle)`$,
and it is paired with the energy of the function, one size of simplices at a
time. The matrices $`\mathbf a_{\ast}^{-1}(\triangle)`$ give fractional regularity
of the trace, and a fractional Sobolev inequality on the
$`(d-1)`$-dimensional cube boundary drives a De Giorgi iteration.

The same extension, paired with powers of a supersolution, gives Moser's
iteration and the weak Harnack inequality at the exponent $`\eta=r/4`$; a
lemma of Bombieri and Giusti produces the constant $`\exp(C\sqrt\Theta)`$, and
Corollary B completes the Harnack inequality. The endpoint
$`\eta=\frac{r^*}2`$ (Section 9.5 of the manuscript) uses that the
contributions of the scales to $`\lambda_{t,1,q}(\square_0)`$ are summable: a
reconstruction of functions with zero boundary values, scale by scale, gives
a distribution estimate for potentials of measures, a capacitary comparison
bounds the mass of $`-\nabla\cdot\mathbf a\nabla u`$ on
$`\frac34\square_0`$, and the rest of $`u`$ is a solution controlled by the
Harnack inequality. Smaller exponents follow by Hölder's inequality.

## Sharpness

Section 11 of the manuscript proves three sharpness results, and all three
are formalized. The range of the condition and the powers of $`\Theta`$ are
shown to be optimal by coefficients concentrated on thin cylinders parallel to
the $`x_1`$-axis, and the exponent range of the weak Harnack inequality by a
radial coefficient field. Write $`x=(x_1,y)`$ with $`y\in\mathbb R^{d-1}`$. A cylinder
of radius $`\varepsilon`$ occupies a fraction of order $`\varepsilon^{d-1}`$ of
the simplices of size $`\varepsilon`$, so averages over simplices and cubes see
it only through its codimension $`d-1`$ (Lemma 11.1). This is why the same
$`d-1`$ appears in the range and in the powers of the main results.

### The coefficient range

The Besov-type condition cannot be relaxed, even at its boundary (Theorem F
of the manuscript). Let $`d\ge3`$, $`1\lt p,q\lt\infty`$ and $`\alpha,\beta\ge0`$
satisfy

```math
\theta_0=1-\frac{\alpha+\beta}2-\frac{d-1}2\Bigl(\frac1p+\frac1q\Bigr)\le0.
```

Then there are a measurable function $`a:(-\tfrac12,\tfrac12)^{d-1}\to(0,\infty)`$
and a weak solution $`u\in H^1_{\mathbf a}(\square_0)`$ of
$`-\nabla\cdot\mathbf a\nabla u=0`$ in $`\square_0`$ for the **scalar** field
$`\mathbf a(x)=a(y)I`$, such that
$`\mathrm{tr}\mathbf a,\mathrm{tr}\mathbf a^{-1}\in L^1(\square_0)`$, $`u\ge1`$
almost everywhere, the quasi-norm of $`\mathbf a`$ of order $`-\alpha`$ and
integrability $`p`$ is finite if $`\alpha\gt0`$ (and
$`\lVert\mathbf a\rVert_{L^p(\square_0)}\lt\infty`$ if $`\alpha=0`$), likewise for
$`\mathbf a^{-1}`$ with $`\beta`$ and $`q`$, and

```math
\mathrm{ess\,sup}_{\frac12\square_0}u=\infty\qquad\text{and}\qquad 0\lt\mathrm{ess\,inf}_{\frac12\square_0}u\lt\infty.
```

In fact $`u`$ is essentially unbounded in every neighborhood of every point of
the segment $`\{(x_1,0):\lvert x_1\rvert\lt\frac12\}`$. So both the $`L^\infty`$
bound and the Harnack inequality fail, and the range of the
[Besov-type condition](#conditions-on-the-coefficients) is exactly
$`\theta_0\gt0`$, in every dimension $`d\ge3`$. For $`\alpha=\beta=0`$ this is the
sharpness of the Bella–Schäffner range $`\frac1p+\frac1q\lt\frac2{d-1}`$ (above),
endpoint included, also in dimension three.

**The examples.** The field equals the identity outside a sequence of
disjoint cylinders whose axes $`\{y=y_j\}`$ converge to the line $`\{y=0\}`$.
Cylinder $`j`$ has a conducting core of radius $`\varrho_j`$, where
$`a=b_j\varrho_j^{-\kappa}`$, surrounded by an insulating annulus of outer radius
$`2\varrho_j`$, where $`a=b_j^{-1}\varrho_j^{2-\kappa}`$, with $`b_j=2^{-j-2}`$. By
Lemma 11.1, each cylinder contributes at most a constant times $`b_j^{1/2}`$ to
the square roots of both quasi-norms, whatever its radius, provided that

```math
\kappa\le\frac{d-1}p+\alpha\qquad\text{and}\qquad2-\kappa\le\frac{d-1}q+\beta,
```

and such a $`\kappa\in(0,2)`$ exists exactly when $`\theta_0\le0`$; at
$`\theta_0=0`$ both inequalities are equalities. Since the two conductivities
have ratio proportional to $`\varrho_j^2`$, each cylinder carries an explicit
nonnegative subsolution $`v_j`$, at least of order $`j`$ on its core, whose
growth rate along the axis does not depend on $`\varrho_j`$. The radii can therefore be chosen so small
that the norms of the $`v_j`$ are summable. Then $`v=\sum_jv_j`$ is a
subsolution, and $`u=1+U`$, where $`U`$ is the $`\mathbf a`$-harmonic function with
the boundary values of $`v`$, is a solution with $`u\ge1+v`$. The formal proof
uses the same cylinders with a different explicit subsolution in each of
them; [`CORRESPONDENCE.md`](CORRESPONDENCE.md) describes both.

### Optimal powers in the local bound

The powers $`\frac{d-1}{4\theta}`$ in the $`L^\infty`$ bound and
$`\frac{d-1}{2\eta\theta}`$ in its $`L^\eta`$ form cannot be lowered
(Proposition 11.2 of the manuscript). Fix $`d\ge3`$, $`1\lt p,q\lt\infty`$ and
$`s,t\gt0`$ with $`\theta\gt0`$. For $`0\lt\varepsilon\lt\frac18`$ let $`\mathbf a_\varepsilon`$
be the identity outside the cylinder $`\{\lvert y\rvert\lt2\varepsilon\}`$ and
$`\mathrm{diag}(a_\parallel,a_\perp,\dots,a_\perp)`$ inside it, with

```math
a_\perp=\varepsilon^{2t+\frac{d-1}q},\qquad a_\parallel=(d-1)\,\varepsilon^{2t+\frac{d-1}q-2}.
```

Each $`\mathbf a_\varepsilon`$ is uniformly elliptic, with constants depending on
$`\varepsilon`$, and the integrals of $`\mathrm{tr}\mathbf a_\varepsilon`$
and $`\mathrm{tr}\mathbf a_\varepsilon^{-1}`$ are bounded uniformly in
$`\varepsilon`$. The function
$`u_\varepsilon=1+x_1^2-\lvert y\rvert^2/\varepsilon^2`$ solves the equation in
the cylinder and is continued outside by a radial function that keeps it
negative there, so $`u_\varepsilon`$ is a solution whose positive part, a
subsolution, satisfies

```math
\lVert(u_\varepsilon)_+\rVert_{L^\infty(\rho_1\square_0)}=1+\frac{\rho_1^2}4,\qquad\lVert(u_\varepsilon)_+\rVert_{L^\eta(\rho_2\square_0)}\asymp\varepsilon^{\frac{d-1}\eta}.
```

Averages of $`\mathbf a_\varepsilon`$ and $`\mathbf a_\varepsilon^{-1}`$ and Lemma 11.1
bound $`\Lambda_{s,1,p}`$ and $`\lambda_{t,1,q}^{-1}`$ from above, and Theorem A
applied to $`u_\varepsilon`$ gives the matching lower bounds. Together,

```math
\Lambda_{s,1,p}\asymp\varepsilon^{-2\theta},\qquad\lambda_{t,1,q}\asymp1,\qquad\Theta\asymp\varepsilon^{-2\theta}.
```

Hence, for fixed $`\tfrac12\le\rho_1\lt\rho_2\le1`$ and $`0\lt\eta\le2`$, and every
real $`\upsilon\lt\frac{d-1}{2\eta\theta}`$,

```math
\frac{\lVert(u_\varepsilon)_+\rVert_{L^\infty(\rho_1\square_0)}}{\Theta^{\upsilon}\,\lVert(u_\varepsilon)_+\rVert_{L^\eta(\rho_2\square_0)}}\longrightarrow\infty\qquad(\varepsilon\to0).
```

With $`\eta=2`$ this is the optimality of $`\frac{d-1}{4\theta}`$ in Theorem A,
and with $`0\lt\eta\lt2`$ that of $`\frac{d-1}{2\eta\theta}`$ in Corollary B. The
manuscript does not claim this optimality for nonnegative solutions measured
by their full norms, for the powers of $`\rho_2-\rho_1`$, or for the powers of
the coefficient norms in Theorem D, where $`\Theta`$ is only bounded from above.

### The exponent of the weak Harnack inequality

The range $`0\lt\eta\le\frac{r^*}2`$ in the weak Harnack inequality cannot be
enlarged (Proposition 11.3 of the manuscript). Fix $`d\ge3`$, $`1\lt p,q\lt\infty`$ and
$`s,t\gt0`$ with $`\theta\gt0`$, and let $`\beta=2t+\frac dq`$, so that
$`\frac{r^*}2=\frac d{d-2+\beta}`$. The radial field

```math
\mathbf a(x)=|x|^{\beta}\log^3\Bigl(\frac{e\sqrt d}{|x|}\Bigr)I
```

satisfies the hypothesis: it is bounded, so $`\Lambda_{s,1,p}(\square_0)\lt\infty`$,
and near the origin each scale contributes a bounded amount to the series
defining $`\lambda_{t,1,q}(\square_0)^{-1/2}`$, up to the logarithm, whose third
power makes the series converge, so $`\lambda_{t,1,q}(\square_0)\gt0`$. The
supersolutions $`u_\varepsilon`$, $`0\lt\varepsilon\lt\frac18`$, are the fundamental
solution with pole at the origin, of size $`|x|^{-(d-2+\beta)}`$ up to a
logarithm, made constant on the ball $`B(0,\varepsilon)`$. Their essential
infimum on $`\frac12\square_0`$ is positive and does not depend on
$`\varepsilon`$, while, for every $`\eta\gt\frac{r^*}2`$,

```math
\Bigl(\frac1{|\tfrac58\square_0|}\int_{\frac58\square_0}u_\varepsilon^{\eta}\Bigr)^{\frac1\eta}\longrightarrow\infty\qquad(\varepsilon\to0).
```

The field and the supersolutions are the same for every $`\eta\gt\frac{r^*}2`$, and
$`\Theta\lt\infty`$ for this field, so the weak Harnack inequality fails for every
$`\eta\gt\frac{r^*}2`$, with any finite constant. The formal proof uses the same
field and smooth supersolutions with the same behaviour;
[`CORRESPONDENCE.md`](CORRESPONDENCE.md) describes the difference.

### In Lean

Theorem F is formalized as
[`CoarseDeGiorgi.sharpness`](CoarseDeGiorgi/Statements/Sharpness.lean),
Proposition 11.2 as
[`CoarseDeGiorgi.optimal_powers`](CoarseDeGiorgi/Statements/OptimalPowers.lean)
and Proposition 11.3 as
[`CoarseDeGiorgi.weak_harnack_sharpness`](CoarseDeGiorgi/Statements/WeakHarnackSharpness.lean),
with the constructions in
[`CoarseDeGiorgi/SharpnessExamples/`](CoarseDeGiorgi/SharpnessExamples/).
All three are restated with Mathlib alone in the comparators
[`Sharpness`](comparators/Sharpness.json),
[`SharpnessPolynomial`](comparators/SharpnessPolynomial.json) and
[`SharpnessWeakHarnack`](comparators/SharpnessWeakHarnack.json).
In `sharpness` and in the `Sharpness` comparator the integrability exponents
of Theorem F are called `ξ` and `ζ`; the manuscript writes $`p`$ and $`q`$.

## Guarantees

- **No `sorry`** in the library. Each Mathlib-only comparator challenge in
  `CoarseDeGiorgiAudit/Challenge/` contains one intentional statement-level
  `sorry`, which the corresponding solution file proves.
- **No custom `axiom`.** The main theorems, and the theorems proved by the
  comparator solutions, depend only on mathlib's standard axioms `propext`,
  `Classical.choice` and `Quot.sound`, as reported by
  [`CoarseDeGiorgiAudit/AxiomsAudit.lean`](CoarseDeGiorgiAudit/AxiomsAudit.lean)
  and checked in CI.
- **Independent check of the statements.** The main results are restated with
  Mathlib alone and checked with
  [`leanprover/comparator`](https://github.com/leanprover/comparator); see
  [below](#verified-against-mathlib-only-statements) and
  [`COMPARATORS.md`](COMPARATORS.md).
- **Pinned toolchain.** Lean `v4.35.0-rc2`, mathlib `v4.35.0-rc2`, and
  `CoarseGraining` at a fixed revision, recorded in
  [`lake-manifest.json`](lake-manifest.json).
- **Size.** About 100,000 lines of Lean in about 1,000 library modules, plus
  the comparator checks.

## The Lean statements

Each main result is a theorem in the `CoarseDeGiorgi` namespace, stated in a
file of its own in [`CoarseDeGiorgi/Statements/`](CoarseDeGiorgi/Statements/):

| Result | Lean declaration |
| --- | --- |
| $`L^\infty`$ bound for subsolutions, in $`L^2`$ and in every $`L^\eta`$, $`0\lt\eta\lt2`$, with one shared $`\gamma`$ (Theorem A, Corollary B) | [`CoarseDeGiorgi.local_boundedness`](CoarseDeGiorgi/Statements/LocalBoundedness.lean) |
| weak Harnack inequality for every $`0\lt\eta\le r^*/2`$, with a constant depending on $`\eta`$ (Theorem C) | [`CoarseDeGiorgi.weak_harnack_range`](CoarseDeGiorgi/Statements/WeakHarnackRange.lean) |
| Harnack inequality (Theorem C) | [`CoarseDeGiorgi.harnack`](CoarseDeGiorgi/Statements/Harnack.lean) |
| integrability: $`\Lambda_{s,1,p}\le\lVert\mathbf a\rVert_{L^p}`$, $`\lambda_{t,1,q}^{-1}\le\lVert\mathbf a^{-1}\rVert_{L^q}`$ and the bound on $`\Theta`$, for all $`s,t\gt0`$ and finite $`p,q`$ (Theorem D (i)) | [`CoarseDeGiorgi.moment_bounds_lebesgue`](CoarseDeGiorgi/Statements/MomentBoundsLebesgue.lean) |
| negative regularity: the same bounds by the cube quasi-norms, for finite $`p,q`$ (Theorem D (ii)) | [`CoarseDeGiorgi.moment_bounds_besov`](CoarseDeGiorgi/Statements/MomentBoundsBesov.lean) |
| negative Sobolev norms: $`\Lambda_{s,1,p}\le C\lVert\mathbf a\rVert_{W^{-2s+\varepsilon,p}}`$, $`\lambda_{t,1,q}^{-1}\le C\lVert\mathbf a^{-1}\rVert_{W^{-2t+\varepsilon,q}}`$ and the bound on $`\Theta`$, for $`0\lt\varepsilon\le2\min\{s,t\}`$ and finite $`p,q`$ (Theorem D (iii)) | [`CoarseDeGiorgi.moment_bounds_sobolev`](CoarseDeGiorgi/Statements/MomentBoundsSobolev.lean) |
| coefficients in negative Sobolev spaces: the $`L^\infty`$ bound with the power $`\frac{d-1}{2\theta}`$ of $`N=\lVert\mathbf a\rVert_{W^{-\alpha,p}}\lVert\mathbf a^{-1}\rVert_{W^{-\beta,q}}`$, and the Harnack inequality with constant $`\exp(C\sqrt N)`$ (Corollary E) | [`CoarseDeGiorgi.local_boundedness_sobolev`](CoarseDeGiorgi/Statements/LocalBoundednessSobolev.lean), [`CoarseDeGiorgi.harnack_sobolev`](CoarseDeGiorgi/Statements/HarnackSobolev.lean) |
| indices $`s,t\gt0`$ with $`\theta\gt0`$ exist only if $`\frac1p+\frac1q\lt\frac2{d-1}`$ (after Theorem D) | [`CoarseDeGiorgi.classical_moments_converse`](CoarseDeGiorgi/Statements/ClassicalMomentsConverse.lean) |
| sharpness of the coefficient range: for every $`\theta_0\le0`$, a scalar field $`a(y)I`$ with finite quasi-norms or Lebesgue norms and a solution $`u\ge1`$ unbounded near every point of the segment $`\{(x_1,0):\lvert x_1\rvert\lt\frac12\}`$ (Theorem F) | [`CoarseDeGiorgi.sharpness`](CoarseDeGiorgi/Statements/Sharpness.lean) |
| optimal powers of $`\Theta`$: uniformly elliptic fields $`\mathbf a_\varepsilon`$ with $`\Theta\asymp\varepsilon^{-2\theta}`$ and solutions for which the ratio of the two sides of the $`L^\eta`$ bound, with any smaller power, tends to infinity (Proposition 11.2) | [`CoarseDeGiorgi.optimal_powers`](CoarseDeGiorgi/Statements/OptimalPowers.lean) |
| optimal exponent range of the weak Harnack inequality: a radial field $`a(\lvert x\rvert)I`$ satisfying the hypothesis and supersolutions $`u_\varepsilon`$ with a fixed positive infimum on $`\frac12\square_0`$ whose normalized $`L^\eta`$ means on $`\frac58\square_0`$ tend to infinity, for every $`\eta\gt r^*/2`$ (Proposition 11.3) | [`CoarseDeGiorgi.weak_harnack_sharpness`](CoarseDeGiorgi/Statements/WeakHarnackSharpness.lean) |
| cubes instead of simplices: $`\widetilde\Lambda\le\Lambda\le C\widetilde\Lambda`$ and $`C^{-1}\widetilde\lambda\le\lambda\le\widetilde\lambda`$ for $`s\lt\frac12(1-\frac1p)`$, $`t\lt\frac12(1-\frac1q)`$ (Proposition 3.4) | [`CoarseDeGiorgi.cubical_simplicial_equivalence`](CoarseDeGiorgi/Statements/CubicalSimplicialEquivalence.lean) |
| Theorems A and C and Corollary B under the cubical hypothesis, with $`\widetilde\Theta`$ in place of $`\Theta`$ (after (3.20)) | [`CoarseDeGiorgi.local_boundedness_cubical`](CoarseDeGiorgi/Statements/LocalBoundednessCubical.lean), [`CoarseDeGiorgi.weak_harnack_cubical`](CoarseDeGiorgi/Statements/WeakHarnackCubical.lean), [`CoarseDeGiorgi.harnack_cubical`](CoarseDeGiorgi/Statements/HarnackCubical.lean) |

The same directory states the definitions used in these theorems and the
intermediate results of the manuscript on which their proofs rest, for
example the interpolation on Whitney simplices `whitney_interpolation`, the
existence of a good radius `good_radius_exists`, the piecewise harmonic
extension `harmonic_extension`, the Caccioppoli inequality
`caccioppoli_inequality`, the bound `energy_to_supremum` of the supremum by
the energy, the crossover estimate `crossover_estimate`, the weak Harnack
inequality at the exponent $`r/4`$ that the proof of Theorem C establishes
first (`weak_harnack`), the steps of the endpoint: `interior_weak_harnack`,
`interior_harnack`, `dirichlet_reconstruction`, `endpoint_potential` and
`source_mass_potential`, and the two results of Appendix B: the comparison of
averages over simplices or cubes with Gaussian averages, `besov_averages`
(Proposition B.1), and the bound of the cube quasi-norm by negative Sobolev
norms, `negative_sobolev_bound` (Lemma B.2).
[`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps every numbered definition and
result of the manuscript to its Lean declaration, or records that it is not
formalized.

The Harnack inequality, for example, reads:

```lean
theorem harnack (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSolution a (originCube 1) u G →
          eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u
```

The constant is chosen after $`d,p,q,s,t`$ and before the coefficient field and
the solution. The names in these statements mean the following.

| Name | Meaning |
| --- | --- |
| `Vec d`, `CoeffField d` | `Fin d → ℝ`, and fields of real `d × d` matrices on it (from `CoarseGraining`) |
| `originCube ρ` | the open cube $`(-\rho/2,\rho/2)^d`$, that is, $`\rho\square_0`$ |
| `IsWeightedCoeffOn V a` | `a` is a.e. strongly measurable and a.e. positive definite (Mathlib's `PosDef`, which includes symmetry) on `V`, with integrable trace and inverse trace |
| `upperMoment`, `lowerMoment` | the coarse ellipticity constants $`\Lambda_{s,1,p}(\square_0)`$ and $`\lambda_{t,1,q}(\square_0)`$, valued in `ℝ≥0∞` |
| `contrast` | $`\Theta`$, the quotient `upperMoment / lowerMoment` in `ℝ≥0∞` |
| `paramTheta d p q s t` | $`\theta=1-s-t-\frac{d-1}2(\frac1p+\frac1q)`$ |
| `IsWeightedSubsolution`, `IsWeightedSupersolution`, `IsWeightedSolution` | membership in $`H^1_{\mathbf a}`$ with the explicit gradient `G`, and the weak inequality or equation against smooth compactly supported tests (nonnegative tests for subsolutions); `u` is a supersolution when `-u` is a subsolution |
| `positivePart u`, `LocallyBoundedAbove V u` | $`u_+=\max(u,0)`$, and a.e. boundedness above on every compact subset of `V` |
| `nonnegativeEssInf V u` | the essential infimum of $`u`$ on `V`, in `ℝ≥0∞` |
| `normalizedLpMoment b V u` | $`\bigl(\frac1{\lvert V\rvert}\int_V\lvert u\rvert^b\bigr)^{1/b}`$ |
| `paramR q`, `rStarParam q t`, `harnackEtaParam q` | $`r=2q/(q+1)`$, $`r^*=dr/(d-(1-t)r)`$, and $`r/4=q/(2(q+1))`$, the exponent of `weak_harnack` |
| `besovCubeNorm b _ s p` | the cube quasi-norm $`\lVert\mathbf b\rVert_{\mathring{\underline B}^{-2s}_{p,1/2}(\square_0)}`$ |
| `IsWeakDerivArray U j w D` | `D` is the array $`\nabla^jw`$ of the weak partial derivatives of order $`j`$ of `w` on `U`, one entry for each of the $`d^j`$ ordered index tuples |
| `sobolevNorm U _ β ξ _ _ w` | $`\lVert w\rVert_{W^{\beta,\xi}(U)}`$ for an open `U`: an infimum over arrays of weak derivatives, which equals the manuscript's value (`sobolevNorm_eq_of_isWeakDerivArray`) and is $`\infty`$ when the weak derivatives do not exist |
| `negSobolevNorm U _ b _ β p _ _` | the negative Sobolev norm $`\lVert\mathbf b\rVert_{W^{-\beta,p}(U)}`$, the dual norm tested on bounded functions |
| `cubeUpperMoment`, `cubeLowerMoment`, `cubeContrast` | $`\widetilde\Lambda_{s,1,p}(\square_0)`$, $`\widetilde\lambda_{t,1,q}(\square_0)`$ and $`\widetilde\Theta`$, computed on the triadic subcubes |

The Lean names keep the word "response" of the coarse-grained matrices:
`upperResponse` is $`\mathbf a(U)`$ and `lowerResponseInv` is
$`\mathbf a_{\ast}^{-1}(U)`$. Reading a Mathlib-only challenge (below) is the
quickest way to inspect a precise claim without the library's definitions.

## Scope and faithfulness

The formal statements follow the manuscript with the following rendering
conventions and exceptions.

- **Not formalized.** The infinite exponents in Theorem D, in Appendix B, in
  Proposition 3.4 and in Lemma C.1; the summability indices other than one in
  Proposition 3.4; and the remarks and the comparisons with other work, among
  them the remark that the growth $`\exp(C\sqrt\Theta)`$ of the Harnack
  constant cannot be improved. Some intermediate results are formalized in
  the forms that the proofs use.
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md) gives the status of every numbered
  statement. Section 1.5 of the manuscript describes the formalization in
  summary: it does not mention the infinite exponents in Theorem D and in
  Appendix B, and among the proofs that differ from the manuscript's it
  names only that of Lemma 4.2. The precise account is the one given here
  and in [`CORRESPONDENCE.md`](CORRESPONDENCE.md).
- **Space and cubes.** The ambient space is `Fin d → ℝ`; cubes are open and
  centred at the origin; the operator norm is the ℓ² operator norm.
- **Solution classes.** Sub-, super- and solutions carry an explicit weak
  gradient `G`; membership in $`H^1_{\mathbf a}`$ is closure of smooth functions
  in the squared mean plus the weighted energy, with convergence in $`L^1`$ on
  compact subsets.
- **Extended values.** Norms, the coarse ellipticity constants and
  $`\Theta`$ are valued in `ℝ≥0∞`; the Harnack constants use the real value of
  $`\Theta`$, which is finite under the hypotheses. For $`0\lt\eta\lt1`$ the quantity
  $`\lVert\cdot\rVert_{L^\eta}`$ is Mathlib's `eLpNorm`,
  $`(\int\lvert f\rvert^\eta)^{1/\eta}`$, as in the manuscript.
- **Theorem C.** The weak Harnack inequality is one declaration for the
  whole range $`0\lt\eta\le r^*/2`$, with the constant chosen after $`\eta`$, as in
  the manuscript; the Harnack inequality is a second declaration.
- **Theorem D.** Parts (i), (ii) and (iii) are formalized for finite
  exponents, in three declarations; in part (iii) the condition
  $`0\lt\varepsilon\le2\min\{s,t\}`$ is written as $`\varepsilon\le2s`$ and
  $`\varepsilon\le2t`$. The consequences of parts (i) and (ii) for Theorems A
  and C and Corollary B are composed in the Mathlib-only restatements below;
  those of part (iii) are Corollary E. The infinite exponents are not
  formalized.
- **Corollary E.** The local bound and the Harnack inequality are two
  declarations, `local_boundedness_sobolev` and `harnack_sobolev`, each with
  its own constant (the larger of the two serves both). The slack $`\theta`$ is
  an argument fixed by its defining equation, and $`\mathbf a\in L^1`$,
  $`\mathbf a^{-1}\in L^1`$ is the entrywise integrability that the negative
  Sobolev norms take as arguments.
- **Sobolev and negative Sobolev norms.** `sobolevNorm` and `negSobolevNorm`
  are defined on open sets (they take a proof that the set is open) and for
  finite exponents. The norm of an array of derivatives is the Euclidean norm
  over its $`d^j`$ ordered index tuples. The negative Sobolev norm takes the
  entrywise integrability of the matrix field as an argument, as the cube
  quasi-norm does; the comparators state it without that argument.
- **Appendix B.** Proposition B.1 is one declaration, for both families of
  cells and with one constant, for $`1\le p\lt\infty`$; Lemma B.2 is stated for
  $`1\lt p\lt\infty`$. The case $`p=\infty`$ of both, and the remark after Proposition
  B.1 comparing the Gaussian averages with the Besov space defined through
  the Fourier transform (cited from Kerkyacharian and Petrushev), are not
  formalized.
- **Cubes and simplices.** Proposition 3.4, Lemma C.1 and (3.20) are
  formalized for summability index one and finite exponents, the cases that
  the definitions of the coarse ellipticity constants cover; the
  cases $`p=\infty`$ or $`q=\infty`$ and the independence of the constant from the
  summability index are not formalized. The countable subadditivity (2.15)
  and (2.16) is stated for partitions into bounded open convex pieces.
- **The cube quasi-norm.** `besovCubeNorm` is defined for finite $`p`$ and takes
  the entrywise integrability of the matrix field as an argument; its
  Mathlib-only restatements carry no such argument.
- **Theorem F.** `sharpness` calls the integrability exponents `ξ` and `ζ`
  (the manuscript's $`p`$ and $`q`$). It gives $`a`$ as a Borel function on all of
  `Vec d`, positive at every point, with $`a(x)=a(x')`$ whenever $`x`$ and $`x'`$
  differ only in the coordinate $`x_1`$ (the coordinate `0`); the field is
  `fun x => a x • 1`. It also asserts the entrywise integrability of
  $`\mathbf a`$ and $`\mathbf a^{-1}`$ that the quasi-norms take as arguments. The
  bound $`u\ge1`$ holds almost everywhere in $`\square_0`$,
  $`\mathrm{ess\,sup}\,u=\infty`$ is written as
  `eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) = ⊤`, and the
  unboundedness near a point $`x`$ of the segment says that the same norm is
  infinite on $`N\cap\square_0`$ for every neighborhood $`N`$ of $`x`$.
- **Proposition 11.2.** `optimal_powers` indexes the fields, the solutions and
  their gradients by every real $`\varepsilon`$ and asserts the properties for
  $`0\lt\varepsilon\lt\frac18`$. Each comparison $`\asymp`$ is written with one
  explicit constant $`C\ge1`$, independent of $`\varepsilon`$ (and of $`\rho_2`$,
  and depending on $`\eta`$, for the $`L^\eta`$ norms). The height is stated for
  $`\tfrac12\le\rho_1\lt1`$ and the $`L^\eta`$ comparison for
  $`\tfrac12\lt\rho_2\le1`$, which covers every pair of radii in the final
  assertion. That assertion is a limit in `ℝ≥0∞` as $`\varepsilon\to0^+`$
  (`Tendsto … (𝓝[>] 0) (𝓝 ⊤)`); the comparisons make every quantity in the
  ratio finite and positive.
- **Proposition 11.3.** `weak_harnack_sharpness` asserts the existence of a
  profile $`a`$ with the field $`a(\lvert x\rvert)I`$, $`\lvert x\rvert`$ the Euclidean
  norm; the supersolutions are indexed by every real $`\varepsilon`$, with the
  properties asserted for $`0\lt\varepsilon\lt\frac18`$, and the limit is taken in
  `ℝ≥0∞` as $`\varepsilon\to0^+`$.
- **Dimension.** The main results assume $`d\ge3`$, the standing assumption
  of the manuscript, except Proposition 3.4, which is stated for every $`d`$,
  as are the intermediate statements whose proofs work in every dimension,
  such as Proposition B.1 and Lemma B.2.
- **Proofs.** The formal proofs follow the manuscript, with a few recorded
  differences: the reconstruction estimate of Lemma 4.2 is proved by another
  argument; the scale decomposition of Lemma 9.6 solves Dirichlet problems on
  the cube, with Calderón–Zygmund estimates for cubes and Morrey's inequality
  on small cubes, in place of Newtonian potentials on $`\mathbb R^d`$;
  Proposition 9.7 does not use the positivity of the potential and sums over
  its level sets in place of the decreasing rearrangement; Lemma 9.8 obtains
  the potential from the Riesz representation theorem in place of the
  Lax–Milgram lemma and does not use the uniqueness of the capacitary
  function; the supersolutions of Proposition 11.3, the subsolution in
  each cylinder of Theorem F and the Whitney cubes of Lemma C.1 are slightly
  different; Lemma B.2 bounds the derivatives of Gaussian averages by a wider
  Gaussian in place of Young's inequality, and tests with one extremal
  function in place of a supremum over the unit ball of $`L^{p'}`$; and some
  intermediate lemmas carry larger powers of
  $`(\rho_2-\rho_1)^{-1}`$. [`CORRESPONDENCE.md`](CORRESPONDENCE.md) lists them.

## Verified against Mathlib-only statements

So that the claims can be checked without trusting the library, the main
results are restated using **only Mathlib**, with every definition written out,
in a challenge file under
[`CoarseDeGiorgiAudit/Challenge/`](CoarseDeGiorgiAudit/Challenge/). Each
challenge contains one intentional `sorry`. The matching file under
[`CoarseDeGiorgiAudit/Solution/`](CoarseDeGiorgiAudit/Solution/) proves the
identical statement from the library, and
[`leanprover/comparator`](https://github.com/leanprover/comparator) checks the
pair with both the Lean kernel and the independent
[`nanoda`](https://github.com/robsimmons/nanoda_lib) kernel, accepting only
`propext`, `Classical.choice` and `Quot.sound`. The detailed list, with what
each restatement contains and how it is derived, is in
[`COMPARATORS.md`](COMPARATORS.md).

| Configuration | Statement |
| --- | --- |
| [`Harnack`](comparators/Harnack.json) | Harnack inequality in terms of the coarse ellipticity constants (Theorem C) |
| [`WeakHarnack`](comparators/WeakHarnack.json) | weak Harnack inequality in the same terms, for every exponent $`0\lt\eta\le r^*/2`$, with a constant depending on $`\eta`$ (Theorem C) |
| [`ResponseQuadraticForms`](comparators/ResponseQuadraticForms.json) | the coarse-grained matrices of the two challenges above, defined by polarization, are positive definite and their quadratic forms are the variational quantities (Propositions 2.2 and 2.3) |
| [`LocalBoundednessLpLq`](comparators/LocalBoundednessLpLq.json) | $`L^2`$ and $`L^\eta`$ local boundedness with the powers $`\kappa`$ and $`2\kappa/\eta`$ of $`1+M`$, $`M=\lVert\mathbf a\rVert_{L^p}\lVert\mathbf a^{-1}\rVert_{L^q}`$, for every $`\kappa\gt(d-1)/(4\theta_0)`$, where $`\frac1p+\frac1q\lt\frac2{d-1}`$ and $`\theta_0=1-\frac{d-1}2(\frac1p+\frac1q)`$ (Theorem D (i) with Theorem A and Corollary B) |
| [`HarnackLpLq`](comparators/HarnackLpLq.json) | Harnack inequality with constant $`\exp(C\sqrt M)`$ in the same range (Theorem D (i) with Theorem C) |
| [`WeakHarnackLpLq`](comparators/WeakHarnackLpLq.json) | weak Harnack inequality in the same setting, for every exponent $`0\lt\eta\lt dq/(dq+d-2q)`$, the value of $`r^*/2`$ at $`t=0`$ |
| [`LocalBoundednessUniform`](comparators/LocalBoundednessUniform.json) | uniformly elliptic local boundedness with every power $`\kappa\gt(d-1)/4`$ of $`1+\Lambda/\lambda`$ |
| [`HarnackUniform`](comparators/HarnackUniform.json) | uniformly elliptic Harnack inequality: symmetric $`\mathbf a`$ with $`\lambda\le\mathbf a\le\Lambda`$ gives $`\exp(C\sqrt{\Lambda/\lambda})`$ |
| [`WeakHarnackUniform`](comparators/WeakHarnackUniform.json) | uniformly elliptic weak Harnack inequality for every exponent $`0\lt\eta\lt d/(d-2)`$, with the constant $`\exp(C\sqrt{\Lambda/\lambda})`$ |
| [`LocalBoundednessBesov`](comparators/LocalBoundednessBesov.json) | $`L^2`$ and $`L^\eta`$ local boundedness with the powers $`\frac{d-1}{4\theta}`$ and $`\frac{d-1}{2\eta\theta}`$ of $`N=\lVert\mathbf a\rVert_{\mathring{\underline B}^{-2s}_{p,1/2}}\lVert\mathbf a^{-1}\rVert_{\mathring{\underline B}^{-2t}_{q,1/2}}`$ (Theorem D (ii) with Theorem A and Corollary B) |
| [`HarnackBesov`](comparators/HarnackBesov.json) | Harnack inequality with constant $`\exp(C\sqrt N)`$ (Theorem D (ii) with Theorem C) |
| [`WeakHarnackBesov`](comparators/WeakHarnackBesov.json) | weak Harnack inequality in the same setting, for every exponent $`0\lt\eta\le r^*/2`$ |
| [`LocalBoundednessSobolev`](comparators/LocalBoundednessSobolev.json) | $`L^2`$ local boundedness with the power $`\frac{d-1}{2\theta}`$ of $`N=\lVert\mathbf a\rVert_{W^{-\alpha,p}}\lVert\mathbf a^{-1}\rVert_{W^{-\beta,q}}`$, where $`\theta=1-\frac{\alpha+\beta}2-\frac{d-1}2(\frac1p+\frac1q)\gt0`$, with the negative Sobolev norms written out (Corollary E) |
| [`HarnackSobolev`](comparators/HarnackSobolev.json) | Harnack inequality with constant $`\exp(C\sqrt N)`$ in the same setting (Corollary E) |
| [`Sharpness`](comparators/Sharpness.json) | for every $`\theta_0\le0`$: a positive scalar field $`a(y)I`$, with $`a`$ independent of $`x_1`$, finite cube quasi-norms of orders $`-\alpha`$, $`-\beta`$ (Lebesgue norms for a zero order), and a weighted solution $`u\ge1`$ with $`\mathrm{ess\,sup}_{\frac12\square_0}u=\infty`$ and $`0\lt\mathrm{ess\,inf}_{\frac12\square_0}u\lt\infty`$, essentially unbounded near every point of the segment $`\{(x_1,0):\lvert x_1\rvert\lt\frac12\}`$ (Theorem F) |
| [`SharpnessPolynomial`](comparators/SharpnessPolynomial.json) | for $`\theta\gt0`$: uniformly elliptic fields $`\mathbf a_\varepsilon`$ and solutions $`u_\varepsilon`$ with $`\Lambda_{s,1,p}\asymp\Theta\asymp\varepsilon^{-2\theta}`$, $`\lambda_{t,1,q}\asymp1`$, $`\lVert(u_\varepsilon)_+\rVert_{L^\infty(\rho_1\square_0)}=1+\rho_1^2/4`$ and $`\lVert(u_\varepsilon)_+\rVert_{L^\eta(\rho_2\square_0)}\asymp\varepsilon^{(d-1)/\eta}`$, so that no power of $`\Theta`$ below $`\frac{d-1}{2\eta\theta}`$ works (Proposition 11.2) |
| [`SharpnessWeakHarnack`](comparators/SharpnessWeakHarnack.json) | for $`\theta\gt0`$: a radial field $`a(\lvert x\rvert)I`$ with $`\Lambda_{s,1,p}\lt\infty`$ and $`\lambda_{t,1,q}\gt0`$, and nonnegative weighted supersolutions $`u_\varepsilon`$ with the same positive essential infimum on $`\frac12\square_0`$, whose normalized $`L^\eta`$ means on $`\frac58\square_0`$ tend to infinity as $`\varepsilon\to0^+`$ for every $`\eta\gt r^*/2`$ (Proposition 11.3) |

## Relation to CoarseGraining and to DeGiorgi

**CoarseGraining.** The library
[`CoarseGraining`](https://github.com/scottnarmstrong/CoarseGraining)
(Armstrong and Kuusi) supplies the coefficient fields, weak derivatives and
Sobolev spaces, triadic cubes, cube averages and Poincaré inequalities on which
this development is built. It is a pinned Lake dependency.

**DeGiorgi.** The earlier repository
[`DeGiorgi`](https://github.com/scottnarmstrong/DeGiorgi) (Armstrong and
Kempe, [arXiv:2604.05984](https://arxiv.org/abs/2604.05984)) formalizes
De Giorgi–Nash–Moser theory for uniformly elliptic, possibly nonsymmetric
coefficients on balls in dimension $`d\ge3`$: local boundedness, the weak
Harnack and Harnack inequalities, and Hölder continuity. For **symmetric**
coefficients, this repository supersedes its local boundedness, weak Harnack
and Harnack results and goes well beyond uniform ellipticity:

- the uniformly elliptic Harnack inequality (`HarnackUniform` above) has the
  constant $`\exp(C\sqrt{\Lambda/\lambda})`$, the same dependence as DeGiorgi's
  `harnack`;
- the uniformly elliptic weak Harnack inequality (`WeakHarnackUniform` above)
  holds for every exponent $`0\lt\eta\lt d/(d-2)`$, the range of DeGiorgi's
  `weak_harnack`, with the constant $`\exp(C\sqrt{\Lambda/\lambda})`$, the same
  dependence as there;
- the uniformly elliptic local boundedness estimate
  (`LocalBoundednessUniform` above) holds with every power $`\kappa\gt(d-1)/4`$ of
  $`1+\Lambda/\lambda`$, where DeGiorgi's `linfty_subsolution_DeGiorgi_normalized`
  has the power $`d/4`$ of $`\Lambda`$ (with $`\lambda`$ normalized to $`1`$);
- all three come from theorems for degenerate and unbounded coefficients.

DeGiorgi remains the reference for what is not covered here: Hölder
continuity of solutions (`holder_Moser`), nonsymmetric coefficients, and
statements on balls for the classical $`H^1`$ weak solutions (here, cubes and
the weighted class $`H^1_{\mathbf a}`$; the two solution classes are not compared
formally in either repository).

## Building and verifying

The project uses [`elan`](https://github.com/leanprover/elan) and Lake; the
toolchain is pinned in [`lean-toolchain`](lean-toolchain).

```bash
# from the repository root
lake exe cache get   # prebuilt mathlib oleans
lake build           # compile the CoarseGraining dependency and every module of the library
```

`lake exe cache get` requires the committed
[`lake-manifest.json`](lake-manifest.json). The `CoarseGraining` dependency has
no olean cache and is compiled from source on the first build, which dominates
its time. Keep the committed manifest; avoid `lake update` and `lake clean`.

`import CoarseDeGiorgi` loads the main results.

To print the axioms of the main theorems and of the comparator solutions:

```bash
lake build CoarseDeGiorgiAudit                    # if not built yet
lake env lean CoarseDeGiorgiAudit/AxiomsAudit.lean
```

Each of the 34 declarations (17 theorems of the library and the 17 theorems
of the comparator solutions) must be reported as
`depends on axioms: [propext, Classical.choice, Quot.sound]` (Lean wraps the
list over several lines for long names).

To run the comparator checks (Linux with Landlock support; `landrun` and
`nanoda_bin` on the `PATH`, or set `COMPARATOR_LANDRUN` and `COMPARATOR_NANODA`;
the [`Comparators` workflow](.github/workflows/comparators.yml) builds pinned
revisions of both):

```bash
lake build CoarseDeGiorgiAudit          # challenges and solutions (not a default target)
scripts/verify_comparator.sh            # all 17 configurations in comparators/
scripts/verify_comparator.sh HarnackLpLq  # or a single one
```

The script builds pinned revisions of `leanprover/comparator` and
`leanprover/lean4export` in a user cache (`~/.cache/cdg-comparator`, or
`$CDG_COMPARATOR_CACHE`) and runs each configuration in
[`comparators/`](comparators/). A passing check prints
`Your solution is okay!`, and the script then prints `=== <Name>: PASS`.
Building the challenges reports one `declaration uses 'sorry'` warning per
challenge, as intended.

Compilation establishes that Lean accepts the proofs. Mathematical review
remains necessary to check that the formal statements and definitions express
the intended results.

## Repository layout

| Location | Contents |
| --- | --- |
| [`CoarseDeGiorgi/Statements/`](CoarseDeGiorgi/Statements/) | the statement layer, one declaration per file: the main theorems, the intermediate named results, and the definitions they use |
| [`CoarseDeGiorgi/Weighted/`](CoarseDeGiorgi/Weighted/) | the weighted space $`H^1_{\mathbf a}`$, truncations and testing, harmonic replacement and the coarse-grained matrices |
| [`CoarseDeGiorgi/Foundations/`](CoarseDeGiorgi/Foundations/), [`CoarseDeGiorgi/Moments/`](CoarseDeGiorgi/Moments/) | simplices and triangulations, fractional Sobolev spaces, reconstruction from triadic averages of the gradient, chain rules, scalar iteration lemmas |
| [`CoarseDeGiorgi/LowerFractional/`](CoarseDeGiorgi/LowerFractional/), [`CoarseDeGiorgi/Localization/`](CoarseDeGiorgi/Localization/), [`CoarseDeGiorgi/Selection/`](CoarseDeGiorgi/Selection/), [`CoarseDeGiorgi/GoodRadius/`](CoarseDeGiorgi/GoodRadius/) | the embedding into fractional Sobolev spaces, localization, and the choice of a good radius |
| [`CoarseDeGiorgi/Whitney/`](CoarseDeGiorgi/Whitney/), [`CoarseDeGiorgi/ExteriorIntegral/`](CoarseDeGiorgi/ExteriorIntegral/), [`CoarseDeGiorgi/GoodRadiusEnergy/`](CoarseDeGiorgi/GoodRadiusEnergy/), [`CoarseDeGiorgi/Adapters/`](CoarseDeGiorgi/Adapters/) | Whitney cubes and simplices, the interpolation at free vertices, the piecewise affine and piecewise harmonic extensions, the exterior integral and the energy in a cube with a good radius |
| [`CoarseDeGiorgi/CgCaccioppoli/`](CoarseDeGiorgi/CgCaccioppoli/), [`CoarseDeGiorgi/Recurrence/`](CoarseDeGiorgi/Recurrence/), [`CoarseDeGiorgi/TheoremA/`](CoarseDeGiorgi/TheoremA/), [`CoarseDeGiorgi/Assembly/`](CoarseDeGiorgi/Assembly/) | the Caccioppoli inequality, the two-level recurrence, the bound of the supremum by the energy, and the $`L^\infty`$ bound |
| [`CoarseDeGiorgi/PowerCacc/`](CoarseDeGiorgi/PowerCacc/), [`CoarseDeGiorgi/Harnack/`](CoarseDeGiorgi/Harnack/) | weak Harnack and Harnack inequalities: the Caccioppoli inequality for powers, the logarithmic estimate, Bombieri's lemma, crossover and iterations |
| [`CoarseDeGiorgi/Endpoint/`](CoarseDeGiorgi/Endpoint/) | the endpoint $`\eta=r^*/2`$ of the weak Harnack inequality: rescaling to small cubes and chaining, the reconstruction with zero boundary values (Dirichlet problems on the cube, Morrey's inequality on cubes), potentials of measures, the source measure and the capacitary comparison, and the completion of Theorem C |
| [`CoarseDeGiorgi/Cubical/`](CoarseDeGiorgi/Cubical/) | cubes instead of simplices (Appendix C): countable subadditivity, Whitney decompositions of simplices, Proposition 3.4 and its consequences |
| [`CoarseDeGiorgi/CoefficientConditions/`](CoarseDeGiorgi/CoefficientConditions/), [`CoarseDeGiorgi/Besov/`](CoarseDeGiorgi/Besov/) | conditions on the coefficients (Theorem D): integrability and cube quasi-norms |
| [`CoarseDeGiorgi/NegSobolev/`](CoarseDeGiorgi/NegSobolev/) | negative Sobolev norms (Appendix B, Theorem D (iii), Corollary E): the Gaussian kernel and bounds for its derivatives, averages over simplices or cubes against Gaussian averages, the Sobolev norms of Gaussian averages of test functions, duality and the geometric series |
| [`CoarseDeGiorgi/SharpnessExamples/`](CoarseDeGiorgi/SharpnessExamples/), [`CoarseDeGiorgi/Sharpness/`](CoarseDeGiorgi/Sharpness/) | the examples of Section 11: averages of cylinders, the scalar cylinders of Theorem F with their quasi-norms and harmonic replacement, the single anisotropic cylinder of Proposition 11.2 with the bounds on its coarse ellipticity constants, and the radial field and supersolutions of Proposition 11.3; calculus near a line |
| [`CoarseDeGiorgiAudit/`](CoarseDeGiorgiAudit/) | Mathlib-only comparator challenges and their solutions, and the axiom audit `AxiomsAudit.lean` |
| [`comparators/`](comparators/), [`scripts/verify_comparator.sh`](scripts/verify_comparator.sh) | comparator configurations and runner |
| [`COMPARATORS.md`](COMPARATORS.md) | the comparator statements in detail |
| [`CORRESPONDENCE.md`](CORRESPONDENCE.md) | the paper-to-Lean map |
| [`paper/`](paper/) | the manuscript (LaTeX source and PDF) |
| [`.github/workflows/`](.github/workflows/) | CI, on every push and pull request to `main`: [`build.yml`](.github/workflows/build.yml) builds the library and the comparator files and runs the axiom audit; [`comparators.yml`](.github/workflows/comparators.yml) runs the comparator checks |

## How this was built

The Lean code was written by AI agents under the supervision of the authors.
Claude Opus 5.5
(Anthropic, in Claude Code) coordinated the work and audited the statements
and the completed proofs; GPT-6 Luna, GPT-6 Sol and GPT-6.1 Sol (OpenAI, in Codex) and
Claude Sonnet 5 (Anthropic) wrote the Lean code. The work used less than one weekly quota of a ChatGPT
subscription and less than half of a Claude Max weekly quota. The authors
reviewed the theorem statements before proof development; separate agent
reviews checked the statements against the manuscript and audited each
completed proof. Lean checks the proofs, and the comparator files make the
statements available for independent inspection. The models, tools, cost and
review status are recorded in [`formalization.yaml`](formalization.yaml),
following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by

- **Scott Armstrong** — CNRS and Laboratoire Jacques-Louis Lions, Sorbonne
  Université; Courant Institute School of Mathematics, Computing, and Data
  Science, New York University
- **Benny Avelin** — Department of Mathematics, Uppsala University
- **Tuomo Kuusi** — Department of Mathematics and Statistics, University of
  Helsinki
- **Aatu Turpeinen** — Department of Mathematics and Statistics, University of
  Helsinki

If you use this formalization, please cite it using the metadata in
[`CITATION.cff`](CITATION.cff).

## Acknowledgements

Scott Armstrong and Tuomo Kuusi were supported by the European Research Council
(ERC) under the European Union's Horizon Europe research and innovation
programme, grant agreement No. 101200828. Tuomo Kuusi and Aatu Turpeinen were
supported by the Academy of Finland.

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4) and
[CoarseGraining](https://github.com/scottnarmstrong/CoarseGraining); the
comparator checks use
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)). The manuscript source and PDF in `paper/` are © the authors,
all rights reserved, and are not covered by the Apache license.
