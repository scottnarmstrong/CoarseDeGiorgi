# Comparator challenges

This page lists the theorems of the formalization that are stated
independently of the library and checked with
[leanprover/comparator](https://github.com/leanprover/comparator). They are
the results of the manuscript *Coarse ellipticity and De
Giorgi–Nash–Moser theory in the optimal range* by Scott Armstrong, Benny
Avelin, Tuomo Kuusi and Aatu Turpeinen, which is included in this repository
as a [PDF](paper/coarse-grained-dgnm.pdf).
Theorem and equation numbers below refer to that manuscript.

## What a comparator challenge is

Each comparator is a pair of Lean files and a configuration.

- **The challenge**, `CoarseDeGiorgiAudit/Challenge/<Name>.lean`, is one
  self-contained file between about 140 and 320 lines long. It imports only
  `Mathlib` and writes out every definition it needs: cubes, coefficient
  fields, the weighted energy space, weak subsolutions, the triangulations,
  the coarse-grained matrices and the coarse ellipticity constants. It then
  states one theorem whose proof is a
  single intentional `sorry`. A reader can check the claim against the
  manuscript without opening the library.
- **The solution**, `CoarseDeGiorgiAudit/Solution/<Name>.lean`, repeats the
  challenge's definitions and theorem statement and proves the theorem from
  the library.
- **The configuration**, `comparators/<Name>.json`, names the theorem and
  allows only the axioms `propext`, `Classical.choice` and `Quot.sound`. It
  also turns on the independent nanoda kernel (`"enable_nanoda": true`).

Comparator builds and exports both modules inside a
[landrun](https://github.com/zouuup/landrun) sandbox. It then checks three
things.

1. Every declaration in the challenge theorem's statement is identical in the
   solution environment. This covers the theorem type and, constant by
   constant, the whole dependency closure of that statement, including every
   definition the challenge writes out.
2. The solution's proof uses only the permitted axioms.
3. The Lean kernel accepts the solution environment, and so does
   [nanoda](https://github.com/robsimmons/nanoda_lib), an independent kernel
   implementation.

A successful run prints `Your solution is okay!`.

### What is trusted

The checks above assume the following.

- The Lean kernel is sound, or nanoda is: an error would have to occur in
  both kernels to go unnoticed.
- The comparator, `lean4export` and landrun work as intended.
- Mathlib's definitions mean what they say. The challenges use Mathlib's
  measure theory (`volume`, `eLpNorm`, `essInf`, `Integrable`, lower
  integrals), the Fréchet derivative `fderiv`, `Matrix.PosDef` and the
  operator norm on matrices, in `SharpnessPolynomial` also
  `Matrix.IsHermitian` and limits (`Filter.Tendsto`), in `Sharpness`
  neighborhoods (`nhds`), in `SharpnessWeakHarnack` the square root
  `Real.sqrt` and limits (`Filter.Tendsto`, `𝓝[>] 0`), and in
  `LocalBoundednessSobolev` and `HarnackSobolev` the iterated derivative
  `iteratedFDeriv`, `LocallyIntegrableOn`, `HasCompactSupport` and `tsupport`,
  the product measure `Measure.prod`, `MemLp`, `Nat.floor` and `Real.sqrt`.
- The challenge definitions express the intended mathematics. Comparator
  cannot check this; you have to read the challenge. The sections below say,
  for each challenge, how its definitions are written, so you know what to
  compare with the manuscript.

You do not need to trust anything in the library itself: not its
definitions, not its intermediate results, and not the bridge lemmas the
solutions use to transport statements.

### Running the checks

From the repository root, with the pinned toolchain installed:

```sh
lake exe cache get
scripts/verify_comparator.sh HarnackLpLq      # one comparator
scripts/verify_comparator.sh                  # every configuration that has a solution
```

The script fetches and builds pinned revisions of comparator and
`lean4export`, which must use the project's Lean toolchain. It keeps them
under `~/.cache/cdg-comparator`, or under `$CDG_COMPARATOR_CACHE` if that is
set. It expects `landrun` and nanoda's `nanoda_bin` either on `PATH` or given
by the variables `COMPARATOR_LANDRUN` and `COMPARATOR_NANODA`. It runs on
Linux with Landlock support.

For each comparator the script prints comparator's own output, ending in
`Your solution is okay!` on success, and then a line `=== <Name>: PASS` or
`=== <Name>: FAIL`. The
[`Comparators` workflow](.github/workflows/comparators.yml) builds pinned
revisions of landrun and nanoda and runs the script on every configuration,
on every push and pull request to `main`.

## The comparators

| Comparator | What it states | Manuscript | Status |
|---|---|---|---|
| [`Harnack`](CoarseDeGiorgiAudit/Challenge/Harnack.lean) | Harnack inequality, constant $`\exp(C\sqrt\Theta)`$ in the coarse ellipticity ratio | Theorem C, (1.11) | passes |
| [`WeakHarnack`](CoarseDeGiorgiAudit/Challenge/WeakHarnack.lean) | Weak Harnack inequality for every exponent $`0\lt\eta\le r^*/2`$, constant $`\exp(C\sqrt\Theta)`$ with $`C`$ depending on $`\eta`$ | Theorem C, (1.10) | passes |
| [`ResponseQuadraticForms`](CoarseDeGiorgiAudit/Challenge/ResponseQuadraticForms.lean) | The polarized coarse-grained matrices $`\mathbf a(\triangle)`$, $`\mathbf a_{\ast}^{-1}(\triangle)`$ are positive definite, with the directional quantities as quadratic forms | Propositions 2.2, 2.3 | passes |
| [`HarnackLpLq`](CoarseDeGiorgiAudit/Challenge/HarnackLpLq.lean) | Harnack inequality for $`\lvert\mathbf a\rvert\in L^p`$, $`\lvert\mathbf a^{-1}\rvert\in L^q`$, $`\frac1p+\frac1q\lt\frac2{d-1}`$ | Theorem D (i) with (1.11) | passes |
| [`WeakHarnackLpLq`](CoarseDeGiorgiAudit/Challenge/WeakHarnackLpLq.lean) | Weak Harnack inequality in the same range, for every exponent $`0\lt\eta\lt\frac{dq}{dq+d-2q}`$ | Theorem D (i) with (1.10) | passes |
| [`LocalBoundednessLpLq`](CoarseDeGiorgiAudit/Challenge/LocalBoundednessLpLq.lean) | $`L^2\to L^\infty`$ and $`L^\eta\to L^\infty`$ bounds in the same range | Theorem D (i) with Theorem A and Corollary B | passes |
| [`HarnackUniform`](CoarseDeGiorgiAudit/Challenge/HarnackUniform.lean) | Harnack inequality with constant $`\exp(C\sqrt{\Lambda/\lambda})`$ | Theorem D (i) with (1.11), $`p=q=d`$ | passes |
| [`WeakHarnackUniform`](CoarseDeGiorgiAudit/Challenge/WeakHarnackUniform.lean) | Weak Harnack inequality for every exponent $`0\lt\eta\lt\frac d{d-2}`$, constant $`\exp(C\sqrt{\Lambda/\lambda})`$ | Theorem D (i) with (1.10) | passes |
| [`LocalBoundednessUniform`](CoarseDeGiorgiAudit/Challenge/LocalBoundednessUniform.lean) | $`L^2\to L^\infty`$ bound with factor $`(1+\Lambda/\lambda)^\kappa`$, any $`\kappa\gt\frac{d-1}4`$ | Theorem A, (1.8), with Theorem D (i) | passes |
| [`HarnackBesov`](CoarseDeGiorgiAudit/Challenge/HarnackBesov.lean) | Harnack inequality under finite cube quasi-norms (1.12) | Theorem D (ii) with (1.11) | passes |
| [`WeakHarnackBesov`](CoarseDeGiorgiAudit/Challenge/WeakHarnackBesov.lean) | Weak Harnack inequality under (1.12), for every exponent $`0\lt\eta\le r^*/2`$ | Theorem D (ii) with (1.10) | passes |
| [`LocalBoundednessBesov`](CoarseDeGiorgiAudit/Challenge/LocalBoundednessBesov.lean) | $`L^2\to L^\infty`$ and $`L^\eta\to L^\infty`$ bounds under (1.12) | Theorem D (ii) with Theorem A and Corollary B | passes |
| [`LocalBoundednessSobolev`](CoarseDeGiorgiAudit/Challenge/LocalBoundednessSobolev.lean) | $`L^2\to L^\infty`$ bound with the power $`\frac{d-1}{2\theta}`$ of $`N=\lVert\mathbf a\rVert_{W^{-\alpha,p}}\lVert\mathbf a^{-1}\rVert_{W^{-\beta,q}}`$ | Corollary E, (1.18) | passes |
| [`HarnackSobolev`](CoarseDeGiorgiAudit/Challenge/HarnackSobolev.lean) | Harnack inequality with constant $`\exp(C\sqrt N)`$ | Corollary E, (1.19) | passes |
| [`Sharpness`](CoarseDeGiorgiAudit/Challenge/Sharpness.lean) | Sharpness of the range: for every $`\theta_0\le0`$, a scalar field $`a(y)I`$ with finite quasi-norms (1.12) or Lebesgue norms and a solution $`u\ge1`$ that is unbounded on $`\frac12\square_0`$ and near every point of a segment | Theorem F, (1.20) | passes |
| [`SharpnessPolynomial`](CoarseDeGiorgiAudit/Challenge/SharpnessPolynomial.lean) | Optimal powers of $`\Theta`$: uniformly elliptic fields with $`\Theta\asymp\varepsilon^{-2\theta}`$ for which no power below $`\frac{d-1}{2\eta\theta}`$ works | Proposition 11.2, (11.12)–(11.15) | passes |
| [`SharpnessWeakHarnack`](CoarseDeGiorgiAudit/Challenge/SharpnessWeakHarnack.lean) | Optimal exponent range of the weak Harnack inequality: a radial field satisfying the hypothesis and supersolutions for which (1.10) fails for every $`\eta\gt r^*/2`$ | Proposition 11.3, (11.19) | passes |

Each comparator has the configuration `comparators/<Name>.json`. The theorem
it checks is `CoarseDeGiorgiAudit.<Name>.<name>`: for example,
`CoarseDeGiorgiAudit.HarnackLpLq.harnackLpLq`.

## Conventions common to all challenges

The challenges were written separately, but they spell out the following
objects in the same way.

- **Space and cubes.** A point of $`\mathbb R^d`$ is a function `Fin d → ℝ`.
  `cube ρ` is the open cube $`\rho\square_0=(-\rho/2,\rho/2)^d`$, so `cube 1` is
  the manuscript's $`\square_0`$; `Sharpness` and `SharpnessPolynomial` call it
  `originCube ρ`, as the library does. Every statement assumes $`d\ge3`$, except
  `ResponseQuadraticForms`, which holds for every $`d`$.
- **Coefficients.** A coefficient field is any function from points to real
  $`d\times d`$ matrices. The standing assumption `IsWeightedCoeffOn (cube 1) a`
  requires three things on $`\square_0`$: $`\mathbf a`$ is almost everywhere
  strongly measurable; $`\mathbf a(x)`$ is positive definite almost everywhere
  (Mathlib's `Matrix.PosDef` includes symmetry); and
  $`\mathrm{tr}\mathbf a`$ and $`\mathrm{tr}\mathbf a^{-1}`$ are
  integrable. These are the qualitative hypotheses (2.1) of the
  manuscript's Section 2. None of the estimates depends on the two integrals. The
  challenges write $`\lvert\cdot\rvert`$ for the $`\ell^2`$ operator norm of a
  matrix; Lean selects it with `open scoped Matrix.Norms.L2Operator`.
- **The weighted space $`H^1_{\mathbf a}`$.** `MemH1a a V u G` says that $`u`$
  lies in $`H^1_{\mathbf a}(V)`$ and that $`G`$ is its gradient. The space is the
  closure of the smooth functions on $`V`$ that are integrable and have finite
  weighted energy $`\int_V\nabla\varphi\cdot\mathbf a\nabla\varphi`$, taken in
  the norm
  $`\bigl(\lvert(\varphi)_V\rvert^2+\int_V\nabla\varphi\cdot\mathbf a\nabla\varphi\bigr)^{1/2}`$
  (squared mean plus weighted energy; this is the manuscript's norm (2.2),
  and there is no $`L^2`$ term). Concretely, $`u`$ and $`G`$ are almost everywhere
  strongly measurable, and there is a sequence $`\varphi_n`$ of such functions
  with three properties: it is Cauchy in this norm; $`\varphi_n\to u`$ in $`L^1`$
  on every compact subset of $`V`$; and
  $`\int_V(\nabla\varphi_n-G)\cdot\mathbf a(\nabla\varphi_n-G)\to0`$.
- **Subsolutions, supersolutions and solutions.** A weighted subsolution on
  $`V`$ is a pair $`(u,G)`$ with `MemH1a a V u G` such that, for every smooth
  $`\varphi\ge0`$ with compact support in $`V`$, the function
  $`\nabla\varphi\cdot\mathbf aG`$ is integrable and
  $`\int_V\nabla\varphi\cdot\mathbf aG\le0`$. A supersolution is a $`u`$ with
  $`-u`$ a subsolution. A solution satisfies the equation with $`=0`$ against
  every smooth compactly supported $`\varphi`$. The integrability requirement is
  harmless, since $`\mathbf a\nabla u\in L^1`$ for every $`u\in H^1_{\mathbf a}`$
  (Proposition A.1). These are the manuscript's classes
  $`\mathcal C_{\mathrm{sub}}(\square_0)`$ and $`\mathcal C_{\mathrm{sol}}(\square_0)`$
  in (2.3). In particular, solutions have finite weighted energy on the whole
  of $`\square_0`$.
- **Norms.** Lebesgue norms are Mathlib's unnormalized `eLpNorm`, with values
  in $`[0,\infty]`$. For $`\eta\lt1`$ the "norm" $`\lVert f\rVert_{L^\eta}`$ is
  $`(\int\lvert f\rvert^\eta)^{1/\eta}`$. $`\lVert u\rVert_{L^\infty}`$ is the
  essential supremum of $`\lvert u\rvert`$. The essential infimum of a
  nonnegative $`u`$ is taken in $`[0,\infty]`$.
- **Constants.** Each estimate has the form "for all parameters there exist
  constants such that for every coefficient field and every function …".
  The constants therefore depend only on the parameters listed before them
  (such as $`d,p,q,s,t`$), never on $`\mathbf a`$ or $`u`$. The three sharpness
  challenges are not estimates: for all parameters in their ranges they
  assert the existence of coefficient fields and solutions or supersolutions.

## Coarse ellipticity

These three challenges state Theorem C of the manuscript in its original
hypothesis. That hypothesis bounds the coarse ellipticity constants,
discounted spatial moments of two coarse-grained matrices computed on the
simplices of the triadic triangulations $`\mathscr T_k`$ of $`\square_0`$.

**How the definitions are given.** The triangulation $`\mathscr T_k`$ splits
each of the $`3^{kd}`$ triadic subcubes of $`\square_0`$ of side $`3^{-k}`$ into $`d!`$
open Kuhn simplices
$`\{z+3^{-k}y: y\in(-\tfrac12,\tfrac12)^d,\ y_{\pi(1)}\lt\dots\lt y_{\pi(d)}\}`$,
one for each permutation $`\pi`$. This gives $`d!\,3^{kd}`$ simplices. For a simplex
$`\triangle`$ and $`e\in\mathbb R^d`$, the challenge defines the two directional
quantities as suprema over weighted solutions $`w`$ on $`\triangle`$:

```math
\mathbf a(\triangle,e)=\sup_{w}\frac1{\lvert\triangle\rvert}\int_\triangle\bigl(-\nabla w\cdot\mathbf a\nabla w+2e\cdot\mathbf a\nabla w\bigr),
\qquad
\mathbf a_{\ast}^{-1}(\triangle,e)=\sup_{w}\frac1{\lvert\triangle\rvert}\int_\triangle\bigl(-\nabla w\cdot\mathbf a\nabla w+2e\cdot\nabla w\bigr).
```

These are (2.6) with $`\mathcal C_{\mathrm{sol}}`$, and (1.5). By Proposition 2.2,
the first is also the minimum (1.4) of the energy with affine boundary values.
The matrices are then written out explicitly by polarization:
$`\mathbf a(\triangle)_{ij}=\tfrac14\bigl(\mathbf a(\triangle,e_i+e_j)-\mathbf a(\triangle,e_i-e_j)\bigr)`$,
and likewise for $`\mathbf a_{\ast}^{-1}(\triangle)`$. The challenges call them the
upper and lower responses (`upperResponse`, `lowerResponseInv`). The
coarse ellipticity constants are the manuscript's (3.12) and (3.13),

```math
\Lambda_{s,1,p}=\Bigl((1-3^{-s})\sum_{k\ge0}3^{-ks}\Bigl(\frac1{\lvert\mathscr T_k\rvert}\sum_{\triangle\in\mathscr T_k}\lvert\mathbf a(\triangle)\rvert^p\Bigr)^{\frac1{2p}}\Bigr)^2,
\qquad
\lambda_{t,1,q}=\Bigl((1-3^{-t})\sum_{k\ge0}3^{-kt}\Bigl(\frac1{\lvert\mathscr T_k\rvert}\sum_{\triangle\in\mathscr T_k}\lvert\mathbf a_{\ast}^{-1}(\triangle)\rvert^q\Bigr)^{\frac1{2q}}\Bigr)^{-2},
```

and the coarse ellipticity ratio is $`\Theta=\Lambda_{s,1,p}/\lambda_{t,1,q}`$,
as in (1.6). The challenges call it the contrast.

### `Harnack`

[Challenge](CoarseDeGiorgiAudit/Challenge/Harnack.lean) ·
[configuration](comparators/Harnack.json) · theorem
`CoarseDeGiorgiAudit.Harnack.harnack` · manuscript: Theorem C, (1.11).

Let $`d\ge3`$, $`1\lt p,q`$ and $`s,t\gt0`$, with
$`\theta=1-s-t-\frac{d-1}2\bigl(\frac1p+\frac1q\bigr)\gt0`$. Then there is
$`C\ge0`$, depending on $`d,p,q,s,t`$, with the following property. Let
$`\mathbf a`$ satisfy the standing assumption on $`\square_0`$, with
$`\Lambda_{s,1,p}\lt\infty`$ and $`\lambda_{t,1,q}\gt0`$. Then every nonnegative
weighted solution $`u`$ on $`\square_0`$ satisfies

```math
\mathrm{ess\,sup}_{\frac12\square_0}u\le\exp\bigl(C\sqrt\Theta\bigr)\mathrm{ess\,inf}_{\frac12\square_0}u .
```

### `WeakHarnack`

[Challenge](CoarseDeGiorgiAudit/Challenge/WeakHarnack.lean) ·
[configuration](comparators/WeakHarnack.json) · theorem
`CoarseDeGiorgiAudit.WeakHarnack.weakHarnack` · manuscript: Theorem C, (1.10).

Take the same parameters and hypotheses on $`\mathbf a`$, and write
$`r=\frac{2q}{q+1}`$ and $`r^*=\frac{dr}{d-(1-t)r}`$, as in (1.7) and (3.22), so
that $`\frac{r^*}2=\frac d{d-2+2t+d/q}`$. For every $`0\lt\eta\le r^*/2`$ there is
$`C\ge0`$, depending on $`\eta,d,p,q,s,t`$, such that every nonnegative weighted
supersolution $`u`$ on $`\square_0`$ satisfies

```math
\Bigl(\frac1{\lvert\tfrac58\square_0\rvert}\int_{\frac58\square_0}u^{\eta}\Bigr)^{1/\eta}\le\exp\bigl(C\sqrt\Theta\bigr)\mathrm{ess\,inf}_{\frac12\square_0}u .
```

This is (1.10) in the whole range of Theorem C, the endpoint $`\eta=r^*/2`$
included. The challenge writes out $`r`$ and $`r^*`$ (`paramR`, `rStar`) and
chooses the constant after the exponent, so that it may depend on $`\eta`$, as in
the manuscript. The solution applies `CoarseDeGiorgi.weak_harnack_range`.

### `ResponseQuadraticForms`

[Challenge](CoarseDeGiorgiAudit/Challenge/ResponseQuadraticForms.lean) ·
[configuration](comparators/ResponseQuadraticForms.json) · theorem
`CoarseDeGiorgiAudit.ResponseQuadraticForms.responseQuadraticForms` ·
manuscript: Propositions 2.2 and 2.3.

Let $`\mathbf a`$ satisfy the standing assumption on $`\square_0`$, in any
dimension $`d`$. Then for every $`k\ge0`$ and every simplex $`\triangle\in\mathscr T_k`$,
the matrices $`\mathbf a(\triangle)`$ and $`\mathbf a_{\ast}^{-1}(\triangle)`$ defined
by polarization are positive definite, and for every $`e\in\mathbb R^d`$

```math
e\cdot\mathbf a(\triangle)e=\mathbf a(\triangle,e),\qquad e\cdot\mathbf a_{\ast}^{-1}(\triangle)e=\mathbf a_{\ast}^{-1}(\triangle,e).
```

Here is why this comparator is needed. The polarization formula uses the
directional quantities as real numbers: Lean computes each supremum in
$`[-\infty,\infty]`$ and would read an infinite value as $`0`$. The formula
recovers the manuscript's matrices only if each directional quantity is a
finite quadratic form in $`e`$. This theorem proves exactly that, for the
matrices used in `Harnack` and `WeakHarnack`. So the constants in those two
statements are the manuscript's $`\Lambda_{s,1,p}`$ and $`\lambda_{t,1,q}`$.

## Coefficient moments $`L^p`$/$`L^q`$

These challenges contain no coarse-grained matrices. Their hypothesis is
ordinary integrability of $`\mathbf a`$ and $`\mathbf a^{-1}`$ in the range of
Bella and Schäffner, stated for symmetric coefficients:

```math
d\ge3,\qquad 1\lt p,q,\qquad \frac1p+\frac1q\lt\frac2{d-1},
```

together with $`\lvert\mathbf a\rvert\in L^p(\square_0)`$ and
$`\lvert\mathbf a^{-1}\rvert\in L^q(\square_0)`$ (operator norms), and the
standing assumption. Write
$`M=\lVert\lvert\mathbf a\rvert\rVert_{L^p(\square_0)}\,\lVert\lvert\mathbf a^{-1}\rvert\rVert_{L^q(\square_0)}`$.
Part (i) of Theorem D gives $`\Theta\le M`$ for all $`s,t\gt0`$, and in this range
there are $`s,t\gt0`$ with $`\theta\gt0`$ (the discussion after Theorem D). The
statements below are Theorems A and C and Corollary B for such $`s,t`$, with
$`\Theta`$ replaced by $`M`$; for the weak Harnack inequality, $`t`$ is chosen
depending on the exponent.

**How the definitions are given.** The challenges contain only the common
definitions (cubes, $`H^1_{\mathbf a}`$ and the solution classes). The
integrability hypotheses use Mathlib's `eLpNorm` of the pointwise operator
norms.

### `HarnackLpLq`

[Challenge](CoarseDeGiorgiAudit/Challenge/HarnackLpLq.lean) ·
[configuration](comparators/HarnackLpLq.json) · theorem
`CoarseDeGiorgiAudit.HarnackLpLq.harnackLpLq` · manuscript: Theorem D (i)
with (1.11).

There is $`C\ge0`$, depending on $`d,p,q`$, such that every nonnegative weighted
solution $`u`$ on $`\square_0`$ satisfies

```math
\mathrm{ess\,sup}_{\frac12\square_0}u\le\exp\bigl(C\sqrt M\bigr)\mathrm{ess\,inf}_{\frac12\square_0}u .
```

### `WeakHarnackLpLq`

[Challenge](CoarseDeGiorgiAudit/Challenge/WeakHarnackLpLq.lean) ·
[configuration](comparators/WeakHarnackLpLq.json) · theorem
`CoarseDeGiorgiAudit.WeakHarnackLpLq.weakHarnackLpLq` · manuscript:
Theorem D (i) with (1.10).

For every $`0\lt\eta\lt\frac{dq}{dq+d-2q}`$ there is $`C\ge0`$, depending on
$`\eta,d,p,q`$, such that every nonnegative weighted supersolution $`u`$ on
$`\square_0`$ satisfies

```math
\Bigl(\frac1{\lvert\tfrac58\square_0\rvert}\int_{\frac58\square_0}u^{\eta}\Bigr)^{1/\eta}\le\exp\bigl(C\sqrt M\bigr)\mathrm{ess\,inf}_{\frac12\square_0}u .
```

The bound $`\frac{dq}{dq+d-2q}`$ is the value at $`t=0`$ of
$`\frac{r^*}2=\frac{dq}{dq+d-2q+2qt}`$. Theorem C needs $`t\gt0`$, but part (i) of
Theorem D holds for every $`t\gt0`$, so for each $`\eta`$ in this range there are
$`s,t\gt0`$ with $`\theta\gt0`$ and $`\eta\le r^*/2`$; the solution takes
$`s=\theta_0/4`$ and $`t`$ small, depending on $`\eta`$, where
$`\theta_0=1-\frac{d-1}2(\frac1p+\frac1q)`$. This is the range of Bella and
Schäffner, as the manuscript notes after Theorem C. The bound itself is not
included.

### `LocalBoundednessLpLq`

[Challenge](CoarseDeGiorgiAudit/Challenge/LocalBoundednessLpLq.lean) ·
[configuration](comparators/LocalBoundednessLpLq.json) · theorem
`CoarseDeGiorgiAudit.LocalBoundednessLpLq.localBoundednessLpLq` · manuscript:
Theorem D (i) with Theorem A (1.8) and Corollary B (1.9).

Let $`\theta_0=1-\frac{d-1}2\bigl(\frac1p+\frac1q\bigr)\gt0`$ and
$`\kappa\gt\frac{d-1}{4\theta_0}`$. Then there is $`\gamma\gt0`$, depending on
$`d,p,q,\kappa`$, with the following properties.

1. There is $`C\ge0`$, depending on $`d,p,q,\kappa`$, such that every weighted
   subsolution $`u`$ on $`\square_0`$ is essentially bounded above on every
   compact subset of $`\square_0`$, and for $`\tfrac12\le\rho\lt R\le1`$

   $`\displaystyle \lVert u_+\rVert_{L^\infty(\rho\square_0)}\le C(R-\rho)^{-\gamma}(1+M)^{\kappa}\lVert u_+\rVert_{L^2(R\square_0)},`$

   where the right side is finite when $`R\lt1`$.
2. For every $`0\lt\eta\lt2`$ there is $`C_\eta\ge0`$, depending on
   $`d,p,q,\kappa,\eta`$, such that, with the same $`\gamma`$,

   $`\displaystyle \lVert u_+\rVert_{L^\infty(\rho\square_0)}\le C_\eta(R-\rho)^{-2\gamma/\eta}(1+M)^{2\kappa/\eta}\lVert u_+\rVert_{L^\eta(R\square_0)},`$

   where the right side is finite when $`R\lt1`$.

Theorem A gives the power $`\frac{d-1}{4\theta}`$ of $`\Theta`$, where $`\theta`$ is
the slack (1.7). Take $`\theta=\frac{d-1}{4\kappa}\lt\theta_0`$ and
$`s=t=\frac{\theta_0-\theta}2`$. Then the power is $`\kappa`$, and
$`\Theta^\kappa\le(1+M)^\kappa`$. The inequality on $`\kappa`$ is strict because
Theorem A requires $`s,t\gt0`$.

## Uniformly elliptic coefficients

These three challenges specialize the previous results to bounded, uniformly
positive coefficients. The ellipticity constants are written as $`\lambda`$ and
$`\Lambda`$; the code writes `lam`, because `λ` is a Lean keyword.

**How the definitions are given.** `UniformlyElliptic lam Λ a` says that for
almost every $`x\in\square_0`$ the matrix $`\mathbf a(x)`$ is symmetric and
$`\lambda\lvert\xi\rvert^2\le\xi\cdot\mathbf a(x)\xi\le\Lambda\lvert\xi\rvert^2`$
for all $`\xi`$. Together with almost-everywhere strong measurability, this is
the whole coefficient hypothesis. The solution classes are the common
weighted classes. For such coefficients, the norm of $`H^1_{\mathbf a}(\square_0)`$
is equivalent to the $`H^1(\square_0)`$ norm, and the space is the ordinary
Sobolev space $`H^1(\square_0)`$, with $`G=\nabla u`$. This identification is
standard mathematics (Poincaré's inequality and the Meyers–Serrin theorem); it
is not part of the challenges.

### `HarnackUniform`

[Challenge](CoarseDeGiorgiAudit/Challenge/HarnackUniform.lean) ·
[configuration](comparators/HarnackUniform.json) · theorem
`CoarseDeGiorgiAudit.HarnackUniform.harnackUniform` · manuscript: Theorem D
(i) with (1.11), $`p=q=d`$.

Let $`d\ge3`$. There is $`C\ge0`$, depending only on $`d`$, with the following
property. Let $`0\lt\lambda\le\Lambda`$, and let $`\mathbf a`$ be measurable and
uniformly elliptic on $`\square_0`$ with these constants. Then every
nonnegative weighted solution $`u`$ on $`\square_0`$ satisfies

```math
\mathrm{ess\,sup}_{\frac12\square_0}u\le\exp\Bigl(C\sqrt{\Lambda/\lambda}\Bigr)\mathrm{ess\,inf}_{\frac12\square_0}u .
```

The exponents $`p=q=d`$ lie in the range $`\frac1p+\frac1q\lt\frac2{d-1}`$. On the
unit cube,
$`\lVert\lvert\mathbf a\rvert\rVert_{L^d}\lVert\lvert\mathbf a^{-1}\rvert\rVert_{L^d}\le\Lambda/\lambda`$.

### `WeakHarnackUniform`

[Challenge](CoarseDeGiorgiAudit/Challenge/WeakHarnackUniform.lean) ·
[configuration](comparators/WeakHarnackUniform.json) · theorem
`CoarseDeGiorgiAudit.WeakHarnackUniform.weakHarnackUniform` · manuscript:
Theorem D (i) with (1.10) and the discussion after Theorem C.

Let $`d\ge3`$ and $`0\lt\eta\lt\frac d{d-2}`$. There is $`C\ge0`$, depending only on
$`\eta`$ and $`d`$, with the following property. Let $`0\lt\lambda\le\Lambda`$, and let
$`\mathbf a`$ be measurable and uniformly elliptic on $`\square_0`$ with these
constants. Then every nonnegative weighted supersolution $`u`$ on $`\square_0`$
satisfies

```math
\Bigl(\frac1{\lvert\tfrac58\square_0\rvert}\int_{\frac58\square_0}u^{\eta}\Bigr)^{1/\eta}\le\exp\Bigl(C\sqrt{\Lambda/\lambda}\Bigr)\mathrm{ess\,inf}_{\frac12\square_0}u .
```

This is `WeakHarnackLpLq` with $`p=q=Q`$, where $`Q\ge d`$ is chosen, depending on
$`\eta`$, so large that $`\eta\lt\frac{dQ}{dQ+d-2Q}`$, and $`M\le\Lambda/\lambda`$ as for
`HarnackUniform`. As $`Q\to\infty`$ the bound $`\frac{dQ}{dQ+d-2Q}`$ increases to
$`\frac d{d-2}`$, so the range is the union of the ranges of Theorem C over the
admissible exponents, as the manuscript notes after Theorem C. The bound
$`\frac d{d-2}`$ is not included; the manuscript notes that the range is sharp
because of the fundamental solution $`\lvert x\rvert^{2-d}`$.

### `LocalBoundednessUniform`

[Challenge](CoarseDeGiorgiAudit/Challenge/LocalBoundednessUniform.lean) ·
[configuration](comparators/LocalBoundednessUniform.json) · theorem
`CoarseDeGiorgiAudit.LocalBoundednessUniform.localBoundednessUniform` ·
manuscript: Theorem A (1.8) with Theorem D (i).

Let $`d\ge3`$ and $`\kappa\gt\frac{d-1}4`$. There are $`\gamma\gt0`$ and $`C\ge0`$,
depending on $`d`$ and $`\kappa`$, with the following property. Let
$`0\lt\lambda\le\Lambda`$, and let $`\mathbf a`$ be measurable and uniformly
elliptic on $`\square_0`$ with these constants. Then every weighted subsolution
$`u`$ on $`\square_0`$ is essentially bounded above on every compact subset of
$`\square_0`$, and for $`\tfrac12\le\rho\lt R\le1`$

```math
\lVert u_+\rVert_{L^\infty(\rho\square_0)}\le C(R-\rho)^{-\gamma}\bigl(1+\Lambda/\lambda\bigr)^{\kappa}\lVert u_+\rVert_{L^2(R\square_0)},
```

where the right side is finite when $`R\lt1`$. The proof applies Theorem A with
$`\theta=\frac{d-1}{4\kappa}\in(0,1)`$, $`s=t=\frac{1-\theta}4`$ and
$`p=q=\frac{2(d-1)}{1-\theta}`$. Part (i) of Theorem D then bounds $`\Theta`$ by
$`\Lambda/\lambda`$.

## Negative regularity of the coefficients

Part (ii) of Theorem D replaces the integrability of $`\mathbf a`$ and
$`\mathbf a^{-1}`$ by bounds on their averages over the triadic subcubes of
$`\square_0`$, which may grow with the scale. Theorem F shows that its range of
parameters cannot be enlarged, even at its boundary, in any dimension
$`d\ge3`$.

**How the definitions are given.** The challenges write out the cube
quasi-norm (1.12) of a matrix field $`\mathbf b`$, as `cubeQuasiNorm`:

```math
\lVert\mathbf b\rVert_{\mathring{\underline B}^{-2s}_{p,1/2}(\square_0)}=\Bigl(\sum_{k\ge0}3^{-ks}\Bigl(\frac1{3^{kd}}\sum_{z\in3^{-k}\mathbb Z^d\cap\square_0}\lvert(\mathbf b)_{z+\square_{-k}}\rvert^p\Bigr)^{\frac1{2p}}\Bigr)^2\in[0,\infty],
```

where the cubes $`z+\square_{-k}`$ of side $`3^{-k}`$ tile $`\square_0`$,
$`(\mathbf b)_Q`$ is the entrywise average of $`\mathbf b`$ over $`Q`$ and
$`\lvert\cdot\rvert`$ is the operator norm. The manuscript notes that, for
positive semidefinite fields, it is comparable to a Besov quasi-norm of order
$`-2s`$ and fine index $`\frac12`$ of the extension by zero.

For the three estimates, the parameters are $`d\ge3`$, $`1\lt p,q`$ and $`s,t\gt0`$
with

```math
\theta=1-s-t-\frac{d-1}2\Bigl(\frac1p+\frac1q\Bigr)\gt0,
```

as in (1.16), for the indices of the quasi-norms themselves. Besides the
standing assumption, each of them assumes that
$`\lVert\mathbf a\rVert_{\mathring{\underline B}^{-2s}_{p,1/2}}\lt\infty`$ and
$`\lVert\mathbf a^{-1}\rVert_{\mathring{\underline B}^{-2t}_{q,1/2}}\lt\infty`$. Write
$`N`$ for the product of the two quasi-norms. Part (ii) of Theorem D gives
$`\Lambda_{s,1,p}\le d!\,(1-3^{-s})^2\lVert\mathbf a\rVert_{\mathring{\underline B}^{-2s}_{p,1/2}}`$,
$`\lambda_{t,1,q}^{-1}\le d!\,(1-3^{-t})^2\lVert\mathbf a^{-1}\rVert_{\mathring{\underline B}^{-2t}_{q,1/2}}`$
and $`\Theta\le(d!)^2N`$, so Theorems A and C and Corollary B hold with these
$`s,t`$ and with $`\Theta`$ replaced by $`N`$.

The quasi-norm is defined for every matrix field, and Lean's integral of a
non-integrable function is $`0`$. In these three estimates the quasi-norms are
hypotheses, and the standing assumption makes them the genuine quasi-norms: a
symmetric positive definite matrix satisfies
$`\lvert a_{ij}\rvert\le\mathrm{tr}\mathbf a`$, so the entries of $`\mathbf a`$ and
of $`\mathbf a^{-1}`$ are integrable on $`\square_0`$ and the cube averages are
true averages. The same holds in `Sharpness` below, where the quasi-norms are
conclusions.

### `HarnackBesov`

[Challenge](CoarseDeGiorgiAudit/Challenge/HarnackBesov.lean) ·
[configuration](comparators/HarnackBesov.json) · theorem
`CoarseDeGiorgiAudit.HarnackBesov.harnackBesov` · manuscript: Theorem D (ii)
with (1.11).

There is $`C\ge0`$, depending on $`d,p,q,s,t`$, such that every nonnegative
weighted solution $`u`$ on $`\square_0`$ satisfies

```math
\mathrm{ess\,sup}_{\frac12\square_0}u\le\exp\bigl(C\sqrt N\bigr)\mathrm{ess\,inf}_{\frac12\square_0}u .
```

### `WeakHarnackBesov`

[Challenge](CoarseDeGiorgiAudit/Challenge/WeakHarnackBesov.lean) ·
[configuration](comparators/WeakHarnackBesov.json) · theorem
`CoarseDeGiorgiAudit.WeakHarnackBesov.weakHarnackBesov` · manuscript:
Theorem D (ii) with (1.10).

Write $`r=\frac{2q}{q+1}`$ and $`r^*=\frac{dr}{d-(1-t)r}`$, as in `WeakHarnack`, where
$`-2t`$ is the order of the quasi-norm of $`\mathbf a^{-1}`$. For every
$`0\lt\eta\le r^*/2`$ there is $`C\ge0`$, depending on $`\eta,d,p,q,s,t`$, such that
every nonnegative weighted supersolution $`u`$ on $`\square_0`$ satisfies

```math
\Bigl(\frac1{\lvert\tfrac58\square_0\rvert}\int_{\frac58\square_0}u^{\eta}\Bigr)^{1/\eta}\le\exp\bigl(C\sqrt N\bigr)\mathrm{ess\,inf}_{\frac12\square_0}u .
```

As in `WeakHarnack`, the endpoint $`\eta=r^*/2`$ is included.

### `LocalBoundednessBesov`

[Challenge](CoarseDeGiorgiAudit/Challenge/LocalBoundednessBesov.lean) ·
[configuration](comparators/LocalBoundednessBesov.json) · theorem
`CoarseDeGiorgiAudit.LocalBoundednessBesov.localBoundednessBesov` ·
manuscript: Theorem D (ii) with Theorem A (1.8) and Corollary B (1.9).

There is $`\gamma\gt0`$, depending on $`d,p,q,s,t`$, with the following
properties.

1. There is $`C\ge0`$, depending on $`d,p,q,s,t`$, such that every weighted
   subsolution $`u`$ on $`\square_0`$ is essentially bounded above on every
   compact subset of $`\square_0`$, and for $`\tfrac12\le\rho\lt R\le1`$

   $`\displaystyle \lVert u_+\rVert_{L^\infty(\rho\square_0)}\le C(R-\rho)^{-\gamma}N^{\frac{d-1}{4\theta}}\lVert u_+\rVert_{L^2(R\square_0)},`$

   where the right side is finite when $`R\lt1`$.
2. For every $`0\lt\eta\lt2`$ there is $`C_\eta\ge0`$, depending on
   $`d,p,q,s,t,\eta`$, such that, with the same $`\gamma`$,

   $`\displaystyle \lVert u_+\rVert_{L^\infty(\rho\square_0)}\le C_\eta(R-\rho)^{-2\gamma/\eta}N^{\frac{d-1}{2\eta\theta}}\lVert u_+\rVert_{L^\eta(R\square_0)},`$

   where the right side is finite when $`R\lt1`$.

A note on comparing this with `LocalBoundednessLpLq`. There the hypothesis
does not involve $`s`$ and $`t`$, so any $`s,t\gt0`$ may be used, and the slack
$`\theta`$ can approach, but not reach,
$`\theta_0=1-\frac{d-1}2(\frac1p+\frac1q)`$; this is why every power
$`\kappa\gt\frac{d-1}{4\theta_0}`$ is allowed there. Here the hypothesis fixes
$`s`$ and $`t`$, and the powers are those of Theorem A and Corollary B for these
indices.

### `Sharpness`

[Challenge](CoarseDeGiorgiAudit/Challenge/Sharpness.lean) ·
[configuration](comparators/Sharpness.json) · theorem
`CoarseDeGiorgiAudit.Sharpness.sharpness` · manuscript: Theorem F, (1.20).

This challenge goes in the other direction. Its parameters lie outside the
range (1.16), and it asserts that there local boundedness and the Harnack
inequality can fail, already for scalar coefficients. It is stated with the
orders $`\alpha,\beta\ge0`$ of negative regularity and the integrabilities
$`1\lt\xi,\zeta`$, which Theorem F of the manuscript calls $`p`$ and $`q`$ (the
library statement `CoarseDeGiorgi.sharpness` also writes $`\xi`$, $`\zeta`$); the
quasi-norm of order $`-\alpha`$ and integrability $`\xi`$ is (1.12) with
$`s=\alpha/2`$ and $`p=\xi`$. Let $`d\ge3`$, and suppose that

```math
\theta_0=1-\frac{\alpha+\beta}2-\frac{d-1}2\Bigl(\frac1\xi+\frac1\zeta\Bigr)\le0 .
```

Then there is a measurable function $`a`$ on $`\mathbb R^d`$ with $`a(x)\gt0`$ at
every point and $`a(x)=a(x')`$ whenever $`x`$ and $`x'`$ differ only in the first
coordinate, so that $`a`$ depends only on the transverse variable $`y`$ in
$`x=(x_1,y)`$, with the following properties. The scalar field
$`\mathbf a=aI`$ satisfies the standing assumption on $`\square_0`$; if
$`\alpha\gt0`$, its quasi-norm of order $`-\alpha`$ and integrability $`\xi`$ is
finite, and if $`\alpha=0`$, $`\lVert\lvert\mathbf a\rvert\rVert_{L^\xi(\square_0)}\lt\infty`$;
likewise for $`\mathbf a^{-1}`$ with $`\beta`$ and $`\zeta`$. There is a weighted
solution $`u`$ on $`\square_0`$, with some gradient $`G`$, such that $`u\ge1`$
almost everywhere in $`\square_0`$,

```math
\mathrm{ess\,sup}_{\frac12\square_0}u=\infty,\qquad 0\lt\mathrm{ess\,inf}_{\frac12\square_0}u\lt\infty ,
```

and, for every point $`x=(x_1,0)`$ with $`\lvert x_1\rvert\lt\frac12`$ and every
neighborhood $`N`$ of $`x`$, the essential supremum of $`\lvert u\rvert`$ on
$`N\cap\square_0`$ is infinite.

Since a solution is a subsolution, and $`u`$ is not essentially bounded above
on the compact set $`\overline{\tfrac12\square_0}\subset\square_0`$, the
conclusions of `LocalBoundednessBesov` and `HarnackBesov` fail for these
parameters. No case is excluded: the hypothesis is the whole complement of
(1.16), including the boundary $`\theta_0=0`$ in dimension three. For
$`\alpha=\beta=0`$ the conclusions are finite $`L^\xi`$ and $`L^\zeta`$ norms, so this
is also the sharpness of the range $`\frac1p+\frac1q\lt\frac2{d-1}`$ of the `LpLq`
challenges, endpoint included. The examples that the solution formalizes are
those of the manuscript's Section 11.2: the field is the identity outside
disjoint thin cylinders parallel to the $`x_1`$-axis whose axes accumulate on
the line $`\{y=0\}`$, each with a conducting core and an insulating annulus;
each cylinder carries an explicit nonnegative subsolution, and the harmonic
replacement of their sum, plus one, is the solution $`u`$. The formal proof
uses a different explicit subsolution in each cylinder than the manuscript;
[`CORRESPONDENCE.md`](CORRESPONDENCE.md) describes both.

**How the definitions are given.** The challenge writes out cubes, the
standing assumption, $`H^1_{\mathbf a}`$ and weighted solutions, and the
quasi-norm (1.12) as in the three estimates above. The field is
`fun x => a x • 1`, and its inverse is written `(a x • 1)⁻¹`, Mathlib's matrix
inverse. The supremum is written as
`eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) = ⊤`, the essential
supremum of $`\lvert u\rvert`$, which is that of $`u`$ because $`u\ge1`$, and the
unboundedness near a point $`x`$ as
`eLpNorm u ⊤ (volume.restrict (N ∩ originCube 1)) = ⊤` for every `N ∈ 𝓝 x`.
The infimum is the essential infimum of $`\max\{u,0\}`$, valued in
$`[0,\infty]`$. The Lebesgue norms at a zero order are `eLpNorm` of the pointwise
operator norms of the field and of its inverse.

## Negative Sobolev norms of the coefficients

Part (iii) of Theorem D bounds the coarse ellipticity constants by
negative Sobolev norms of $`\mathbf a`$ and $`\mathbf a^{-1}`$, and Corollary E
combines it with Theorems A and C. These two challenges state Corollary E.

**How the definitions are given.** The challenges write out the Sobolev norms
of every order $`s\ge0`$ on an open set $`U`$ and the dual norm (1.22).

- **Weak derivatives.** `IsWeakDerivArray U j w D` says that $`D`$ is the array
  $`\nabla^jw`$ of the weak partial derivatives of order $`j`$ of $`w`$ on $`U`$:
  one entry $`D_\iota`$ for each of the $`d^j`$ ordered index tuples
  $`\iota=(\iota_0,\dots,\iota_{j-1})`$, with $`w`$ and every entry locally integrable
  on $`U`$, and
  $`\int_Uw\,\partial^\iota\varphi=(-1)^j\int_UD_\iota\,\varphi`$
  for every smooth $`\varphi`$ with compact support in $`U`$. Here
  $`\partial^\iota\varphi(x)`$ is the iterated derivative `iteratedFDeriv ℝ j φ x`
  applied to the coordinate vectors $`e_{\iota_0},\dots,e_{\iota_{j-1}}`$. For $`j=0`$
  the array has one entry, equal to $`w`$ almost everywhere.
- **The fractional seminorm.** For an array $`F=(F_i)_i`$ of functions,
  `arrayFracSeminorm V σ r F` is (1.21) with the Euclidean norm of the array
  difference and the Euclidean distance (Mathlib's distance on `Fin d → ℝ` is
  the sup distance and is not used),

  $`\displaystyle [F]_{W^{\sigma,r}(V)}=\Bigl(\int_V\int_V\frac{\lvert F(x)-F(y)\rvert^r}{\lvert x-y\rvert^{d+\sigma r}}\,dx\,dy\Bigr)^{1/r},`$

  where the double integral is the lower integral for the product measure on
  $`V\times V`$, equal to the iterated integral by Tonelli's theorem.
- **The Sobolev norm.** Write $`s=m+\sigma`$ with $`m=\lfloor s\rfloor`$ and
  $`0\le\sigma\lt1`$. `sobolevNorm U s ξ w` is

  $`\displaystyle \lVert w\rVert_{W^{s,\xi}(U)}=\Bigl(\sum_{j=0}^m\lVert\nabla^jw\rVert_{L^\xi(U)}^\xi+[\nabla^mw]_{W^{\sigma,\xi}(U)}^\xi\Bigr)^{1/\xi},`$

  with the seminorm omitted when $`\sigma=0`$, so that integer orders are
  included and the order zero is the $`L^\xi`$ norm. Here
  $`\lVert\nabla^jw\rVert_{L^\xi(U)}`$ is the $`L^\xi`$ norm of the pointwise Euclidean
  norm of the array. The challenge takes the infimum of this expression over
  all families of weak derivative arrays of $`w`$ up to order $`m`$. On an open set
  (here always the cube $`\square_0`$) weak derivatives are unique almost
  everywhere, so the infimum is the value at $`\nabla^0w,\dots,\nabla^mw`$; it is
  $`\infty`$ when $`w`$ has no weak derivatives up to order $`m`$.
- **The negative Sobolev norm.** For $`1\lt p\lt\infty`$ and $`p'=\frac p{p-1}`$,
  `negSobolevNorm U b s p` is the dual norm (1.22) tested on bounded
  functions,

  $`\displaystyle \lVert\mathbf b\rVert_{W^{-s,p}(U)}=\sup\Bigl\{\Bigl\lvert\int_Ug\,\mathbf b\Bigr\rvert\ :\ g\in L^\infty(U),\ \lVert g\rVert_{W^{s,p'}(U)}\le1\Bigr\}\in[0,\infty],`$

  where $`\int_Ug\,\mathbf b`$ is the matrix of the integrals $`\int_Ug\,b_{ij}`$ and
  $`\lvert\cdot\rvert`$ is the operator norm. The bounded functions are those
  with `MemLp g ⊤`.

For the two estimates, the parameters are $`d\ge3`$, $`1\lt p,q`$ and
$`\alpha,\beta\ge0`$ with

```math
\theta=1-\frac{\alpha+\beta}2-\frac{d-1}2\Bigl(\frac1p+\frac1q\Bigr)\gt0 .
```

Besides the standing assumption, each of them assumes that
$`\lvert\mathbf a\rvert`$ and $`\lvert\mathbf a^{-1}\rvert`$ are integrable on
$`\square_0`$ (the manuscript's $`\mathbf a\in W^{-\alpha,p}\cap L^1`$; these
hypotheses also follow from the standing assumption, so they do not restrict
the challenges) and that
$`\lVert\mathbf a\rVert_{W^{-\alpha,p}(\square_0)}\lt\infty`$ and
$`\lVert\mathbf a^{-1}\rVert_{W^{-\beta,q}(\square_0)}\lt\infty`$. Write
$`N=\lVert\mathbf a\rVert_{W^{-\alpha,p}(\square_0)}\lVert\mathbf a^{-1}\rVert_{W^{-\beta,q}(\square_0)}`$.
The entries of $`\mathbf a`$ and $`\mathbf a^{-1}`$ are integrable on $`\square_0`$, so
the integrals $`\int g\,a_{ij}`$ are genuine integrals. The constants depend
only on $`d,p,q,\alpha,\beta`$, and the two challenges choose them
independently; the larger of the two constants serves both. The proofs apply
part (iii) of Theorem D with $`s=\frac\alpha2+\frac\theta4`$,
$`t=\frac\beta2+\frac\theta4`$ and $`\varepsilon=\frac\theta2`$, so that the slack of
Theorems A and C is $`\frac\theta2`$ and the power $`\frac{d-1}{4\theta}`$ of
Theorem A becomes $`\frac{d-1}{2\theta}`$.

### `LocalBoundednessSobolev`

[Challenge](CoarseDeGiorgiAudit/Challenge/LocalBoundednessSobolev.lean) ·
[configuration](comparators/LocalBoundednessSobolev.json) · theorem
`CoarseDeGiorgiAudit.LocalBoundednessSobolev.localBoundednessSobolev` ·
manuscript: Corollary E, (1.18).

There are $`C\ge0`$ and $`\gamma\gt0`$, depending on $`d,p,q,\alpha,\beta`$, such that
every weighted subsolution $`u`$ on $`\square_0`$ satisfies, for
$`\tfrac12\le\rho\lt R\le1`$,

```math
\lVert u_+\rVert_{L^\infty(\rho\square_0)}\le C(R-\rho)^{-\gamma}N^{\frac{d-1}{2\theta}}\lVert u_+\rVert_{L^2(R\square_0)},
```

where the right side is finite when $`R\lt1`$.

### `HarnackSobolev`

[Challenge](CoarseDeGiorgiAudit/Challenge/HarnackSobolev.lean) ·
[configuration](comparators/HarnackSobolev.json) · theorem
`CoarseDeGiorgiAudit.HarnackSobolev.harnackSobolev` · manuscript: Corollary E,
(1.19).

There is $`C\ge0`$, depending on $`d,p,q,\alpha,\beta`$, such that every
nonnegative weighted solution $`u`$ on $`\square_0`$ satisfies

```math
\mathrm{ess\,sup}_{\frac12\square_0}u\le\exp\bigl(C\sqrt N\bigr)\mathrm{ess\,inf}_{\frac12\square_0}u .
```

## Optimality of the powers

### `SharpnessPolynomial`

[Challenge](CoarseDeGiorgiAudit/Challenge/SharpnessPolynomial.lean) ·
[configuration](comparators/SharpnessPolynomial.json) · theorem
`CoarseDeGiorgiAudit.SharpnessPolynomial.sharpnessPolynomial` · manuscript:
Proposition 11.2, (11.12)–(11.15).

This challenge shows that the powers of $`\Theta`$ in Theorem A (1.8) and
Corollary B (1.9) cannot be lowered. Let $`d\ge3`$, $`1\lt p,q`$ and $`s,t\gt0`$ with
$`\theta=1-s-t-\frac{d-1}2\bigl(\frac1p+\frac1q\bigr)\gt0`$. Then there are
families $`\mathbf a_\varepsilon`$, $`u_\varepsilon`$ and $`G_\varepsilon`$, indexed
by $`\varepsilon\in\mathbb R`$, such that every $`\mathbf a_\varepsilon`$ satisfies
the standing assumption on $`\square_0`$ and, for $`0\lt\varepsilon\lt\frac18`$:

1. $`\mathbf a_\varepsilon`$ is symmetric and uniformly elliptic almost
   everywhere in $`\square_0`$,
   $`\lambda_\varepsilon\lvert\xi\rvert^2\le\xi\cdot\mathbf a_\varepsilon\xi\le\Lambda_\varepsilon\lvert\xi\rvert^2`$
   with $`\lambda_\varepsilon\gt0`$, the constants depending on $`\varepsilon`$;
2. $`u_\varepsilon`$ is a weighted solution with gradient $`G_\varepsilon`$, and
   its positive part $`(u_\varepsilon)_+`$ is a weighted subsolution, with some
   gradient;
3. $`\int_{\square_0}\bigl(\mathrm{tr}\mathbf a_\varepsilon+\mathrm{tr}\mathbf a_\varepsilon^{-1}\bigr)\le C`$,
   with $`C`$ independent of $`\varepsilon`$ (11.12);
4. with one constant $`C\ge1`$ independent of $`\varepsilon`$ (11.13),

   $`\displaystyle C^{-1}\varepsilon^{-2\theta}\le\Lambda_{s,1,p}\le C\varepsilon^{-2\theta},\qquad C^{-1}\le\lambda_{t,1,q}\le C,\qquad C^{-1}\varepsilon^{-2\theta}\le\Theta\le C\varepsilon^{-2\theta},`$

   the constants and the ratio being those of $`\mathbf a_\varepsilon`$;
5. $`\lVert(u_\varepsilon)_+\rVert_{L^\infty(\rho\square_0)}=1+\rho^2/4`$ for
   $`\tfrac12\le\rho\lt1`$, and, for every $`\eta\gt0`$, with $`C_\eta\ge1`$ independent
   of $`\varepsilon`$ and $`R`$,
   $`C_\eta^{-1}\varepsilon^{(d-1)/\eta}\le\lVert(u_\varepsilon)_+\rVert_{L^\eta(R\square_0)}\le C_\eta\varepsilon^{(d-1)/\eta}`$
   for $`\tfrac12\lt R\le1`$ (11.14).

Consequently (11.15), for $`\tfrac12\le\rho\lt R\le1`$, $`0\lt\eta\le2`$ and every
real $`\upsilon\lt\frac{d-1}{2\eta\theta}`$,

```math
\frac{\lVert(u_\varepsilon)_+\rVert_{L^\infty(\rho\square_0)}}{\Theta^{\upsilon}\,\lVert(u_\varepsilon)_+\rVert_{L^\eta(R\square_0)}}\longrightarrow\infty\qquad\text{as }\varepsilon\to0^+ .
```

By item 4, each $`\mathbf a_\varepsilon`$ satisfies the hypotheses
$`\Lambda_{s,1,p}\lt\infty`$ and $`\lambda_{t,1,q}\gt0`$ of Theorem A with these
$`d,p,q,s,t`$. So an estimate of the form (1.8) with a power of $`\Theta`$
below $`\frac{d-1}{4\theta}`$ (take $`\eta=2`$), or of the form (1.9) with a
power below $`\frac{d-1}{2\eta\theta}`$, is false, even for fixed $`\rho`$ and
$`R`$. The solutions
change sign, and it is their positive parts, which are subsolutions, that
are measured; the manuscript does not claim optimality for nonnegative
solutions, nor for the powers of $`R-\rho`$. The example is the one of
Section 11.3: a single cylinder of radius $`\varepsilon`$ about the
$`x_1`$-axis with a large axial and a small transverse conductivity, and
$`u_\varepsilon=1+x_1^2-\lvert y\rvert^2/\varepsilon^2`$ inside it.

**How the definitions are given.** The challenge writes out the common
definitions, weighted subsolutions and the positive part, and the
triangulations, directional quantities, polarized coarse-grained matrices,
coarse ellipticity constants and ratio exactly as the
[coarse ellipticity](#coarse-ellipticity) challenges do. Here the constants are
conclusions rather than hypotheses; by `ResponseQuadraticForms`, for every
field satisfying the standing assumption (as each $`\mathbf a_\varepsilon`$ does)
the polarized matrices are the manuscript's coarse-grained matrices, so the
constants are the manuscript's $`\Lambda_{s,1,p}`$ and $`\lambda_{t,1,q}`$.
Uniform ellipticity is written with Mathlib's `Matrix.IsHermitian` and the dot
product. Norms are `eLpNorm` (item 5 uses `ENNReal.ofReal η` as the exponent),
the power is `ENNReal.rpow`, and the limit is Mathlib's `Tendsto` along
$`\varepsilon\to0^+`$ (`𝓝[>] 0`) to $`\infty`$ in $`[0,\infty]`$. Items 4 and 5
make every quantity in the ratio finite and positive, so the limit is not
produced by the conventions for $`0`$ and $`\infty`$ in $`[0,\infty]`$.

## Optimality of the weak Harnack exponent

### `SharpnessWeakHarnack`

[Challenge](CoarseDeGiorgiAudit/Challenge/SharpnessWeakHarnack.lean) ·
[configuration](comparators/SharpnessWeakHarnack.json) · theorem
`CoarseDeGiorgiAudit.SharpnessWeakHarnack.sharpnessWeakHarnack` · manuscript:
Proposition 11.3, (11.19).

This challenge shows that the range $`0\lt\eta\le r^*/2`$ of the weak Harnack
inequality (1.10) cannot be enlarged. Let $`d\ge3`$, $`1\lt p,q`$ and $`s,t\gt0`$ with
$`\theta=1-s-t-\frac{d-1}2\bigl(\frac1p+\frac1q\bigr)\gt0`$, and write
$`r=\frac{2q}{q+1}`$ and $`r^*=\frac{dr}{d-(1-t)r}`$, as in (1.7) and (3.22), so
that $`\frac{r^*}2=\frac d{d-2+2t+d/q}`$. Then there is a profile
$`a:\mathbb R\to\mathbb R`$ such that the radial field $`\mathbf a(x)=a(\lvert x\rvert)I`$,
where $`\lvert x\rvert`$ is the Euclidean norm, satisfies the standing assumption on
$`\square_0`$ with $`\Lambda_{s,1,p}\lt\infty`$ and $`\lambda_{t,1,q}\gt0`$, and there are
families $`u_\varepsilon`$ and $`G_\varepsilon`$, indexed by $`\varepsilon\in\mathbb R`$,
with the following properties.

1. For $`0\lt\varepsilon\lt\frac18`$, $`u_\varepsilon\ge0`$ almost everywhere in
   $`\square_0`$, and $`u_\varepsilon`$ is a weighted supersolution on $`\square_0`$
   with gradient $`G_\varepsilon`$.
2. The essential infimum of $`u_\varepsilon`$ on $`\frac12\square_0`$ is the same
   number $`m\gt0`$ for every $`0\lt\varepsilon\lt\frac18`$.
3. For every $`\eta\gt r^*/2`$, (11.19) holds:

   $`\displaystyle \frac1{\mathrm{ess\,inf}_{\frac12\square_0}u_\varepsilon}\Bigl(\frac1{\lvert\tfrac58\square_0\rvert}\int_{\frac58\square_0}u_\varepsilon^{\eta}\Bigr)^{1/\eta}\longrightarrow\infty\qquad\text{as }\varepsilon\to0^+ .`$

The field and the supersolutions are chosen before $`\eta`$, so one example
serves every $`\eta\gt r^*/2`$. Since $`\Theta=\Lambda_{s,1,p}/\lambda_{t,1,q}`$ is finite
for this field, an estimate of the form (1.10) with any finite constant fails
for every $`\eta\gt r^*/2`$. Together with `WeakHarnack`, which states Theorem C for
every $`0\lt\eta\le r^*/2`$, the comparators certify that $`r^*/2`$ is the exact
threshold for each fixed $`d,p,q,s,t`$. The example of the manuscript's
Section 11.4 is the field
$`\lvert x\rvert^\beta\log^3(e\sqrt d/\lvert x\rvert)I`$ with $`\beta=2t+\frac dq`$, and
$`u_\varepsilon`$ is the fundamental solution with pole at the origin, made
constant on the ball $`B(0,\varepsilon)`$. The solution formalizes the same field
with smooth supersolutions whose source lies in
$`\varepsilon\le\lvert x\rvert\le2\varepsilon`$; [`CORRESPONDENCE.md`](CORRESPONDENCE.md)
describes the difference.

**How the definitions are given.** The challenge writes out the common
definitions, weighted supersolutions, the essential infimum and the
normalized moment, and the triangulations, directional quantities, polarized
coarse-grained matrices and coarse ellipticity constants exactly as
the [coarse ellipticity](#coarse-ellipticity) challenges do. It adds $`r`$ and $`r^*`$,
the Euclidean norm $`\lvert x\rvert=\bigl(\sum_ix_i^2\bigr)^{1/2}`$ (with `Real.sqrt`) and
the radial field `fun x => a (euclidNorm x) • 1`. The coarse ellipticity
constants are conclusions here. The standing assumption is part of
the conclusion, so by `ResponseQuadraticForms` the polarized matrices are the
manuscript's coarse-grained matrices, and the constants are the manuscript's
$`\Lambda_{s,1,p}`$ and $`\lambda_{t,1,q}`$. The essential infimum is valued in
$`[0,\infty]`$; the conclusion requires it to be positive, and it is finite
because $`u_\varepsilon`$ is real valued on a set of positive measure. The limit
is Mathlib's `Tendsto` along $`\varepsilon\to0^+`$ (`𝓝[>] 0`) to $`\infty`$ in
$`[0,\infty]`$. Since the infimum is finite and positive, the limit is a
statement about the moments and not a product of the conventions for $`0`$ and
$`\infty`$ in $`[0,\infty]`$; a family whose moments were infinite would itself
violate (1.10).

## Relation to the De Giorgi–Nash–Moser formalization

The repository
[scottnarmstrong/DeGiorgi](https://github.com/scottnarmstrong/DeGiorgi)
(Armstrong and Kempe, [arXiv:2604.05984](https://arxiv.org/abs/2604.05984))
is an earlier formalization of De Giorgi–Nash–Moser theory. Its setting is
uniformly elliptic, bounded measurable coefficients, which may be
nonsymmetric, in dimension $`d\ge3`$. It works on Euclidean balls, normalized
to $`\lambda=1`$, with solutions in $`W^{1,2}`$ of the ball. Its headline
theorems are:

- local boundedness of subsolutions,
  $`\lVert u_+\rVert_{L^\infty(B_{1/2})}\le C(d)\,\Lambda^{d/4}\lVert u_+\rVert_{L^2(B_1)}`$
  (`linfty_subsolution_DeGiorgi_normalized`);
- a weak Harnack inequality for positive supersolutions, with a constant of
  the form $`\exp(C\sqrt\Lambda)`$ (`weak_harnack`, `weak_harnack_on_ball`);
- the Harnack inequality for positive solutions with constant
  $`\exp(C(d)\sqrt\Lambda)`$ (`harnack`);
- Hölder continuity of solutions, with a Hölder exponent at least
  $`\exp(-C\sqrt\Lambda)`$ (`holder_Moser`).

This repository does not depend on that one. Its three uniformly elliptic
comparators are special cases of the results for non-uniformly elliptic
coefficients. In the symmetric case, and on cubes instead of balls, they
compare as follows.

- **Local boundedness is recovered with a smaller power of the ellipticity
  contrast.** `LocalBoundednessUniform` gives the factor
  $`(1+\Lambda/\lambda)^\kappa`$ for every $`\kappa\gt\frac{d-1}4`$. The earlier
  repository proves the power $`\frac d4`$, which is what the standard De Giorgi
  and Moser iterations give. The improvement from $`d`$ to $`d-1`$ comes from
  running the argument on $`(d-1)`$-dimensional cube surfaces. The estimate
  here also holds for every pair of radii $`\tfrac12\le\rho\lt R\le1`$.
- **The Harnack inequality is recovered with the same form of constant.**
  `HarnackUniform` gives $`\exp(C\sqrt{\Lambda/\lambda})`$, which has the same
  dependence on $`\Lambda/\lambda`$ as `harnack` there. It is not sharper. It
  assumes only $`u\ge0`$ almost everywhere, where `harnack` assumes $`u\gt0`$ at
  every point.
- **The weak Harnack inequality is recovered in the same range, with the same
  form of constant.** `WeakHarnackUniform` gives the constant
  $`\exp(C\sqrt{\Lambda/\lambda})`$, of the same form as `weak_harnack` there, for
  every exponent $`0\lt\eta\lt\frac d{d-2}`$, the range in which the earlier
  repository proves the inequality.
- **Not covered:** Hölder continuity, which is neither stated nor proved in
  this repository; nonsymmetric coefficients; and domains other than the
  unit cube and its concentric subcubes. The statements are not rescaled or
  translated to general cubes or balls.
