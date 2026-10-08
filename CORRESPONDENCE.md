# Correspondence: paper ↔ Lean

This document maps the manuscript *Coarse ellipticity and De
Giorgi–Nash–Moser theory in the optimal range* (Armstrong, Avelin, Kuusi,
Turpeinen), included as [`paper/coarse-grained-dgnm.pdf`](paper/coarse-grained-dgnm.pdf),
to the Lean formalization, so that a reader of the paper can locate where each
definition and result is stated and proved.

**Conventions.**
- Numbers are those of the PDF in [`paper/`](paper/). The **Source** column
  gives the number, the title of the result and its LaTeX label in the
  source of the manuscript, also in [`paper/`](paper/).
- In the tables, Lean names are given in full. **Statement files**: every
  declaration of [`CoarseDeGiorgi/Statements/`](CoarseDeGiorgi/Statements/)
  is in a file of its own, and for these the File column gives only the base
  name (for example `Harnack.lean` for
  `CoarseDeGiorgi/Statements/Harnack.lean`, which states
  `CoarseDeGiorgi.harnack`). Every declaration of that directory appears in
  a table below. Other files are given by their path from the repository
  root.
- **Status**: `proved` — formalized and proved as stated, up to the rendering
  conventions below; `partial` — the parts of the statement that the proofs
  use are proved, and the rest is not stated in Lean (the row or the note
  after the table says what is missing); `definition` — a definition rather
  than a theorem; `not formalized` — absent from the Lean development.
- The main results (Section 1 of the paper), Propositions 3.4, 11.2, 11.3
  and B.1, Lemmas B.2, C.1 and D.1 and most numbered results of Sections 2–9 have
  statement files, as do most definitions. The other results are proved inside the library, and their
  rows name the declarations that carry them; where the paper's statement is
  split over several declarations, the row names the principal ones.
- The main results are also restated using only Mathlib and checked with
  `leanprover/comparator`; see [`COMPARATORS.md`](COMPARATORS.md) and the
  table [Mathlib-only restatements](#mathlib-only-restatements) below.

**Rendering conventions.** These apply to every row and are not repeated.
- **Space and cubes.** Points are `Fin d → ℝ` (`Vec d`); the unit cube
  $`\square_0=(-\tfrac12,\tfrac12)^d`$ is `originCube 1` and $`\rho\square_0`$ is
  `originCube ρ`; cubes and simplices are open. `Vec d` carries the sup norm
  of `CoarseGraining`, so Euclidean lengths and distances are written with
  `euclidNorm` and `euclidDist`; the matrix norm is the ℓ² operator norm.
- **Coefficients.** `IsWeightedCoeffOn V a` is (2.1) together with
  measurability and a.e. positive definiteness; Mathlib's `Matrix.PosDef`
  includes symmetry, so the coefficients are symmetric, as in the paper.
- **Domains.** Section 2 and Appendix A are stated in the paper for bounded
  connected Lipschitz domains. The formal versions are stated for bounded
  open convex domains (`IsOpenBoundedConvexDomain`), which include the cubes
  and simplices on which the paper uses them.
- **Weighted space.** $`H^1_{\mathbf a}(U)`$ is `MemH1a a U u G`: the pair
  $`(u,G)`$ is a limit of smooth functions of finite energy in the norm (2.2),
  with convergence of $`u`$ in $`L^1`$ on compact subsets and of the gradients
  in weighted energy. Sub-, super- and solutions carry the explicit gradient
  `G`.
- **Coarse-grained matrices.** The directional quantities (2.6) and (1.5) are
  suprema over weighted solutions, valued in `EReal`. The matrices
  $`\mathbf a(U)`$ and $`\mathbf a_{\ast}^{-1}(U)`$ are the unique positive
  definite matrices with these quadratic forms (Propositions 2.2 and 2.3). The
  Lean names keep the word "response": `upperResponse` is $`\mathbf a(U)`$,
  `lowerResponseInv` is $`\mathbf a_{\ast}^{-1}(U)`$, `upperMoment` and
  `lowerMoment` are the coarse ellipticity constants, and `contrast` is the
  coarse ellipticity ratio $`\Theta`$.
- **Extended values.** Norms, energies, the coarse ellipticity constants
  and $`\Theta`$ are valued in `ℝ≥0∞`; the Harnack constants use the
  real value of $`\Theta`$, which is finite under the hypotheses.
- **Coarse ellipticity constants.** Only scale summability one is
  formalized: `upperMoment` and `lowerMoment` are $`\Lambda_{s,1,p}(\square_0)`$
  and $`\lambda_{t,1,q}(\square_0)`$, for finite exponents, and `cubeUpperMoment`
  and `cubeLowerMoment` are their cubical versions. The regularity estimates
  of the paper use only this case. Proposition 3.4, which the paper states for
  every summability index and for infinite exponents, and Lemma C.1, which it
  states also for $`p=\infty`$, are formalized in this case too.
- **Traces.** As in the paper, the trace of a function on a cube boundary is
  the restriction of the function: the statements of Sections 5–9 restrict
  the given representative.
- **Constants** are chosen after the parameters and before the coefficient
  field and the function, as in the paper.

**Summary.** The manuscript has 46 numbered statements: Theorems A, C, D and
F, Corollaries B and E, 39 numbered results of Sections 2–11 and the
appendices, and Definition 3.3. All 46 are formalized: 32 `proved` or
`definition`, and 14 `partial` (Theorem D, Propositions 2.1, 3.4, A.1 and
B.1, Lemmas 4.1, 5.1, 9.3, 9.4, 11.1, A.2, B.2 and C.1, and Definition 3.3).
For Theorem D, the infinite exponents are not formalized; for Proposition
3.4, the infinite exponents and the summability indices other than one; for
Proposition B.1 and Lemmas B.2 and C.1, the case $`p=\infty`$; in the other
partial rows the missing parts are properties or cases that the proofs do not
use, or, for Lemmas 4.1, 9.3 and 9.4, slightly weaker forms that suffice for
the main results. The `not formalized` rows are remarks, examples,
comparisons with other work (among them the comparison of the cube
quasi-norm with the Besov space defined through the Fourier transform, after
Proposition B.1), and a few facts that the formal proofs avoid, such as the
simplex count (3.5) and the coarse ellipticity constants of a constant
matrix.

Section 1.5 of the manuscript says that all its results are formalized, with
scale summability one and, for Proposition 3.4 and Appendix C, finite
exponents. The exceptions are the infinite exponents in Theorem D and in
Appendix B, which are not formalized here. Section 1.5 also says that the
formal proofs follow the arguments of the paper except for the
reconstruction estimate of Lemma 4.2; the other differences, among them the
proof of Lemma 9.6 and some steps of Appendix B, are recorded in the notes
below and in the last table.

---

## Section 1: introduction and main results

| Source | Lean declaration | File | Status |
|---|---|---|---|
| the unit cube $`\square_0`$ and its dilations $`\rho\square_0`$ | `CoarseDeGiorgi.originCube` | `OriginCube.lean` | definition |
| $`\square_0`$ agrees with the unit cube of `CoarseGraining` | `CoarseDeGiorgi.originCube_one_eq_cg` | `OriginCubeOneEqCg.lean` | proved |
| Section 1.7: the cubes $`\rho\square_0`$ are open | `CoarseDeGiorgi.isOpen_originCube` | `IsOpenOriginCube.lean` | proved |
| (1.1), `e.subsolution.equation`: weak solutions and subsolutions | see (2.3) below | | definition |
| (1.3), `e.goodrange`: local boundedness and the Harnack inequality hold if $`\mathbf a\in W^{-\alpha,p}\cap L^1`$, $`\mathbf a^{-1}\in W^{-\beta,q}\cap L^1`$ and $`\frac{\alpha+\beta}2+\frac{d-1}2(\frac1p+\frac1q)\lt1`$ | see Corollary E below | | proved |
| (1.4), `e.upper.matrix.definition`: the coarse-grained matrix $`\mathbf a(U)`$, by the minimum with affine boundary values | `CoarseDeGiorgi.upperResponse`, with the minimum in `CoarseDeGiorgi.upperResponse_spec` (Proposition 2.2) | `UpperResponse.lean`, `UpperResponseSpec.lean` | definition |
| (1.5), `e.lower.matrix.definition`: the coarse-grained matrix $`\mathbf a_{\ast}^{-1}(U)`$ | `CoarseDeGiorgi.lowerDirectionalResponse`, `CoarseDeGiorgi.lowerResponseInv` | `LowerDirectionalResponse.lean`, `LowerResponseInv.lean` | definition |
| Section 1.2: the coarse ellipticity constants $`\Lambda_{s,1,p}(\square_0)`$ and $`\lambda_{t,1,q}(\square_0)`$ | `CoarseDeGiorgi.upperMoment`, `CoarseDeGiorgi.lowerMoment` (Definition 3.3) | `UpperMoment.lean`, `LowerMoment.lean` | definition |
| Section 1.2: $`\lambda_{t,1,q}(\square_0)\le\Lambda_{s,1,p}(\square_0)`$ | `CoarseDeGiorgi.Harnack.Moments.moment_matrix_sandwich` (see (3.14)) | `CoarseDeGiorgi/Harnack/Moments/MomentComparison.lean` | proved |
| Section 1.2: the constants of a constant matrix | — | — | not formalized |
| Section 1.2: with triadic cubes in place of simplices the constants are equivalent when $`s\lt\frac12(1-\frac1p)`$ and $`t\lt\frac12(1-\frac1q)`$ | see Proposition 3.4 (Section 3) | | partial |
| (1.6), `e.spatial.moment.ratio`: the coarse ellipticity ratio $`\Theta`$ | `CoarseDeGiorgi.contrast` | `Contrast.lean` | definition |
| after (1.6): $`\Theta\ge1`$ | `CoarseDeGiorgi.Harnack.Moments.moment_contrast_ge_one` | `CoarseDeGiorgi/Harnack/Moments/MomentComparison.lean` | proved |
| (1.7), `e.intro.parameters`: $`\sigma`$, $`\sigma_*`$, $`\theta`$ and $`r=2q/(q+1)`$ | `CoarseDeGiorgi.sigmaUpper`, `CoarseDeGiorgi.sigmaLower`, `CoarseDeGiorgi.paramTheta`, `CoarseDeGiorgi.paramR` | `SigmaUpper.lean`, `SigmaLower.lean`, `ParamTheta.lean`, `ParamR.lean` | definition |
| the positive part $`u_+`$ and local boundedness above (Theorem A) | `CoarseDeGiorgi.positivePart`, `CoarseDeGiorgi.LocallyBoundedAbove` | `PositivePart.lean`, `LocallyBoundedAbove.lean` | definition |
| Theorem A (local boundedness above), `t.cg.local.boundedness`, with (1.8), and Corollary B (bounds in $`L^\eta`$), `c.lr.bound`, with (1.9) | `CoarseDeGiorgi.local_boundedness` | `LocalBoundedness.lean` | proved |
| after Theorem A and after Corollary B: the powers $`\frac{d-1}{4\theta}`$ and $`\frac{d-1}{2\eta\theta}`$ of $`\Theta`$ are optimal | `CoarseDeGiorgi.optimal_powers` (Proposition 11.2, Section 11) | `OptimalPowers.lean` | proved |
| after Theorem A: comparison with the corresponding bound of the earlier paper | — | — | not formalized |
| the normalized moment and the essential infimum (Theorem C), and the exponent $`r^*=dr/(d-(1-t)r)`$ of Theorem C, which is that of (3.22) | `CoarseDeGiorgi.normalizedLpMoment`, `CoarseDeGiorgi.nonnegativeEssInf`, `CoarseDeGiorgi.rStarParam` | `NormalizedLpMoment.lean`, `NonnegativeEssInf.lean`, `RStarParam.lean` | definition |
| Theorem C (weak Harnack and Harnack inequalities), `t.harnack`: the weak Harnack inequality (1.10), `e.weak.harnack`, for every $`0\lt\eta\le r^*/2`$, with a constant depending on $`\eta`$ | `CoarseDeGiorgi.weak_harnack_range` | `WeakHarnackRange.lean` | proved |
| Theorem C, `t.harnack`: the Harnack inequality (1.11), `e.harnack` | `CoarseDeGiorgi.harnack` | `Harnack.lean` | proved |
| after Theorem C: the weak Harnack inequality for uniformly elliptic coefficients for every $`0\lt\eta\lt d/(d-2)`$, and with part (i) of Theorem D for every exponent below the value of $`r^*/2`$ at $`t=0`$ | the Mathlib-only restatements `WeakHarnackUniform` and `WeakHarnackLpLq`; see [below](#mathlib-only-restatements) | | proved |
| after Theorem C: the range of $`\eta`$ does not depend on $`\Theta`$; the union of the ranges over the admissible parameters is exactly $`0\lt\eta\lt d/(d-2)`$; comparison with Trudinger and with Bella and Schäffner | — | — | not formalized |
| after Theorem C: for fixed $`d,p,q,s,t`$ the range $`0\lt\eta\le r^*/2`$ cannot be enlarged | `CoarseDeGiorgi.weak_harnack_sharpness` (Proposition 11.3, Section 11) | `WeakHarnackSharpness.lean` | proved |
| after Theorem C: optimality of $`\exp(C\sqrt\Theta)`$ (constant coefficients; Guerra's examples) | — | — | not formalized |
| (1.12), `e.negative.regularity.norm`: the cube quasi-norm $`\lVert\mathbf b\rVert_{\mathring{\underline B}^{-2s}_{p,1/2}(\square_0)}`$, for $`1\le p\lt\infty`$ | `CoarseDeGiorgi.besovCubeNorm` | `BesovCubeNorm.lean` | definition |
| after (1.12): the quasi-norm for $`p=\infty`$, and its comparison with the Besov space $`B^{-2s}_{p,1/2}(\mathbb R^d)`$ (through Proposition B.1, which is formalized, and the heat characterization of Kerkyacharian and Petrushev) | — | — | not formalized |
| Theorem D (conditions on the coefficients), `t.coefficient.conditions`, part (i), `c.classical.moments`, with (1.13), for finite $`p,q`$ | `CoarseDeGiorgi.moment_bounds_lebesgue` | `MomentBoundsLebesgue.lean` | proved |
| Theorem D, part (ii), `c.negative.regularity`, with (1.14), for finite $`p,q`$ | `CoarseDeGiorgi.moment_bounds_besov` | `MomentBoundsBesov.lean` | proved |
| Theorem D, part (iii), `c.negative.sobolev`, with (1.15), for finite $`p,q`$ ($`0\lt\varepsilon\le2\min\{s,t\}`$ written as $`\varepsilon\le2s`$ and $`\varepsilon\le2t`$) | `CoarseDeGiorgi.moment_bounds_sobolev` | `MomentBoundsSobolev.lean` | proved |
| Theorem D, parts (i)–(iii) with $`p=\infty`$ or $`q=\infty`$ | — | — | not formalized |
| after Theorem D, (1.16), `e.negative.regularity.range`: under part (i) or (ii), Theorems A and C and Corollary B hold when $`\theta\gt0`$, with the stated bound on $`\Theta`$ | the Mathlib-only restatements `LocalBoundednessLpLq`, `HarnackLpLq`, `WeakHarnackLpLq` (part (i)) and `LocalBoundednessBesov`, `HarnackBesov`, `WeakHarnackBesov` (part (ii)); see [below](#mathlib-only-restatements) | | proved |
| after Theorem D: infinite exponents reduce to finite ones | — | — | not formalized |
| (1.2), `e.intro.bs.range`, and (1.17), `e.classical.moment.range`: for part (i), indices $`s,t\gt0`$ with $`\theta\gt0`$ exist exactly when $`\frac1p+\frac1q\lt\frac2{d-1}`$ | "only if": `CoarseDeGiorgi.classical_moments_converse`; "if": in the solutions of the comparators `LocalBoundednessLpLq`, `HarnackLpLq` and `WeakHarnackLpLq`, with explicit indices (for example $`s=t=\theta_0/4`$ in `HarnackLpLq`, where $`\theta_0=1-\frac{d-1}2(\frac1p+\frac1q)`$) | `ClassicalMomentsConverse.lean`; `CoarseDeGiorgiAudit/Solution/HarnackLpLq.lean` and the two other files | proved |
| after Theorem D: the fine index $`\frac12`$; comparison with the earlier negative Sobolev criterion | — | — | not formalized |
| Corollary E (coefficients in negative Sobolev spaces), `c.sobolev.coefficients`, with (1.18), `e.sobolev.local.boundedness`, and (1.19), `e.sobolev.harnack` | `CoarseDeGiorgi.local_boundedness_sobolev` (the local bound (1.18)), `CoarseDeGiorgi.harnack_sobolev` (the Harnack inequality (1.19)), with independent constants | `LocalBoundednessSobolev.lean`, `HarnackSobolev.lean` | proved |
| before Theorem F: for $`1\lt p,q\lt\infty`$, neither (1.16) for part (ii) nor (1.17) for part (i) can be relaxed | `CoarseDeGiorgi.sharpness`, with $`\alpha=2s`$, $`\beta=2t`$, $`\xi=p`$, $`\zeta=q`$ (for part (i), $`\alpha=\beta=0`$) | `Sharpness.lean` | proved |
| Theorem F (sharpness of the range), `t.sharpness`, with (1.20), `e.sharpness`, and the unboundedness near every point of the segment $`\{(x_1,0):\lvert x_1\rvert\lt\frac12\}`$ | `CoarseDeGiorgi.sharpness` (the integrabilities $`p`$, $`q`$ of Theorem F are named $`\xi`$, $`\zeta`$ there and in the `Sharpness` comparator) | `Sharpness.lean` | proved |
| after Theorem F: description of the examples, and why the threshold is $`\theta_0=0`$ | — (the examples themselves are formalized, Section 11) | — | not formalized |
| Sections 1.3 and 1.4: relation to previous work, ideas of the proof | — | — | not formalized |
| Section 1.7, (1.21), `e.fractional.seminorm`: the fractional seminorm and norm | `CoarseDeGiorgi.fracKernelWithDimension`, `CoarseDeGiorgi.fracKernel`, `CoarseDeGiorgi.fracSeminorm`, `CoarseDeGiorgi.fracNorm` | `FracKernelWithDimension.lean`, `FracKernel.lean`, `FracSeminorm.lean`, `FracNorm.lean` | definition |
| Section 1.7: the Sobolev exponents $`\xi^*`$ and $`\xi^*_\partial`$ of $`W^{\alpha,\xi}`$ | written out in the statements that use them (`CoarseDeGiorgi.critical_surface_embedding`, `CoarseDeGiorgi.dnpvCriticalExponent`); for $`\alpha=1-t`$ and $`\xi=r`$ see (3.22) | `CriticalSurfaceEmbedding.lean`, `DnpvCriticalExponent.lean` | definition |
| Section 1.7: the arrays $`\nabla^jw`$ of weak partial derivatives, one entry for each of the $`d^j`$ ordered index tuples; their uniqueness almost everywhere on open sets | `CoarseDeGiorgi.IsWeakDerivArray`; `CoarseDeGiorgi.isWeakDerivArray_ae_eq` | `IsWeakDerivArray.lean`, `IsWeakDerivArrayAeEq.lean` | definition |
| Section 1.7: the seminorm (1.21) of the array $`\nabla^mw`$, with the Euclidean norm of the array | `CoarseDeGiorgi.arrayFracSeminorm` | `ArrayFracSeminorm.lean` | definition |
| Section 1.7: the norms $`\lVert\cdot\rVert_{W^{\beta,\xi}(U)}`$ for every order $`\beta\ge0`$ on an open $`U`$, and $`W^{0,\xi}(U)=L^\xi(U)`$ | `CoarseDeGiorgi.sobolevNorm`, with its value at the weak derivatives `CoarseDeGiorgi.sobolevNorm_eq_of_isWeakDerivArray` and the order zero `CoarseDeGiorgi.sobolevNorm_zero` | `SobolevNorm.lean`, `SobolevNormEqOfIsWeakDerivArray.lean`, `SobolevNormZero.lean` | definition |
| (1.22), `e.negative.sobolev.norm`: the negative Sobolev norm, for $`1\lt p\lt\infty`$ | `CoarseDeGiorgi.negSobolevNorm` | `NegSobolevNorm.lean` | definition |
| (1.22) for $`p=\infty`$ | — | — | not formalized |

## Section 2: weighted spaces and coarse-grained matrices

| Source | Lean declaration | File | Status |
|---|---|---|---|
| (2.1), `e.weighted.hypotheses`: the standing assumption | `CoarseDeGiorgi.IsWeightedCoeffOn` | `IsWeightedCoeffOn.lean` | definition |
| smooth functions of finite energy, their gradient and the energy $`\mathcal E_U`$ | `CoarseDeGiorgi.IsSmoothCore`, `CoarseDeGiorgi.smoothGrad`, `CoarseDeGiorgi.weightedEnergy` | `IsSmoothCore.lean`, `SmoothGrad.lean`, `WeightedEnergy.lean` | definition |
| (2.2), `e.weighted.norm`: the norm of $`H^1_{\mathbf a}(U)`$ | `CoarseDeGiorgi.h1aWeightedNorm` | `H1aWeightedNorm.lean` | definition |
| $`H^1_{\mathbf a}(U)`$ and $`H^1_{\mathbf a,0}(U)`$ | `CoarseDeGiorgi.MemH1a`, `CoarseDeGiorgi.MemH1a0` | `MemH1a.lean`, `MemH1a0.lean` | definition |
| (2.3), `e.weighted.subsolution`: solutions and subsolutions, $`\mathcal C_{\mathrm{sol}}(U)`$ and $`\mathcal C_{\mathrm{sub}}(U)`$ | `CoarseDeGiorgi.IsWeightedSolution`, `CoarseDeGiorgi.IsWeightedSubsolution`, `CoarseDeGiorgi.Csol`, `CoarseDeGiorgi.Csub` | `IsWeightedSolution.lean`, `IsWeightedSubsolution.lean`, `Csol.lean`, `Csub.lean` | definition |
| supersolutions | `CoarseDeGiorgi.IsWeightedSupersolution` | `IsWeightedSupersolution.lean` | definition |
| Proposition 2.1 (harmonic replacement), `p.harmonic.replacement`, with (2.4) and (2.5) | `CoarseDeGiorgi.Weighted.harmonic_replacement`, `CoarseDeGiorgi.Weighted.exists_harmonic_replacement` | `CoarseDeGiorgi/Weighted/HarmonicProperties.lean`, `CoarseDeGiorgi/Weighted/HarmonicReplacement.lean` | partial |
| (2.6), `e.upper.directional.definition`: the directional quantities $`\mathbf a(U,e;\mathcal C_{\mathrm{sol}})`$ and $`\mathbf a(U,e;\mathcal C_{\mathrm{sub}})`$ | `CoarseDeGiorgi.upperDirectionalResponseSol`, `CoarseDeGiorgi.upperDirectionalResponseSub` | `UpperDirectionalResponseSol.lean`, `UpperDirectionalResponseSub.lean` | definition |
| Proposition 2.2 (the coarse-grained matrix $`\mathbf a(U)`$), `p.upper.dirichlet`: $`\mathbf a(U,e;\mathcal C_{\mathrm{sol}})`$ is the quadratic form of a unique positive definite matrix | `CoarseDeGiorgi.upperResponse_existsUnique` | `UpperResponseExistsUnique.lean` | proved |
| Proposition 2.2: the minimum (1.4) is attained and equals that quadratic form, (2.7), (2.8) and (2.9) | `CoarseDeGiorgi.upperResponse_spec` | `UpperResponseSpec.lean` | proved |
| Proposition 2.3 (the coarse-grained matrix $`\mathbf a_{\ast}(U)`$), `p.lower.matrix`: (1.5) is the quadratic form of a unique positive definite matrix | `CoarseDeGiorgi.lowerResponse_existsUnique` | `LowerResponseExistsUnique.lean` | proved |
| Proposition 2.3: attainment by a mean-zero solution, (2.10)–(2.13) | `CoarseDeGiorgi.lowerResponseInv_spec` | `LowerResponseInvSpec.lean` | proved |
| end of Section 2.2: the results apply on the simplices of the triangulations | `CoarseDeGiorgi.simplexCell_isOpenBoundedConvexDomain`, `CoarseDeGiorgi.simplexCell_nonempty`, `CoarseDeGiorgi.weightedCoeffOn_simplexCell` | `SimplexCellIsOpenBoundedConvexDomain.lean`, `SimplexCellNonempty.lean`, `WeightedCoeffOnSimplexCell.lean` | proved |
| (2.14), `e.matrix.ordering`: $`\mathbf a_{\ast}(U)\le\mathbf a(U)`$ | `CoarseDeGiorgi.Harnack.Moments.inverse_response_order_quadratic` (the case $`U=\square_0`$) | `CoarseDeGiorgi/Harnack/Moments/InverseOrder.lean` | partial |
| (2.15), `e.upper.subadditivity`: subadditivity of $`\mathbf a(U)`$ over a finite or countable partition up to a null set, with an absolutely convergent series | `CoarseDeGiorgi.upper_subadditivity_countable` | `UpperSubadditivityCountable.lean` | proved |
| (2.16), `e.lower.cube.aggregation`: the same for $`\mathbf a_{\ast}^{-1}(U)`$ | `CoarseDeGiorgi.lower_aggregation_countable` | `LowerAggregationCountable.lean` | proved |

Proposition 2.1: existence, the relation $`H_Ug-g\in H^1_{\mathbf a,0}(U)`$,
the orthogonality (2.4), the energy identity (2.5) and uniqueness are proved.
Linearity, $`H_U(g+c)=H_Ug+c`$ and the range bound are proved for affine data
on a simplex, the case Section 6 uses; they are not stated in general.
(2.14) is proved in the case that the proofs use, $`U=\square_0`$, where it
enters the comparison (3.14). (2.15) and (2.16) are stated for an open
bounded convex domain $`U`$ and a finite or countable family of pairwise
disjoint open bounded convex pieces whose union covers $`U`$ up to a null set,
the only case the paper uses (Section 9.5 cuts a simplex into simplices,
Appendix C cuts cubes into simplices and simplices into cubes); the
conclusion is that the series of matrices converges absolutely and that the
difference between the weighted series and the matrix of $`U`$ is positive
semidefinite. The comparison (3.14) uses the earlier special cases for the
partitions $`\mathscr T_k`$ of $`\square_0`$
(`CoarseDeGiorgi.Harnack.Moments.upper_gluing`,
`CoarseDeGiorgi.Harnack.Moments.lower_whole_cube_aggregation`), and for the
cubes of Lemma 4.1 the formal proof applies the mean-gradient bound (2.11) on
each simplex and Jensen's inequality instead of (2.16).

## Section 3: triangulations and coarse ellipticity constants

| Source | Lean declaration | File | Status |
|---|---|---|---|
| Euclidean length and distance (distances marked $`\infty`$ use the sup norm) | `CoarseDeGiorgi.euclidNorm`, `CoarseDeGiorgi.euclidDist` | `EuclidNorm.lean`, `EuclidDist.lean` | definition |
| (3.1), `e.simplex.def`: the standard simplices | `CoarseDeGiorgi.simplex` | `Simplex.lean` | definition |
| (3.2), `e.simplex.family`: the triangulation $`\mathscr T_k`$ and its simplices | `CoarseDeGiorgi.gridOffset`, `CoarseDeGiorgi.triangulation`, `CoarseDeGiorgi.SimplexIndex`, `CoarseDeGiorgi.simplexCell` | `GridOffset.lean`, `Triangulation.lean`, `SimplexIndex.lean`, `SimplexCell.lean` | definition |
| after (3.2): $`\mathscr T_k`$ has $`d!\,3^{kd}`$ simplices, all in $`\square_0`$ | `CoarseDeGiorgi.triangulation_card`, `CoarseDeGiorgi.simplexCell_subset_originCube` | `TriangulationCard.lean`, `SimplexCellSubsetOriginCube.lean` | proved |
| (3.3), `e.partition.average`: the arithmetic mean over $`\mathscr T_k`$ is a volume average | `CoarseDeGiorgi.LowerFractional.lower_spatial_weight_eq_cellAverage` | `CoarseDeGiorgi/LowerFractional/SpatialWeights.lean` | proved |
| $`\mathscr T_k(U)`$, the simplices of $`\mathscr T_k`$ contained in $`U`$ | `CoarseDeGiorgi.triangulationIn` | `TriangulationIn.lean` | definition |
| (3.4), `e.partition.restricted` | `CoarseDeGiorgi.Localization.sum_cells_overlap_le` (the bounded-overlap form used for Proposition 5.3) | `CoarseDeGiorgi/Localization/SummedCells.lean` | partial |
| (3.5), `e.simplex.count`: the count of simplices near a ball | — (the proofs count lattice points directly) | — | not formalized |
| Whitney cubes: triadic cubes, fivefold closed dilations, admissibility, the selected cubes, sup-norm distances | `CoarseDeGiorgi.triadicCenter`, `CoarseDeGiorgi.closedTriadicCube`, `CoarseDeGiorgi.fivefoldClosedTriadicCube`, `CoarseDeGiorgi.closedReferenceCube`, `CoarseDeGiorgi.whitneyAdmissible`, `CoarseDeGiorgi.whitneyCubes`, `CoarseDeGiorgi.infSupDist`, `CoarseDeGiorgi.pointSupDist` | `TriadicCenter.lean`, `ClosedTriadicCube.lean`, `FivefoldClosedTriadicCube.lean`, `ClosedReferenceCube.lean`, `WhitneyAdmissible.lean`, `WhitneyCubes.lean`, `InfSupDist.lean`, `PointSupDist.lean` | definition |
| Lemma 3.1 (Whitney cubes), `l.whitney.cubes`, with (3.6) | `CoarseDeGiorgi.whitney_cubes` | `WhitneyCubesProperties.lean` | proved |
| Whitney simplices and their size, (3.7), `e.whitney.simplex.size` | `CoarseDeGiorgi.ExteriorCell`, `CoarseDeGiorgi.exteriorCellSet`, `CoarseDeGiorgi.exteriorCellCenter`, `CoarseDeGiorgi.exteriorCellVertex` | `ExteriorCell.lean`, `ExteriorCellSet.lean`, `ExteriorCellCenter.lean`, `ExteriorCellVertex.lean` | definition |
| after (3.7): the Whitney simplices of size $`3^{-j}`$ in $`\square_0`$ belong to $`\mathscr T_j`$ | part of (6.6) in `CoarseDeGiorgi.harmonic_extension`, for the simplices of $`\mathscr W_h^j`$ | `HarmonicExtension.lean` | proved |
| vertices of Whitney simplices; free vertices (hanging vertices are the vertices that are not free; Figure 1) | `CoarseDeGiorgi.IsWhitneyVertex`, `CoarseDeGiorgi.IsFreeVertex` | `IsWhitneyVertex.lean`, `IsFreeVertex.lean` | definition |
| Lemma 3.2 (interpolation on Whitney simplices), `l.whitney.interpolation`: existence and uniqueness | `CoarseDeGiorgi.IsWhitneyInterpolant`, `CoarseDeGiorgi.whitney_interpolation_existsUnique` | `IsWhitneyInterpolant.lean`, `WhitneyInterpolationExistsUnique.lean` | proved |
| Lemma 3.2: the interpolant | `CoarseDeGiorgi.whitneyInterpolation`, `CoarseDeGiorgi.whitneyInterpolation_spec` | `WhitneyInterpolationDef.lean`, `WhitneyInterpolationSpec.lean` | definition |
| Lemma 3.2: uniqueness among continuous functions on the exterior, the range bound and (3.8), `e.interpolation.gradient` | `CoarseDeGiorgi.whitney_interpolation` | `WhitneyInterpolation.lean` | proved |
| Definition 3.3 (coarse ellipticity constants), `d.cg.constants`: the coarse-grained matrices of the simplices and their means over $`\mathscr T_k`$ | `CoarseDeGiorgi.upperResponseOnCell`, `CoarseDeGiorgi.lowerResponseInvOnCell`, `CoarseDeGiorgi.upperCellAverage`, `CoarseDeGiorgi.lowerCellAverage` | `UpperResponseOnCell.lean`, `LowerResponseInvOnCell.lean`, `UpperCellAverage.lean`, `LowerCellAverage.lean` | definition |
| Definition 3.3, (3.10), (3.11), in the form (3.12), (3.13): $`\Lambda_{s,1,p}(\square_0)`$ and $`\lambda_{t,1,q}(\square_0)`$ | `CoarseDeGiorgi.upperMoment`, `CoarseDeGiorgi.lowerMoment` | `UpperMoment.lean`, `LowerMoment.lean` | partial |
| after Definition 3.3: the lower constant never exceeds the upper one | `CoarseDeGiorgi.Harnack.Moments.moment_matrix_sandwich` (for the formalized indices) | `CoarseDeGiorgi/Harnack/Moments/MomentComparison.lean` | proved |
| after (3.13): the constants of a constant matrix | — | — | not formalized |
| (3.14), `e.moment.comparison`, and $`\Theta\ge1`$ | `CoarseDeGiorgi.Harnack.Moments.moment_matrix_sandwich`, `CoarseDeGiorgi.Harnack.Moments.moment_contrast_ge_one` | `CoarseDeGiorgi/Harnack/Moments/MomentComparison.lean` | proved |
| (3.15), `e.cubical.family`: the triadic cubes $`\mathscr Q_k`$ of $`\square_0`$ | `CoarseDeGiorgi.cubeCell` | `CubeCell.lean` | definition |
| after (3.15): the cubes are open bounded convex domains on which the standing assumption holds | `CoarseDeGiorgi.cubeCell_isOpenBoundedConvexDomain`, `CoarseDeGiorgi.cubeCell_nonempty`, `CoarseDeGiorgi.weightedCoeffOn_cubeCell` | `CubeCellIsOpenBoundedConvexDomain.lean`, `CubeCellNonempty.lean`, `WeightedCoeffOnCubeCell.lean` | proved |
| after (3.15): the cubical constants $`\widetilde\Lambda_{s,\mathsf m,p}(\square_0)`$ and $`\widetilde\lambda_{t,\mathsf m,q}(\square_0)`$, Definition 3.3 with $`\mathscr Q_k`$ in place of $`\mathscr T_k`$ | `CoarseDeGiorgi.upperResponseOnCube`, `CoarseDeGiorgi.lowerResponseInvOnCube`, `CoarseDeGiorgi.cubeUpperCellAverage`, `CoarseDeGiorgi.cubeLowerCellAverage`, `CoarseDeGiorgi.cubeUpperMoment`, `CoarseDeGiorgi.cubeLowerMoment` | `UpperResponseOnCube.lean`, `LowerResponseInvOnCube.lean`, `CubeUpperCellAverage.lean`, `CubeLowerCellAverage.lean`, `CubeUpperMoment.lean`, `CubeLowerMoment.lean` | partial |
| Proposition 3.4 (comparison with cubes), `p.cubical.simplicial.equivalence`: (3.17), `e.Lambda.cube.simplex.equivalence`, and (3.18), `e.lambda.cube.simplex.equivalence`, in the range (3.16), `e.cubical.simplicial.range` | `CoarseDeGiorgi.cubical_simplicial_equivalence` | `CubicalSimplicialEquivalence.lean` | partial |
| Proposition 3.4, last sentence: the inequalities with constant one for all $`s,t\gt0`$ and $`1\le p,q`$ | `CoarseDeGiorgi.cubical_simplicial_equivalence_const_one` | `CubicalSimplicialEquivalenceConstOne.lean` | partial |
| (3.19), `e.spatial.moment.range`: the coarse ellipticity condition | `CoarseDeGiorgi.spatialMomentRange` | `SpatialMomentRange.lean` | definition |
| after (3.19): under (3.16), the condition is equivalent to the same condition for $`\widetilde\Lambda_{s,1,p}`$ and $`\widetilde\lambda_{t,1,q}`$ | `CoarseDeGiorgi.cubeSpatialMomentRange`, `CoarseDeGiorgi.cubical_condition_iff` | `CubeSpatialMomentRange.lean`, `CubicalConditionIff.lean` | proved |
| (3.20), `e.cubical.simplicial.ratio`: $`\widetilde\Theta`$ and $`\widetilde\Theta\le\Theta\le C\widetilde\Theta`$ under (3.16) | `CoarseDeGiorgi.cubeContrast`, `CoarseDeGiorgi.cubical_ratio_comparison` | `CubeContrast.lean`, `CubicalRatioComparison.lean` | proved |
| after (3.20): Theorems A and C and Corollary B hold with $`\widetilde\Theta`$ in place of $`\Theta`$ | `CoarseDeGiorgi.local_boundedness_cubical`, `CoarseDeGiorgi.weak_harnack_cubical`, `CoarseDeGiorgi.harnack_cubical` | `LocalBoundednessCubical.lean`, `WeakHarnackCubical.lean`, `HarnackCubical.lean` | proved |
| (3.21), `e.reconstruction.parameters`: identities between $`\sigma`$, $`\sigma_*`$, $`s`$, $`t`$ and $`r`$ | proved where they are used, for example `CoarseDeGiorgi.Recurrence.alpha_sub_beta_eq` | `CoarseDeGiorgi/Recurrence/Params.lean` | partial |
| (3.22), `e.sobolev.exponents`: the order $`1-t`$ and the exponents $`r^*`$ and $`r^*_\partial`$ | `CoarseDeGiorgi.alphaParam`, `CoarseDeGiorgi.rStarParam`, `CoarseDeGiorgi.rBoundaryParam` | `AlphaParam.lean`, `RStarParam.lean`, `RBoundaryParam.lean` | definition |
| (3.23), `e.parameter.facts` | `CoarseDeGiorgi.Recurrence.sup_parameter_facts` and similar lemmas, in the forms used | `CoarseDeGiorgi/Recurrence/Params.lean` | partial |

Definition 3.3 is formalized for scale summability one and finite spatial
exponents, the only case used by the regularity estimates; the general
indices $`\mathsf m`$ and $`p=\infty`$ are not formalized. The comparison (3.14)
and the ordering of the two constants are proved for these indices. The same
holds for the cubical constants, for Proposition 3.4 and for Lemma C.1: they
are formalized for $`\mathsf m=1`$ and finite $`p,q`$, and the cases $`p=\infty`$
or $`q=\infty`$ and the independence of the constant from $`\mathsf m`$ are not.
Proposition 3.4 is two declarations, the comparison in the range (3.16) with
its constant $`C`$ and the inequalities with constant one, which hold for all
$`s,t\gt0`$; one constant serves both inequalities of the first. `upperMoment`
and `cubeUpperMoment` are $`\Lambda_{s,1,p}`$ and $`\widetilde\Lambda_{s,1,p}`$,
which the paper defines as squares of the discounted sums. (3.20) is stated
without the assumption (3.19), which makes it stronger; the inequalities hold
in $`[0,\infty]`$. The three cubical forms of Theorems A and C and Corollary B
take the cubical hypotheses $`\widetilde\Lambda_{s,1,p}\lt\infty`$,
$`\widetilde\lambda_{t,1,q}\gt0`$ and the range (3.16), so their statements involve
no simplices.

Lemma 3.2: functions on the exterior
$`\mathbb R^d\setminus\tau\overline{\square}_0`$ are encoded as
functions on $`\mathbb R^d`$ that vanish on $`\tau\overline{\square}_0`$, which
fixes the values that the lemma leaves free, so that uniqueness is literal;
the statements that use the interpolant evaluate it only on the exterior.

## Section 4: embedding into fractional Sobolev spaces

| Source | Lean declaration | File | Status |
|---|---|---|---|
| the cubes $`Q=z+\square_{-n}`$, $`z\in3^{-n-1}\mathbb Z^d`$, their subcubes and the averages $`P_k(f;Q)`$ | `CoarseDeGiorgi.auxCube`, `CoarseDeGiorgi.auxDescendantIndices`, `CoarseDeGiorgi.auxDescendantCube`, `CoarseDeGiorgi.auxDescendantAverage`, `CoarseDeGiorgi.auxAverage` | `AuxCube.lean`, `AuxDescendantIndices.lean`, `AuxDescendantCube.lean`, `AuxDescendantAverage.lean`, `AuxAverage.lean` | definition |
| Lemma 4.1 (the matrices $`\mathbf a_{\ast}`$ on cubes), `l.lower.averages`, with (4.1) | `CoarseDeGiorgi.LowerFractional.lower_auxAverage_norm_local` | `CoarseDeGiorgi/LowerFractional/LocalAuxNorm.lean` | partial |
| Lemma 4.2 (reconstruction from triadic gradient averages), `l.fractional.reconstruction`, with (4.2) | `CoarseDeGiorgi.fractional_reconstruction` | `FractionalReconstruction.lean` | proved |
| Proposition 4.3 (embedding into $`W^{1-t,r}`$), `p.lower.fractional`: the scale-by-scale bound (4.3), `e.lower.fractional.local`, for every cube $`Q=z+\square_{-n}\subset\square_0`$ | `CoarseDeGiorgi.lower_fractional_scale_bound` | `LowerFractionalScaleBound.lean` | proved |
| Proposition 4.3: (4.4), `e.lower.fractional`, for every such $`Q`$ | `CoarseDeGiorgi.lower_fractional_bound` | `LowerFractionalBound.lean` | proved |
| Proposition 4.3: continuity of $`H^1_{\mathbf a}(Q)\subset W^{1-t,r}(Q)`$ for every such $`Q`$ | `CoarseDeGiorgi.lower_fractional_embedding` | `LowerFractionalEmbedding.lean` | proved |
| Proposition 4.3: every $`w\in H^1_{\mathbf a}(\square_0)`$ belongs to $`L^r(\square_0)`$ | `CoarseDeGiorgi.lower_fractional_memLr` | `LowerFractionalMemLr.lean` | proved |

The cube $`Q=z+\square_{-n}`$ is `auxCube (n + 1) z'` with $`z=3^{-n-1}z'`$, and
`auxAverage m k z f` averages over the subcubes of side $`3^{1-k}`$, so it is
$`P_{k-1}(f;Q)`$ for $`m=n+1`$. With this shift, `fractional_reconstruction`
is (4.2) with the constant multiplied by $`3^{-(1-\alpha)}`$, for every such
cube, and `lower_fractional_scale_bound` is (4.3) exactly. The cubes of
Proposition 4.3 are those with `auxCube m z ⊆ originCube 1`, which include
$`\square_0`$ itself and the cubes that touch $`\partial\square_0`$; the inclusion
forces $`m\ge1`$, that is $`n\ge0`$. As in the paper, `lower_fractional_memLr`
is the continuity of the embedding at $`Q=\square_0`$. Lemma 4.1 is proved with
$`P_{k-1}(\nabla w;Q)`$ in place of $`P_k(\nabla w;Q)`$ on the left of (4.1); by
Jensen's inequality this is weaker than (4.1), and it is the form that the
proof of (4.3) uses. Lemma 4.2 is proved by a different argument than the
paper's, which reconstructs the function through Neumann problems: after an
even reflection to a periodic box, the differences of smooth averages of the
function at successive scales are written as pairings of its gradient with
explicit kernels, and these blocks are bounded by kernel cancellation against
the triadic averages and Schur's test
([`CoarseDeGiorgi/Foundations/Reconstruction/`](CoarseDeGiorgi/Foundations/Reconstruction/)).

## Section 5: cubes with good radii

| Source | Lean declaration | File | Status |
|---|---|---|---|
| (5.1), `e.selection.parameters`: the interval $`J`$ | `CoarseDeGiorgi.selectionInterval` | `SelectionInterval.lean` | definition |
| (5.2), `e.boundary.fractional.seminorm`: the cube boundary, its measure, and the seminorm and norm on it | `CoarseDeGiorgi.cubeSurface`, `CoarseDeGiorgi.faceCoordinateMeasures`, `CoarseDeGiorgi.cubeFaceMeasure`, `CoarseDeGiorgi.surfaceMeasure`, `CoarseDeGiorgi.surfaceFracSeminorm`, `CoarseDeGiorgi.surfaceFracNorm` | `CubeSurface.lean`, `FaceCoordinateMeasures.lean`, `CubeFaceMeasure.lean`, `SurfaceMeasure.lean`, `SurfaceFracSeminorm.lean`, `SurfaceFracNorm.lean` | definition |
| Lemma 5.1 (Sobolev inequality on cube boundaries), `l.critical.trace.embedding`, with (5.3) | `CoarseDeGiorgi.critical_surface_embedding` | `CriticalSurfaceEmbedding.lean` | partial |
| Lemma 5.2 (cutoff estimate for $`W^{\alpha,\xi}`$), `l.fractional.cutoff`, with (5.4) | `CoarseDeGiorgi.Foundations.FracGeometry.fractional_cutoff` | `CoarseDeGiorgi/Foundations/FracGeometry/Cutoff.lean` | proved |
| Proposition 5.3 (localization), `p.fractional.localization`: the covers by threefold enlargements of triadic cubes and their cutoffs | `CoarseDeGiorgi.IsFractionalCover` | `IsFractionalCover.lean` | definition |
| Proposition 5.3, with (5.5): both versions, and the convergence | `CoarseDeGiorgi.fractional_localization` | `FractionalLocalization.lean` | proved |
| Lemma 5.4 (integrated slicing), `l.fractional.slicing`, with (5.7): the constant $`C2^\xi`$, with $`C`$ depending only on $`d`$ | `CoarseDeGiorgi.integrated_slicing` | `IntegratedSlicing.lean` | proved |
| Lemma 5.4: the restriction is well defined for almost every radius | `CoarseDeGiorgi.fractional_slicing_ae_representative` | `FractionalSlicingAeRepresentative.lean` | proved |
| (5.8), `e.boundary.maxima`: the maxima $`A_k(\tau)`$ | `CoarseDeGiorgi.euclideanSetDistance`, `CoarseDeGiorgi.sampledUpperResponse` | `EuclideanSetDistance.lean`, `SampledUpperResponse.lean` | definition |
| (5.9), `e.boundary.maxima.series`: the series $`S(\tau)`$ | `CoarseDeGiorgi.sampledResponseSeries` | `SampledResponseSeries.lean` | definition |
| (5.10), `e.boundary.energy.maximal`: the maximal function $`D_v(\tau)`$ | `CoarseDeGiorgi.surfaceEnergyMaximal` | `SurfaceEnergyMaximal.lean` | definition |
| Lemma 5.5 (integrability in the radius), `l.radius.averages`: (5.11) | `CoarseDeGiorgi.Selection.source_response_sampling` | `CoarseDeGiorgi/Selection/SourceResponses.lean` | proved |
| Lemma 5.5: (5.12) | `CoarseDeGiorgi.Selection.centeredMaximal_weak_bound`, with `CoarseDeGiorgi.Selection.surfaceEnergyMeasure_univ` | `CoarseDeGiorgi/Selection/Maximal.lean`, `CoarseDeGiorgi/Selection/SurfaceEnergy.lean` | proved |
| proof of Lemma 5.5: the cubical coarea formula (5.13) | `CoarseDeGiorgi.Selection.cubical_coarea` | `CoarseDeGiorgi/Selection/CoareaPartition.lean` | proved |
| the truncations $`\min\{(v-k)_+,N\}`$ and their gradients (Proposition 5.6) | `CoarseDeGiorgi.positiveCap`, `CoarseDeGiorgi.positiveCapGradient` | `PositiveCap.lean`, `PositiveCapGradient.lean` | definition |
| Proposition 5.6 (existence of a good radius), `p.good.radius`, with (5.14)–(5.19) | `CoarseDeGiorgi.good_radius_exists` | `GoodRadiusExists.lean` | proved |

Lemma 5.1 is proved for $`1\lt\xi\lt\infty`$; the case $`\xi=1`$, which the paper
does not use, is not formalized. Proposition 5.3: the localized function
agrees with $`v`$ almost everywhere on an open neighborhood of every cube
boundary with radius in $`J`$, and the inner version near
$`\rho_1\overline{\square}_0`$, as in the paper. Lemma 5.4 is
stated for every $`0\lt\alpha\lt1\lt\xi\lt\infty`$ with one constant, chosen before
$`\alpha`$ and $`\xi`$, and its proof follows the paper (midpoint averaging and
the cubical coarea formula (5.13)). Lemma 5.5: the bound (5.11) is
proved for the $`L^{2p}`$ norm over all of $`\mathbb R`$, which is stronger;
(5.12) is obtained by combining the weak-type bound for the centered maximal
function with the total mass of the boundary energy. Proposition 5.6: the
approximations are smooth functions of finite energy, nonnegative on
$`\square_0`$; the trace of $`v`$ and of its truncations at the good radius is
the restriction of the given function, and (5.14) is stated for every
$`k\in\mathbb R`$ and $`0\lt N\le\infty`$. As in the paper, the truncations converge
in $`W^{1-t,r}(\partial(\tau\square_0))`$; convergence in
$`L^2(\partial(\tau\square_0))`$ follows from Lemma 5.1 where it is needed.

## Section 6: the piecewise harmonic extension

| Source | Lean declaration | File | Status |
|---|---|---|---|
| (6.1), `e.extension.width`: triadic widths $`h=3^{-n}`$ (the bound $`h\le(\rho_2-\tau)/(100d)`$ is a hypothesis of the statements of Section 6) | `CoarseDeGiorgi.IsTriadicWidth` | `IsTriadicWidth.lean` | definition |
| the projection $`y_x`$ and the cutoff $`\omega`$ | `CoarseDeGiorgi.seedProjection`, `CoarseDeGiorgi.seedCutoff` | `SeedProjection.lean`, `SeedCutoff.lean` | definition |
| (6.2), `e.extension.definition`: the patches $`\Sigma_z`$ and the values of $`L_hf`$ at the free vertices | `CoarseDeGiorgi.whitneyPatch`, `CoarseDeGiorgi.whitneyFreeValue` | `WhitneyPatch.lean`, `WhitneyFreeValue.lean` | definition |
| the piecewise affine extension $`L_hf`$ | `CoarseDeGiorgi.whitneyAffineExtension` | `WhitneyAffineExtensionDef.lean` | definition |
| $`\mathscr W_h`$ and $`\mathscr W_h^j`$ | `CoarseDeGiorgi.whitneySimplicesNear`, `CoarseDeGiorgi.whitneySimplicesNearSize` | `WhitneySimplicesNear.lean`, `WhitneySimplicesNearSize.lean` | definition |
| $`\mathrm{Lip}`$ for the Euclidean distance | `CoarseDeGiorgi.euclidLipConst` | `EuclidLipConst.lean` | definition |
| Proposition 6.1 (the piecewise affine extension), `p.affine.extension`, with (6.3) | `CoarseDeGiorgi.affine_extension` | `AffineExtension.lean` | proved |
| the piecewise harmonic extension $`H_hf`$ | `CoarseDeGiorgi.IsPiecewiseHarmonicExtension`, `CoarseDeGiorgi.exists_piecewiseHarmonicExtension` | `IsPiecewiseHarmonicExtension.lean`, `ExistsPiecewiseHarmonicExtension.lean` | definition |
| Proposition 6.2 (energy and admissibility of the piecewise harmonic extension), `p.whitney.extension`, with (6.6) | `CoarseDeGiorgi.harmonic_extension` | `HarmonicExtension.lean` | proved |

Proposition 6.1: (6.4), which the proof derives, appears in the statement as
the support assertion, closures in $`(\tau+3h)\overline{\square}_0\Subset\rho_2\square_0`$. Linearity, positivity and
the range bound are stated on the exterior, where $`L_hf`$ lives, and "a
Lipschitz extension of $`f`$" is a function that agrees with $`L_hf`$ there,
equals $`f`$ on $`\partial(\tau\square_0)`$ and has a finite Lipschitz constant on
$`\mathbb R^d\setminus\tau\square_0`$. The vertex estimate (6.5) is part of the
proof. Proposition 6.2:
$`H_hf`$ is given with its gradient, as a relation (`IsPiecewiseHarmonicExtension`)
that determines it almost everywhere on each simplex, and its existence is a
separate statement; the Sobolev trace $`f`$ on $`\partial(\tau\square_0)`$ is
stated as the Gauss–Green identity on $`\square_0\setminus\tau\overline{\square}_0`$.

## Section 7: energy in cubes with good radii

| Source | Lean declaration | File | Status |
|---|---|---|---|
| Lemma 7.1 (estimating the exterior integral), `l.exterior.integral`, with (7.1) and (7.2) | `CoarseDeGiorgi.exterior_integral_bound` | `ExteriorIntegralBound.lean` | proved |
| Proposition 7.2 (energy bound in a cube with a good radius), `p.good.radius.energy`, with (7.5) | `CoarseDeGiorgi.good_radius_energy_bound` | `GoodRadiusEnergyBound.lean` | proved |

Lemma 7.1 and Proposition 7.2 are stated for the widths
$`0\lt h\le\delta/(200d)`$, $`\delta=\rho_2-\rho_1`$, as in the paper. Proposition 7.2
takes "a good radius and the subsequence given by Proposition 5.6" as
hypotheses that list the conclusions of Proposition 5.6 it uses: the
convergence (5.14) in $`W^{1-t,r}(\partial(\tau\square_0))`$ for every $`k`$ and
$`0\lt N\le\infty`$, the bounds (5.15) and (5.16) with an explicit constant, and
$`D_w\le D_v`$ for every truncation. The convergence in
$`L^2(\partial(\tau\square_0))`$ is not a hypothesis; the proof obtains it from
Lemma 5.1, as the paper does.

## Section 8: Caccioppoli inequality and local boundedness

| Source | Lean declaration | File | Status |
|---|---|---|---|
| (8.1), `e.localization.exponents`: $`\gamma_1`$ and $`\gamma_2`$ | `CoarseDeGiorgi.gammaLoc`, `CoarseDeGiorgi.gammaCacc` | `GammaLoc.lean`, `GammaCacc.lean` | definition |
| Proposition 8.1 (Caccioppoli inequality), `p.cg.caccioppoli`, with (8.2) | `CoarseDeGiorgi.caccioppoli_inequality` | `CaccioppoliInequality.lean` | proved |
| (8.5), `e.two.level.quantity`: the quantity $`Y_a(\rho)`$ | `CoarseDeGiorgi.twoLevelQuantity` | `TwoLevelQuantity.lean` | definition |
| (8.6), `e.ordinary.fractional.sobolev`: the fractional Sobolev inequality in the bulk | `CoarseDeGiorgi.Assembly.hybrid_compact_embedding`, from `CoarseDeGiorgi.dnpv_theorem_6_5` (below) | `CoarseDeGiorgi/Assembly/HybridEmbedding.lean` | proved |
| (8.7), `e.recurrence.exponent`: $`\gamma_3`$ | `CoarseDeGiorgi.gammaRec` | `GammaRec.lean` | definition |
| Proposition 8.2 (a two-level recurrence), `p.two.level.recurrence`, with (8.8) | `CoarseDeGiorgi.two_level_recurrence` | `TwoLevelRecurrence.lean` | proved |
| before Proposition 8.3: $`\gamma_4`$ | `CoarseDeGiorgi.gammaSup` | `GammaSup.lean` | definition |
| Proposition 8.3 (from energy to supremum), `p.energy.to.sup`, with (8.10) | `CoarseDeGiorgi.energy_to_supremum` | `EnergyToSupremum.lean` | proved |
| proofs of Theorem A and Corollary B | `CoarseDeGiorgi.local_boundedness` (Section 1), from Propositions 8.1 and 8.3 | `LocalBoundedness.lean` | proved |

## Section 9: weak Harnack and Harnack inequalities

| Source | Lean declaration | File | Status |
|---|---|---|---|
| start of Section 9: $`\chi=r^*/r`$, and $`c_m=\lvert m\rvert/(1-2m)`$ (Section 9.1) | `CoarseDeGiorgi.chiParam`, `CoarseDeGiorgi.powerFactor` | `ChiParam.lean`, `PowerFactor.lean` | definition |
| start of Section 9: $`\gamma_5`$ and $`\gamma_6`$ | `CoarseDeGiorgi.gammaRev`, `CoarseDeGiorgi.gammaIter` (defined; Lemmas 9.3 and 9.4 are proved with larger powers of $`(\rho_2-\rho_1)^{-1}`$, see the note below) | `GammaRev.lean`, `GammaIter.lean` | definition |
| Section 9.1: the powers $`w^m`$ of supersolutions | see Lemma A.2 (iv) below | | |
| Proposition 9.1 (Caccioppoli inequality for powers), `p.power.caccioppoli`, with (9.1) | `CoarseDeGiorgi.power_caccioppoli_inequality` | `PowerCaccioppoliInequality.lean` | proved |
| Lemma 9.2 (logarithmic estimate), `l.log.estimate`, with (9.4) and (9.5) | `CoarseDeGiorgi.log_estimate` | `LogEstimate.lean` | proved |
| Lemma 9.3 (reverse Hölder inequalities for powers), `l.positive.negative.moments`, with (9.6) | `CoarseDeGiorgi.Harnack.Iterations.signed_moment_step_of_normalized_reverse`, `CoarseDeGiorgi.Harnack.ReverseMoments.signed_power_normalized_reverse_of_power_caccioppoli` | `CoarseDeGiorgi/Harnack/Iterations/SignedMomentStep.lean`, `CoarseDeGiorgi/Harnack/ReverseMoments/NormalizedReverse.lean` | partial |
| (9.7), `e.small.exponent`: the small exponent $`p_*=c/\sqrt\Theta`$ with $`c=\min\{r/4,1/(1+C_{(9.5)})\}`$ | `CoarseDeGiorgi.crossoverExponent` | `CrossoverExponent.lean` | definition |
| Lemma 9.4 (Moser iteration), `l.moment.iterations`, with (9.8)–(9.10) | `CoarseDeGiorgi.Harnack.Iterations.uniform_three_iterations_of_power_caccioppoli` | `CoarseDeGiorgi/Harnack/Iterations/UniformThreeIterations.lean` | partial |
| Lemma 9.5 (crossover estimate), `l.crossover`, with (9.12) | `CoarseDeGiorgi.crossover_estimate` | `CrossoverEstimate.lean` | proved |
| Section 9.4: proof of Theorem C for $`\eta=r/4`$, with (9.13), and of (1.11) | `CoarseDeGiorgi.weak_harnack` ((1.10) at $`\eta=r/4=q/(2(q+1))`$, the exponent `CoarseDeGiorgi.harnackEtaParam`), `CoarseDeGiorgi.harnack` (Section 1) | `WeakHarnack.lean`, `HarnackEtaParam.lean`, `Harnack.lean` | proved |
| Section 9.5 (endpoint weak Harnack inequality), `ss.harnack.endpoint`: Corollary B, (1.10) at $`\eta=r/4`$ and (1.11) on the cubes $`y+\square_{1-n}`$ by rescaling | `CoarseDeGiorgi.Endpoint.localWeakHarnackCubes_holds`, `CoarseDeGiorgi.Endpoint.localHarnackCubes_holds`, `CoarseDeGiorgi.Endpoint.remoteLocalBoundedness_holds` | `CoarseDeGiorgi/Endpoint/Rescaling/LocalCubes.lean`, `CoarseDeGiorgi/Endpoint/Rescaling/RemoteBound.lean` | proved |
| Section 9.5: chaining over the cubes $`y+\square_{-3}`$, $`y\in3^{-4}\mathbb Z^d`$ | `CoarseDeGiorgi.Endpoint.interior_weak_harnack_of_cubes`, `CoarseDeGiorgi.Endpoint.interior_harnack_of_cubes` | `CoarseDeGiorgi/Endpoint/Chaining/WeakHarnack.lean`, `CoarseDeGiorgi/Endpoint/Chaining/Harnack.lean` | proved |
| (9.14), `e.interior.weak.harnack`: the weak Harnack estimate at $`\eta=r/4`$ on $`\frac{15}{16}\square_0`$ | `CoarseDeGiorgi.interior_weak_harnack` | `InteriorWeakHarnack.lean` | proved |
| (9.15), `e.interior.harnack`: the Harnack estimate for nonnegative solutions in $`\frac34\square_0`$ | `CoarseDeGiorgi.interior_harnack` | `InteriorHarnack.lean` | proved |
| (9.16), `e.endpoint.scales`: the numbers $`b_k`$ and $`\sum_{k\ge1}b_k\le\lambda_{t,1,q}(\square_0)^{-1/2}/(1-3^{-t})`$ | $`b_k`$ is written out in `CoarseDeGiorgi.dirichlet_reconstruction`, as the term of index $`k`$ of the series of `lowerMoment`; the sum is bounded in the proof of Proposition 9.7 | `DirichletReconstruction.lean`, `CoarseDeGiorgi/Endpoint/Potential/` | proved |
| Lemma 9.6 (scale decomposition for functions with zero boundary values), `l.dirichlet.reconstruction`, with (9.17) | `CoarseDeGiorgi.dirichlet_reconstruction` | `DirichletReconstruction.lean` | proved |
| proof of Lemma 9.6, Step 1: the bound on $`P_k\nabla v`$ and (9.18) | `CoarseDeGiorgi.Endpoint.Reconstruction.fine_grid_spatial_holder` (on the simplices of $`\mathscr T_k`$; see the note below), `CoarseDeGiorgi.Endpoint.Reconstruction.fine_increment_weighted_norm_le` | `CoarseDeGiorgi/Endpoint/Reconstruction/FineCells.lean`, `CoarseDeGiorgi/Endpoint/Reconstruction/FineProjection.lean` | proved |
| proof of Lemma 9.6, Steps 1–3: the terms $`v_k`$ and their bounds in $`L^r`$ and $`L^\infty`$, (9.19)–(9.23) | a different argument, see the note below: `CoarseDeGiorgi.Endpoint.Reconstruction.exists_weighted_dirichlet_blocks`, from `CoarseDeGiorgi.Endpoint.Reconstruction.exists_fineIncrement_dirichlet_estimates`, `CoarseDeGiorgi.Endpoint.Reconstruction.exists_unitCube_dirichlet_cancellation_bound` and `CoarseDeGiorgi.Endpoint.Morrey.exists_cube_morrey_bound` | `CoarseDeGiorgi/Endpoint/Reconstruction/WeightedBlocks.lean`, `CoarseDeGiorgi/Endpoint/Reconstruction/BlockEstimates.lean`, `CoarseDeGiorgi/Endpoint/Reconstruction/DirichletDualBound.lean`, `CoarseDeGiorgi/Endpoint/Morrey/Cube.lean` | proved |
| proof of Lemma 9.6, Step 4: summation and the general $`v`$ | `CoarseDeGiorgi.Endpoint.Reconstruction.weighted_reconstruction_converges`, `CoarseDeGiorgi.Endpoint.Reconstruction.dirichlet_reconstruction_proof` | `CoarseDeGiorgi/Endpoint/Reconstruction/WeightedLimit.lean`, `CoarseDeGiorgi/Endpoint/Reconstruction/Main.lean` | proved |
| potentials of measures: the extension of $`\nu`$ to $`H^1_{\mathbf a,0}(\square_0)`$, (9.24), `e.measure.evaluation`, and the potential of $`\nu`$ | the defining equation of the potential is a hypothesis of `CoarseDeGiorgi.endpoint_potential`; existence: `CoarseDeGiorgi.Endpoint.exists_potential`; (9.24): `CoarseDeGiorgi.Endpoint.nonneg_pairing`, `CoarseDeGiorgi.Endpoint.Potential.pairing_le_of_potential` | `EndpointPotential.lean`, `CoarseDeGiorgi/Endpoint/Source/Potential.lean`, `CoarseDeGiorgi/Endpoint/Source/Extension.lean`, `CoarseDeGiorgi/Endpoint/Potential/Equation.lean` | proved |
| Proposition 9.7 (endpoint potential estimate), `p.endpoint.potential`, with (9.25) | `CoarseDeGiorgi.endpoint_potential` | `EndpointPotential.lean` | proved |
| proof of Proposition 9.7, (9.26)–(9.29) | `CoarseDeGiorgi.Endpoint.endpoint_potential_of_reconstruction`, from `CoarseDeGiorgi.Endpoint.Potential.truncation_energy_le` (the energy of the truncations), `CoarseDeGiorgi.Endpoint.Potential.core_bound` (the level sets) and `CoarseDeGiorgi.Endpoint.Potential.lintegral_rpow_le_tsum` (the layer-cake sum); a different summation, see the note below | `CoarseDeGiorgi/Endpoint/Potential/Main.lean`, `CoarseDeGiorgi/Endpoint/Potential/Equation.lean`, `CoarseDeGiorgi/Endpoint/Potential/Core.lean`, `CoarseDeGiorgi/Endpoint/Potential/LayerCake.lean` | proved |
| Lemma 9.8 (interior source measure estimate), `l.source.mass`, with (9.30), and its last sentence: the restriction $`\nu`$ of $`\mu`$ to $`\frac34\square_0`$ acts continuously on $`H^1_{\mathbf a,0}(\square_0)`$, and its potential $`V`$ satisfies $`0\le V\le u`$ and $`u-V\in\mathcal C_{\mathrm{sol}}(\frac34\square_0)`$ | `CoarseDeGiorgi.source_mass_potential` | `SourceMassPotential.lean` | proved |
| proof of Lemma 9.8, Steps 1 and 2: the measure $`\mu`$, its restriction $`\nu`$ to $`\frac34\square_0`$ with (9.31), the potential $`V`$ of $`\nu`$, $`0\le V\le u`$, and $`u-V\in\mathcal C_{\mathrm{sol}}(\frac34\square_0)`$ | `CoarseDeGiorgi.Endpoint.source_measure_exists`, `CoarseDeGiorgi.Endpoint.source_potential` (some steps by other arguments; see the note below) | `CoarseDeGiorgi/Endpoint/Source/Main.lean` | proved |
| proof of Lemma 9.8, Steps 3–6: Corollary B on the cube $`Q_1`$ and (9.32), the capacitary function and (9.33), (9.34), and the lower bound on $`\frac34\square_0`$ | `CoarseDeGiorgi.Endpoint.capacitary_remote_bound`, `CoarseDeGiorgi.Endpoint.remote_capacitary_exists`, `CoarseDeGiorgi.Endpoint.capacitary_test`, `CoarseDeGiorgi.Endpoint.capacitary_competitor_energy`, `CoarseDeGiorgi.Endpoint.capacitary_functional_lower`, `CoarseDeGiorgi.Endpoint.source_mass_of_interior` (some steps by other arguments; see the note below) | `CoarseDeGiorgi/Endpoint/Capacitary/` | proved |
| Section 9.5: completion of the proof of Theorem C, and smaller exponents by Hölder's inequality | `CoarseDeGiorgi.weak_harnack_range` (Section 1), from `CoarseDeGiorgi.Endpoint.weak_harnack_range_of_endpoint` | `WeakHarnackRange.lean`, `CoarseDeGiorgi/Endpoint/Completion/Main.lean` | proved |

The small exponent is $`p_*=c/\sqrt{1+\Theta}`$ in Lean, where the paper has
$`c/\sqrt\Theta`$; since $`\Theta\ge1`$ the two differ by at most the factor
$`\sqrt2`$ (`CoarseDeGiorgi.Harnack.Crossover.crossoverExponent_sqrt_le`). Lemma
9.5 is stated with this $`p_*`$ and with some $`0\lt c\le r/4`$ depending only on
$`d,p,q,s,t`$; the paper's choice $`c=\min\{r/4,1/(1+C_{(9.5)})\}`$ is made
inside the proof. The Lean form of Lemma 9.4 is stated for
$`0\lt c\le\min\{\frac12,r/(16\chi)\}`$; the proof of the weak Harnack inequality
at $`\eta=r/4`$ obtains Lemma 9.5 for such a $`c`$ from the statement above by
Hölder's inequality, since the crossover bound passes to smaller exponents.
Lemmas 9.3 and 9.4 are proved from a weaker form of Proposition 9.1, with the
larger power $`2\gamma_2'(1-t)/\theta`$ of $`(\rho_2-\rho_1)^{-1}`$, where
$`\gamma_2'=\max\{1-t,\frac d{2q}\}+1+\frac1{2p}+\frac1{2q}\ge\gamma_1`$, which
`CoarseDeGiorgi.power_caccioppoli_of_inequality`
(`CoarseDeGiorgi/PowerCacc/HarnackForm.lean`) derives from
`power_caccioppoli_inequality`. Their powers of $`(\rho_2-\rho_1)^{-1}`$ are
therefore larger than $`\gamma_5r`$ and $`\gamma_6`$; Lemma 9.3 is stated with
the exponent $`z=mr`$ in place of $`m`$, and Lemma 9.4 with an exponent that is
only asserted to exist. Theorem C, at fixed radii, does not depend on these
powers.

**Section 9.5.** The statements (9.14), (9.15), Lemma 9.6, Proposition 9.7
and Lemma 9.8 are formalized as stated, with the constant of Lemma 9.6
depending only on $`d,q`$ and that of Proposition 9.7 only on $`d,q,t`$; in both
the constant is chosen before $`p`$, $`s`$ and the coefficient field. In Lemma
9.6, $`v=\sum_{k\ge1}v_k`$ in $`L^r(\square_0)`$ means that the partial sums
converge to $`v`$ in $`L^r(\square_0)`$, and each $`v_k`$ is almost everywhere
strongly measurable with the two bounds (9.17). Proposition 9.7 applies to
every $`v\in H^1_{\mathbf a,0}(\square_0)`$ with
$`\int_{\square_0}\nabla\varphi\cdot\mathbf a\nabla v=\int\varphi\,d\nu`$ for all
$`\varphi\in C^\infty_c(\square_0)`$, which characterizes the potential of
$`\nu`$; the measure is a finite measure on $`\mathbb R^d`$ that vanishes outside
$`\square_0`$, and the continuity of its action is stated as a bound by the
energy. In Lemma 9.8 the nonnegative Radon measure $`\mu`$ on $`\square_0`$ is a
measure on $`\mathbb R^d`$ that vanishes outside $`\square_0`$ and is finite on
compact subsets of $`\square_0`$; its restriction $`\nu`$ to $`\frac34\square_0`$
is finite, the continuity of its action is stated as a bound by the energy,
in the form of the hypothesis of Proposition 9.7, and the potential $`V`$ is
an element of $`H^1_{\mathbf a,0}(\square_0)`$ satisfying its equation against
$`C^\infty_c(\square_0)`$. The completion of the proof of Theorem C applies
Proposition 9.7 to this $`V`$ and the Harnack estimate (9.15) to $`u-V`$, as in
the paper. The rescaling and chaining behind (9.14) and (9.15)
follow the paper, with two small changes: the centres of neighbouring cubes in
a chain may differ in several coordinates at once, and the chain for (9.15)
uses one more layer of cubes, which still lie in $`\frac34\square_0`$.

The proofs of Lemma 9.6, Proposition 9.7 and Lemma 9.8 differ from the paper
in the following places.
- **Lemma 9.6.** The paper writes each term $`v_k`$ as the Newtonian potential
  on $`\mathbb R^d`$ of the increment $`G_k=(P_k-P_{k-1})\nabla v`$ of the triadic
  averages of the gradient. It bounds $`v_k`$ in $`L^r`$ by duality with
  $`\Gamma*\phi`$, the cancellation of $`G_k`$ on cubes of side $`3^{1-k}`$ and the
  Calderón–Zygmund estimate on $`\mathbb R^d`$, and in $`L^\infty`$ by the size of
  the kernel. The formal proof takes for $`v_k`$ the solution in
  $`H^1_0(\square_0)`$ of the Dirichlet problem $`-\Delta v_k=-\nabla\cdot G_k`$, so
  that the terms have zero boundary values. The $`L^r`$ bound uses the same
  duality and cancellation, with the solution of the Poisson problem with zero
  boundary values on $`\square_0`$ in place of $`\Gamma*\phi`$ and the
  Calderón–Zygmund estimate for the Hessian on the cube from the
  `CoarseGraining` library. The $`L^\infty`$ bound is proved on each cube of side
  $`3^{-k}`$: the mean of $`v_k`$ on the cube is controlled by the $`L^r`$ bound,
  and its oscillation by Morrey's inequality with exponent $`2d`$ (proved here),
  the $`W^{1,2d}`$ estimate for the Dirichlet problem on $`\square_0`$
  (`CoarseGraining`) and the comparison of the $`L^{2d}`$ and $`L^r`$ norms of
  the piecewise constant field $`G_k`$. In Step 1 the bound on $`P_k\nabla v`$ is
  obtained simplex by simplex, each cube of side $`3^{-k}`$ being split by
  Jensen's inequality into its $`d!`$ simplices of $`\mathscr T_k`$, where the
  paper aggregates $`\mathbf a_{\ast}^{-1}`$ on the cubes. In Step 4 the partial
  sums for a smooth $`v`$ with compact support solve the Dirichlet problem with
  data $`P_N\nabla v`$ and converge to $`v`$ in $`L^2`$ by the energy estimate and
  Poincaré's inequality; for a general $`v`$ the terms are built from $`\nabla v`$
  directly, and the identification of the sum passes from smooth
  approximations to $`v`$ through convergence in measure. The statement is the
  same.
- **Proposition 9.7.** The paper proves $`v\ge0`$ and bounds the decreasing
  rearrangement of $`v`$ through the truncations $`v\wedge K`$. The formal proof
  does not use positivity: it works with the symmetric truncations
  $`\max\{-K,\min\{v,K\}\}`$, whose energy it bounds by $`2K\nu(\square_0)`$ in place
  of the $`K\nu(\square_0)`$ of (9.26), and it sums the distribution estimate
  (9.28) over the level sets $`\{\lvert v\rvert\gt K\}`$ with dyadic measures (a
  layer-cake argument) in place of the rearrangement. The continuity
  hypothesis on $`\nu`$ is not used: the equation of the potential already
  provides it.
- **Lemma 9.8.** In Step 1 the flux functional of $`u`$ is extended from smooth
  functions to $`C_c(\square_0)`$ by M. Riesz's extension theorem for positive
  functionals in place of uniform approximation, and the bound of
  $`\int\lvert\phi\rvert\,d\mu`$ by the energies is proved without the identity
  $`\int\lvert\phi\rvert\,d\mu=\int\nabla\lvert\phi\rvert\cdot\mathbf a\nabla u`$. The
  potential $`V`$ of $`\nu`$ is obtained from the Riesz representation theorem in
  $`H^1_{\mathbf a,0}(\square_0)`$ with the energy inner product ($`\mathbf a`$ is
  symmetric) in place of the Lax–Milgram lemma. In Step 4 the capacitary
  function is the admissible function of least energy cut off at $`0`$ and $`1`$;
  the cut-off function is again admissible, with no larger energy, so the
  uniqueness of the minimizer is not used. In Step 5 the piecewise affine
  function $`f`$ is a sum of nodal functions of $`\mathscr T_4`$ at the vertices
  within maximum-norm distance $`2\cdot3^{-4}`$ of $`y_0`$. Step 6 uses cutoffs
  equal to one on compact subsets of $`\frac34\square_0`$ and the inner
  regularity of $`\nu`$ in place of an increasing sequence of cutoffs and
  monotone convergence.

The completion of the proof of Theorem C treats every exponent $`r^*/2`$ at
once, with the quasi-triangle inequality of $`L^{r^*/2}`$, where the paper
distinguishes $`r^*/2\ge1`$ and $`r^*/2\lt1`$.

## Section 10: proofs of Theorem D and Corollary E

| Source | Lean declaration | File | Status |
|---|---|---|---|
| proof of Theorem D (i) | `CoarseDeGiorgi.moment_bounds_lebesgue` (Section 1), from `CoarseDeGiorgi.CoefficientConditions.moment_bounds_lebesgue_aux` | `MomentBoundsLebesgue.lean`, `CoarseDeGiorgi/CoefficientConditions/Lebesgue.lean` | proved |
| after the proof: the constant one is attained for constant matrices | — | — | not formalized |
| proof of Theorem D (ii): $`(\mathbf a)_\triangle\le d!\,(\mathbf a)_Q`$, and the means over simplices against the means over cubes | `CoarseDeGiorgi.CoefficientConditions.quadratic_average_le`, `CoarseDeGiorgi.CoefficientConditions.norm_average_le`, `CoarseDeGiorgi.CoefficientConditions.simplexSum_le`, `CoarseDeGiorgi.CoefficientConditions.upper_le`, `CoarseDeGiorgi.CoefficientConditions.lower_le`; `CoarseDeGiorgi.moment_bounds_besov` (Section 1) | `CoarseDeGiorgi/CoefficientConditions/BesovMatrix.lean`, `CoarseDeGiorgi/CoefficientConditions/BesovLevel.lean`, `CoarseDeGiorgi/CoefficientConditions/BesovSeries.lean`, `MomentBoundsBesov.lean` | proved |
| proof of Theorem D (iii): Lemma B.2 for $`\mathbf a`$ and for $`\mathbf a^{-1}`$, then part (ii) | `CoarseDeGiorgi.moment_bounds_sobolev` (Section 1), from `CoarseDeGiorgi.NegSobolev.moment_bounds_sobolev_of_negative_sobolev_bound` applied to `CoarseDeGiorgi.negative_sobolev_bound` | `MomentBoundsSobolev.lean`, `CoarseDeGiorgi/NegSobolev/MomentBoundsSobolev.lean` | proved |
| proof of Corollary E: part (iii) with $`s=\frac\alpha2+\frac\theta4`$, $`t=\frac\beta2+\frac\theta4`$, $`\varepsilon=\frac\theta2`$, then Theorems A and C with the slack $`\frac\theta2`$ | `CoarseDeGiorgi.local_boundedness_sobolev`, `CoarseDeGiorgi.harnack_sobolev` (Section 1), from `CoarseDeGiorgi.NegSobolev.local_boundedness_sobolev_of_moment_bounds` and `CoarseDeGiorgi.NegSobolev.harnack_sobolev_of_moment_bounds` applied to `CoarseDeGiorgi.moment_bounds_sobolev` | `LocalBoundednessSobolev.lean`, `HarnackSobolev.lean`, `CoarseDeGiorgi/NegSobolev/CorollarySobolev.lean` | proved |
| comparison with Bella and Schäffner | — | — | not formalized |

## Section 11: sharpness

The constructions are in
[`CoarseDeGiorgi/SharpnessExamples/`](CoarseDeGiorgi/SharpnessExamples/). The
cylinders of Theorem F are indexed from $`0`$ in Lean, so the Lean index $`n`$
is the paper's $`j=n+1`$.

| Source | Lean declaration | File | Status |
|---|---|---|---|
| the cylinder $`E_{\varepsilon,y_0}`$ and the fractions $`f_\triangle`$ (Lemma 11.1), and the profile $`\varepsilon^{d-1}\max\{\varepsilon,3^{-k}\}^{-(d-1)(1-1/p)}`$ of (11.1) | `CoarseDeGiorgi.SharpnessExamples.averagesCylinder`, `CoarseDeGiorgi.SharpnessExamples.cylinderFraction`, `CoarseDeGiorgi.SharpnessExamples.cylinderPhi`, `CoarseDeGiorgi.SharpnessExamples.simplexCell_cylinderFraction_eq_source` | `CoarseDeGiorgi/SharpnessExamples/CylinderAveragesDefs.lean` | definition |
| Lemma 11.1 (averages of cylinders over simplices), `l.sharpness.cylinder.averages`: (11.1) | `CoarseDeGiorgi.SharpnessExamples.cylinderFraction_level_moment_upper` | `CoarseDeGiorgi/SharpnessExamples/CylinderAveragesMoments.lean` | partial |
| Lemma 11.1: (11.2) | `CoarseDeGiorgi.SharpnessExamples.cylinderFractionDiscountedRoot_sum`, from `CoarseDeGiorgi.SharpnessExamples.discountedRoot_sum` | `CoarseDeGiorgi/SharpnessExamples/BesovCylinderSum.lean`, `CoarseDeGiorgi/SharpnessExamples/BesovGeometricSum.lean` | partial |
| Lemma 11.1: the same bounds for triadic cubes | `CoarseDeGiorgi.SharpnessExamples.cubePowerMean_le_simplex`, `CoarseDeGiorgi.SharpnessExamples.besovCubeTerm_le` (cube means bounded by simplex means) | `CoarseDeGiorgi/SharpnessExamples/BesovCubeSimplex.lean`, `CoarseDeGiorgi/SharpnessExamples/BesovNorms.lean` | partial |
| proof of Lemma 11.1: total mass and the bound on the fractions | `CoarseDeGiorgi.SharpnessExamples.cylinderFraction_level_sum`, `CoarseDeGiorgi.SharpnessExamples.averagesCylinder_volume_bounds`, `CoarseDeGiorgi.SharpnessExamples.cylinderSimplex_fraction_bounds` | `CoarseDeGiorgi/SharpnessExamples/CylinderAveragesDefs.lean`, `CoarseDeGiorgi/SharpnessExamples/CylinderAveragesGeometry.lean` | proved |
| Section 11.2 (the coefficient range), `ss.sharpness.range`, proof of Theorem F, Step 1: the power $`\kappa`$ with (11.3) | `CoarseDeGiorgi.SharpnessExamples.exists_cylinderExponent` | `CoarseDeGiorgi/SharpnessExamples/Parameters.lean` | proved |
| Step 1: $`b_j`$, the centres $`y_j`$, the radii and the disjointness of the cylinders | `CoarseDeGiorgi.SharpnessExamples.cylinderB`, `CoarseDeGiorgi.SharpnessExamples.cylinderCenter`, `CoarseDeGiorgi.SharpnessExamples.cylinderRadius`, `CoarseDeGiorgi.SharpnessExamples.cylinderRadius_data`, `CoarseDeGiorgi.SharpnessExamples.outerCylinder_pairwise_disjoint` | `CoarseDeGiorgi/SharpnessExamples/Parameters.lean` | proved |
| Step 1: the profile (11.4) and the subsolution (11.5) of one cylinder | `CoarseDeGiorgi.SharpnessExamples.scalarRadialProfile`, `CoarseDeGiorgi.SharpnessExamples.scalarAxialProfile`, `CoarseDeGiorgi.SharpnessExamples.scalarCylinderSubsolution` (a different profile; see the note below) | `CoarseDeGiorgi/SharpnessExamples/ScalarProfile.lean` | definition |
| Step 1: (11.6), `e.sharpness.scalar.field`: the field $`a(y)I`$ | `CoarseDeGiorgi.SharpnessExamples.scalarSharpnessWeight`, `CoarseDeGiorgi.SharpnessExamples.scalarSharpnessCoefficient` | `CoarseDeGiorgi/SharpnessExamples/ScalarCoefficient.lean` | definition |
| Step 2: each $`v_j`$ is a weighted subsolution; matching of the radial fluxes | `CoarseDeGiorgi.SharpnessExamples.scalarCylinderSubsolution_isWeightedSubsolution`, `CoarseDeGiorgi.SharpnessExamples.scalarProfile_inner_flux_match`, `CoarseDeGiorgi.SharpnessExamples.scalarCutoffFlux_divergence_nonneg` | `CoarseDeGiorgi/SharpnessExamples/ScalarCylinderSubsolution.lean`, `CoarseDeGiorgi/SharpnessExamples/ScalarProfileCalculus.lean`, `CoarseDeGiorgi/SharpnessExamples/ScalarFluxSign.lean` | proved |
| Step 2: the energy bound (11.7) | `CoarseDeGiorgi.SharpnessExamples.scalarProfile_energy_scaling_bound`, `CoarseDeGiorgi.SharpnessExamples.scalarCylinder_energy_band_majorant`, `CoarseDeGiorgi.SharpnessExamples.scalarCylinder_value_energy_bound` | `CoarseDeGiorgi/SharpnessExamples/ScalarEnergyScaling.lean`, `CoarseDeGiorgi/SharpnessExamples/ScalarEnergyPointwise.lean`, `CoarseDeGiorgi/SharpnessExamples/ScalarEnergyIntegral.lean` | proved |
| Step 3: the radii (11.8), the majorants (11.9) and $`\mathrm{tr}\mathbf a,\mathrm{tr}\mathbf a^{-1}\in L^1(\square_0)`$ | `CoarseDeGiorgi.SharpnessExamples.cylinderRadius`, `CoarseDeGiorgi.SharpnessExamples.scalarSharpnessWeight_majorant`, `CoarseDeGiorgi.SharpnessExamples.scalarInvSharpnessWeight_majorant`, `CoarseDeGiorgi.SharpnessExamples.scalarSharpnessWeight_integrable`, `CoarseDeGiorgi.SharpnessExamples.scalarSharpnessCoefficient_isWeightedCoeffOn` | `CoarseDeGiorgi/SharpnessExamples/Parameters.lean`, `CoarseDeGiorgi/SharpnessExamples/ScalarMajorants.lean`, `CoarseDeGiorgi/SharpnessExamples/ScalarIntegrability.lean` | proved |
| Step 3: the quasi-norm bounds (11.10) and (11.11) | `CoarseDeGiorgi.SharpnessExamples.scalarSharpnessWeight_besov`, `CoarseDeGiorgi.SharpnessExamples.scalarSharpnessWeight_inv_besov`, from `CoarseDeGiorgi.SharpnessExamples.majorant_besov_lt_top`, `CoarseDeGiorgi.SharpnessExamples.simplexMean_le_one_add_series`, `CoarseDeGiorgi.SharpnessExamples.sqrt_tsum_le_tsum_sqrt` | `CoarseDeGiorgi/SharpnessExamples/BesovScalarField.lean`, `CoarseDeGiorgi/SharpnessExamples/BesovSeries.lean` | proved |
| Step 3: the Lebesgue norms when $`\alpha=0`$ or $`\beta=0`$ | `CoarseDeGiorgi.SharpnessExamples.majorant_lp_lt_top`, `CoarseDeGiorgi.SharpnessExamples.eLpNorm_tsum_le_tsum` | `CoarseDeGiorgi/SharpnessExamples/BesovLebesgue.lean` | proved |
| Step 4: $`v_j\in H^1_{\mathbf a}(\square_0)`$, convergence of $`\sum_jv_j`$, and $`v\in\mathcal C_{\mathrm{sub}}(\square_0)`$ | `CoarseDeGiorgi.SharpnessExamples.scalarCylinderSubsolution_memH1a`, `CoarseDeGiorgi.SharpnessExamples.scalarSubsolutionSum`, `CoarseDeGiorgi.SharpnessExamples.scalarSubsolutionSum_memH1a`, `CoarseDeGiorgi.SharpnessExamples.scalarSubsolutionSum_isWeightedSubsolution` | `CoarseDeGiorgi/SharpnessExamples/ScalarMembership.lean`, `CoarseDeGiorgi/SharpnessExamples/ScalarLargeSets.lean`, `CoarseDeGiorgi/SharpnessExamples/ScalarSumMembership.lean`, `CoarseDeGiorgi/SharpnessExamples/ScalarSumSubsolution.lean` | proved |
| Step 4: harmonic replacement, $`u=1+H_{\square_0}v\ge1+v`$ | `CoarseDeGiorgi.SharpnessExamples.subsolution_le_harmonic_replacement`, `CoarseDeGiorgi.SharpnessExamples.harmonic_replacement_one_plus_dominates` | `CoarseDeGiorgi/SharpnessExamples/HarmonicComparison.lean`, `CoarseDeGiorgi/SharpnessExamples/NearAxisReplacement.lean` | proved |
| Step 4: unboundedness near every point of the segment and in $`\frac12\square_0`$, and (1.20) | `CoarseDeGiorgi.SharpnessExamples.scalarSubsolutionSum_large_near_line`, `CoarseDeGiorgi.SharpnessExamples.solution_unbounded_near_axis`, `CoarseDeGiorgi.SharpnessExamples.scalarSubsolutionSum_large_sets` | `CoarseDeGiorgi/SharpnessExamples/NearAxis.lean`, `CoarseDeGiorgi/SharpnessExamples/ScalarLargeSets.lean` | proved |
| proof of Theorem F: assembly | `CoarseDeGiorgi.SharpnessExamples.sharpness_besov_proved`; `CoarseDeGiorgi.sharpness` (Section 1) | `CoarseDeGiorgi/SharpnessExamples/BesovSharpness.lean`, `Sharpness.lean` | proved |
| after the proof: relation to the examples of Bella and Schäffner | — | — | not formalized |
| Section 11.3 (the polynomial bound), `ss.sharpness.polynomial`: Proposition 11.2 (sharpness of the polynomial bound), `p.sharpness.polynomial`, with (11.12)–(11.15) | `CoarseDeGiorgi.optimal_powers` | `OptimalPowers.lean` | proved |
| after Proposition 11.2: the powers in (1.8) and (1.9) are optimal; what is not claimed | — (the consequence is the last assertion of `CoarseDeGiorgi.optimal_powers`) | — | not formalized |
| proof of Proposition 11.2, Step 1: the field (11.16), its uniform ellipticity and (11.12) | `CoarseDeGiorgi.SharpnessExamples.polynomialPerpendicular`, `CoarseDeGiorgi.SharpnessExamples.polynomialParallel`, `CoarseDeGiorgi.SharpnessExamples.polynomialCoefficientFamily`, `CoarseDeGiorgi.SharpnessExamples.polynomialCoefficientFamily_ellipticity`, `CoarseDeGiorgi.SharpnessExamples.polynomialCoefficientFamily_trace_integral_bound` | `CoarseDeGiorgi/SharpnessExamples/PolynomialDefs.lean`, `CoarseDeGiorgi/SharpnessExamples/PolynomialEllipticity.lean`, `CoarseDeGiorgi/SharpnessExamples/PolynomialTraces.lean` | proved |
| Step 1: the profile (11.17), $`u_\varepsilon\in\mathcal C_{\mathrm{sol}}(\square_0)`$ and $`(u_\varepsilon)_+\in\mathcal C_{\mathrm{sub}}(\square_0)`$ | `CoarseDeGiorgi.SharpnessExamples.polynomialProfile`, `CoarseDeGiorgi.SharpnessExamples.polynomialSolution`, `CoarseDeGiorgi.SharpnessExamples.polynomialSolution_isWeightedSolution`; `CoarseDeGiorgi.Weighted.IsWeightedSubsolution.posPart` | `CoarseDeGiorgi/SharpnessExamples/PolynomialDefs.lean`, `CoarseDeGiorgi/SharpnessExamples/PolynomialEquationWeak.lean`, `CoarseDeGiorgi/Weighted/TestingTruncation.lean` | proved |
| Step 2: the positive part (11.18) and (11.14) | `CoarseDeGiorgi.SharpnessExamples.polynomialPositivePart_eq_inner`, `CoarseDeGiorgi.SharpnessExamples.polynomialPositivePart_height_of_solution`, `CoarseDeGiorgi.SharpnessExamples.polynomialPositivePart_Lp_asymptotic_of_solution` | `CoarseDeGiorgi/SharpnessExamples/PolynomialPositivePart.lean`, `CoarseDeGiorgi/SharpnessExamples/PolynomialNormExports.lean` | proved |
| Step 3: upper bounds for the coarse ellipticity constants, from coefficient averages and (11.2) | `CoarseDeGiorgi.SharpnessExamples.optimalPowers_upper_bounds`, from `CoarseDeGiorgi.SharpnessExamples.optimalPowers_upperMoment_cylinder_le`, `CoarseDeGiorgi.SharpnessExamples.optimalPowers_lowerMoment_inv_cylinder_le`, `CoarseDeGiorgi.SharpnessExamples.optimalPowers_upper_level`, `CoarseDeGiorgi.SharpnessExamples.optimalPowers_lower_level`, `CoarseDeGiorgi.SharpnessExamples.optimalPowers_series_bound` | `CoarseDeGiorgi/SharpnessExamples/OptimalPowersMoments.lean`, `CoarseDeGiorgi/SharpnessExamples/OptimalPowersUpper.lean`, `CoarseDeGiorgi/SharpnessExamples/OptimalPowersCells.lean`, `CoarseDeGiorgi/SharpnessExamples/OptimalPowersSeries.lean` | proved |
| Step 3: lower bounds (11.13) from Theorem A applied to $`u_\varepsilon`$ | `CoarseDeGiorgi.SharpnessExamples.optimalPowers_theoremA_inequality` (Theorem A, `CoarseDeGiorgi.local_boundedness`, with $`\eta=2`$, $`\rho_1=\frac12`$, $`\rho_2=\frac34`$), `CoarseDeGiorgi.SharpnessExamples.optimalPowers_solve_for_contrast`, `CoarseDeGiorgi.SharpnessExamples.optimalPowers_combine` | `CoarseDeGiorgi/SharpnessExamples/OptimalPowersLower.lean`, `CoarseDeGiorgi/SharpnessExamples/OptimalPowersCombine.lean` | proved |
| Step 3: the ratio (11.15); assembly | `CoarseDeGiorgi.SharpnessExamples.optimalPowers_rpow_le`, `CoarseDeGiorgi.SharpnessExamples.optimalPowers_ratio_tendsto_top`, `CoarseDeGiorgi.SharpnessExamples.optimal_powers_proved` | `CoarseDeGiorgi/SharpnessExamples/OptimalPowersFailure.lean`, `CoarseDeGiorgi/SharpnessExamples/OptimalPowersFinal.lean` | proved |
| Section 11.4 (the exponent of the weak Harnack inequality), `ss.sharpness.weak.harnack`: $`\eta_c=r^*/2=d/(d-2+2t+d/q)`$ | written as `rStarParam q t / 2` in `CoarseDeGiorgi.weak_harnack_sharpness` | `WeakHarnackSharpness.lean` | definition |
| Proposition 11.3 (sharpness of the weak Harnack exponent), `p.sharpness.weak.harnack`, with (11.19) | `CoarseDeGiorgi.weak_harnack_sharpness` | `WeakHarnackSharpness.lean` | proved |
| after Proposition 11.3: the range of Theorem C is optimal for each fixed $`d,p,q,s,t`$ | — (the consequence is the last assertion of `CoarseDeGiorgi.weak_harnack_sharpness`, with the field and the supersolutions chosen before $`\eta`$) | — | not formalized |
| proof of Proposition 11.3, Step 1: $`\beta=2t+d/q`$, (11.20), the field $`a(\varrho)=\varrho^\beta\log^3(eR/\varrho)`$ and $`\Lambda_{s,1,p}(\square_0)\lt\infty`$ | `CoarseDeGiorgi.SharpnessExamples.whBeta`, `CoarseDeGiorgi.SharpnessExamples.whField`, `CoarseDeGiorgi.SharpnessExamples.whCoeff_weightedCoeffOn`, `CoarseDeGiorgi.SharpnessExamples.whUpperMoment_lt_top` | `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessField.lean`, `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessMoments.lean`, `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessUpper.lean` | proved |
| Step 2: (11.21), (11.22) and $`\lambda_{t,1,q}(\square_0)\gt0`$ | `CoarseDeGiorgi.SharpnessExamples.whLower_level_le`, `CoarseDeGiorgi.SharpnessExamples.whLowerMoment_pos` | `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessLower.lean`, `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessLowerMoment.lean` | proved |
| Step 3: the supersolutions $`u_\varepsilon`$ and their source (11.23) | `CoarseDeGiorgi.SharpnessExamples.whu`, `CoarseDeGiorgi.SharpnessExamples.whFlux_identity`, `CoarseDeGiorgi.SharpnessExamples.whH_div_nonneg`, `CoarseDeGiorgi.SharpnessExamples.whu_isWeightedSupersolution` (different supersolutions; see the note below) | `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessGradient.lean`, `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessProfile.lean`, `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessSupersolution.lean` | proved |
| Step 4: the infimum, the asymptotics (11.24) and the blow-up of the moments | `CoarseDeGiorgi.SharpnessExamples.whEssInf`, `CoarseDeGiorgi.SharpnessExamples.whU_lower`, `CoarseDeGiorgi.SharpnessExamples.whRatio_tendsto`, `CoarseDeGiorgi.SharpnessExamples.weakHarnackSharpness_proved` | `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessInfimum.lean`, `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessCore.lean`, `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessRatio.lean`, `CoarseDeGiorgi/SharpnessExamples/WeakHarnackSharpnessFinal.lean` | proved |
| after the proof: the case $`\eta=\eta_c`$ | — | — | not formalized |

**Lemma 11.1** is formalized with explicit constants, for
$`0\lt\varepsilon\lt\frac14`$ and centres $`y_0`$ with all coordinates in
$`[-\frac14,\frac14]`$, which covers every cylinder of the two constructions;
the paper allows $`0\lt\varepsilon\lt1`$ and every $`y_0\in\mathbb R^{d-1}`$. The
version for cubes is used in the form "the mean of $`f^p`$ over the triadic
cubes of side $`3^{-k}`$ is at most the mean over $`\mathscr T_k`$", which
holds for nonnegative functions by Jensen's inequality, since each cube is the
union of $`d!`$ simplices of equal volume.

**Theorem F.** The Lean proof uses the same cylinders as the paper: the same
$`b_j=2^{-j-2}`$ and centres $`y_j=(b_j,0,\dots,0)`$, an inner conductivity
$`b_j\varrho_j^{-\kappa}`$ and an annular conductivity
$`b_j^{-1}\varrho_j^{2-\kappa}`$, the same majorants (11.9), the same
quasi-norm bounds through (11.2) (for simplices, combined with the comparison
of cube means and simplex means), Minkowski's inequality and square-root
subadditivity, and the same harmonic replacement. It differs from the paper
in three places.
- **The power $`\kappa`$.** The paper sets
  $`\kappa=(1-\theta_0)^{-1}(\frac{d-1}p+\alpha)`$; Lean chooses some
  $`\kappa\in(0,2)`$ satisfying (11.3), which exists exactly when
  $`\theta_0\le0`$.
- **The subsolution in one cylinder.** The paper uses
  $`v_j=j\exp(\frac{d-1}{b_j}(x_1+\frac12))\psi_j`$, with the profile (11.4),
  quadratic in the inner cylinder and equal to $`(2-\varrho/\varrho_j)^{d-1}`$
  in the annulus, so that no flux jump occurs at the outer radius. Lean uses
  a different subsolution: the axial factor is a multiple of
  $`\cosh(\mathfrak c_jx_1)`$ with
  $`\mathfrak c_j=\sqrt{(d-1)c_d}/b_j`$, where $`c_d`$ normalizes the radially
  harmonic profile of the annulus; the radial profile is quadratic in the
  inner cylinder and radially harmonic in the annulus, and the radial fluxes
  match at the inner radius. The outer radius then carries a nonnegative
  flux jump, which is not formalized as a surface measure: the flux is
  multiplied by a Lipschitz cutoff of small width at the outer radius, the
  divergence of the product is shown to be nonnegative, and the width is
  sent to zero. Both profiles have the properties the proof uses: they give
  nonnegative subsolutions whose axial growth rate does not depend on the
  radius, at least $`j`$ on the inner cylinder for the paper's profile and at
  least $`j/2`$ for the Lean profile.
- **The sum of the subsolutions.** The paper sums the norms of the $`v_j`$ in
  $`H^1_{\mathbf a}(\square_0)`$. Lean chooses the radii so that the energies
  are summable, takes the pointwise sum, proves that it lies in
  $`H^1_{\mathbf a}(\square_0)`$, and passes the subsolution inequality for
  every smooth test function to the limit by dominated convergence. The
  energy identity behind (11.7) is replaced by pointwise bounds on bands of
  the annulus times their volumes.

The unboundedness near every point of the segment is proved as in the paper:
every neighborhood of such a point contains a positive-measure part of the
inner cylinders of all large $`j`$, on which $`u\ge1+v`$ is large.

**Proposition 11.2.** The field, the solution and the proof follow the paper: the
upper bounds for $`\Lambda_\varepsilon`$ and $`\lambda_\varepsilon^{-1}`$ come from
averages of the coefficients over the simplices of $`\mathscr T_k`$ and the summed
cylinder bound (11.2), and the lower bounds from Theorem A applied to
$`u_\varepsilon`$ (with $`\eta=2`$, $`\rho_1=\frac12`$, $`\rho_2=\frac34`$). The ratio
(11.15) is proved directly in the form with $`\Theta_\varepsilon^\upsilon`$, for every
real $`\upsilon`$.

**Proposition 11.3.** The statement asserts the existence of a profile
$`a:\mathbb R\to\mathbb R`$ with the field $`a(\lvert x\rvert)I`$, $`\lvert x\rvert`$ the
Euclidean norm, and of families $`u_\varepsilon`$, $`G_\varepsilon`$ indexed by every
real $`\varepsilon`$, with the properties asserted for $`0\lt\varepsilon\lt\frac18`$:
a common essential infimum $`m\gt0`$ on $`\frac12\square_0`$, and, for every
$`\eta\gt r^*/2`$, the limit (11.19) in `ℝ≥0∞` as $`\varepsilon\to0^+`$. The proof
uses the paper's field, with $`\lvert a\rvert`$ in place of $`a`$, which changes
nothing for $`0\lt\varrho\le R=\sqrt d`$, and the value $`0`$ in place of $`I`$ at
the origin, a null set. It differs from the paper in three places.
- **The supersolutions.** The paper takes $`u_\varepsilon=G(\max\{\lvert x\rvert,\varepsilon\})`$,
  the fundamental solution made constant on $`B(0,\varepsilon)`$, whose source is
  a multiple of the surface measure on $`\partial B(0,\varepsilon)`$. Lean takes
  smooth functions $`U_\varepsilon(\lvert x\rvert^2)`$ whose source is a smooth
  nonnegative function supported in $`\varepsilon\le\lvert x\rvert\le2\varepsilon`$, with
  the same total mass; for $`\lvert x\rvert\ge2\varepsilon`$ they equal
  $`G(\lvert x\rvert)-G(R/\sqrt2)`$. The infimum on $`\frac12\square_0`$ is therefore
  $`G(R/4)-G(R/\sqrt2)\gt0`$ in place of $`G(R/4)`$; it does not depend on
  $`\varepsilon`$ either.
- **The asymptotics.** In place of (11.24), the lower bound for $`u_\varepsilon`$ on
  $`B(0,2\varepsilon)`$ uses an elementary bound for the logarithm, which costs a
  small power of $`\varepsilon`$; it is absorbed because $`\eta\gt r^*/2`$ is fixed
  before $`\varepsilon\to0`$.
- **The lower constant.** Near the origin, the averages of $`a^{-1}`$ over the
  simplices of $`\mathscr T_k`$ are bounded through the number $`d!\,3^{kd}`$ of
  simplices of $`\mathscr T_k`$ rather than through the count (3.5); away from
  the origin the proof uses Jensen's inequality, as the paper does.

## Appendices

| Source | Lean declaration | File | Status |
|---|---|---|---|
| Proposition A.1 (weighted calculus and approximation), `p.weighted.calculus`, (i): embedding in $`W^{1,1}`$, $`\mathbf a\nabla u\in L^1`$; Hilbert structure | `CoarseDeGiorgi.Weighted.memH1a_memW11`; `CoarseDeGiorgi.Weighted.weightedHilbert_complete`, `CoarseDeGiorgi.Weighted.zeroHilbert_complete` | `CoarseDeGiorgi/Weighted/Identification.lean`; `CoarseDeGiorgi/Weighted/SmoothSpace.lean`, `CoarseDeGiorgi/Weighted/ZeroSpace.lean` | partial |
| Proposition A.1 (ii): the coercivity bound (A.1) and $`\int_U\nabla\varphi=0`$ | `CoarseDeGiorgi.Weighted.exists_memH1a0_coercivity` | `CoarseDeGiorgi/Weighted/ZeroBoundary.lean` | partial |
| Proposition A.1 (iii): restriction and zero extension | `CoarseDeGiorgi.LowerFractional.memH1a_restrict`, `CoarseDeGiorgi.Whitney.lift_zero_extension` | `CoarseDeGiorgi/LowerFractional/Restriction.lean`, `CoarseDeGiorgi/Whitney/LiftZeroExtension.lean` | partial |
| Proposition A.1 (iv): chain rule, locality (A.8), positive parts and truncations (A.2) | `CoarseDeGiorgi.Weighted.MemH1a.comp`, `CoarseDeGiorgi.Weighted.MemH1a.gradient_zero_on_level`, `CoarseDeGiorgi.Weighted.MemH1a.max_sub_const`, `CoarseDeGiorgi.Weighted.MemH1a.truncation` | `CoarseDeGiorgi/Weighted/Truncation/Chain.lean`, `CoarseDeGiorgi/Weighted/Truncation/Energy.lean`, `CoarseDeGiorgi/Weighted/Truncation/PositivePart.lean`, `CoarseDeGiorgi/Weighted/Truncation/Truncate.lean` | partial |
| the gradient $`\mathbf 1_{\{u\gt c\}}\nabla u`$ of $`(u-c)_+`$, as in (A.2) | `CoarseDeGiorgi.positiveTruncationGradient` | `PositiveTruncationGradient.lean` | definition |
| Proposition A.1 (v): smooth, nonnegative and bounded approximations | `CoarseDeGiorgi.Weighted.MemH1a.smoothGraph_tendsto`, `CoarseDeGiorgi.Weighted.MemH1a0.nonnegative_approximation`, `CoarseDeGiorgi.Weighted.MemH1a0.comp_approximation` | `CoarseDeGiorgi/Weighted/GraphRepresentation.lean`, `CoarseDeGiorgi/Weighted/TestingNonnegative.lean`, `CoarseDeGiorgi/Weighted/TestingApproximation.lean` | partial |
| Proposition A.1 (vi): Lipschitz functions and products (A.3) | `CoarseDeGiorgi.Weighted.memH1a_of_lipschitzOn`, `CoarseDeGiorgi.Weighted.MemH1a.cutoff_comp`, `CoarseDeGiorgi.Harnack.Calculus.MemH1a.mul_bounded` | `CoarseDeGiorgi/Weighted/Lipschitz.lean`, `CoarseDeGiorgi/Weighted/TestingProducts.lean`, `CoarseDeGiorgi/Harnack/Calculus/BoundedAlgebra.lean` | partial |
| after the proof of Proposition A.1: comparison with the space of the earlier homogenization paper | — | — | not formalized |
| Lemma A.2 (admissible tests, truncations and powers), `l.weighted.testing`, (i)–(iii), with (A.9) | `CoarseDeGiorgi.Weighted.IsWeightedSubsolution.testing`, `CoarseDeGiorgi.Weighted.MemH1a.memH1a0_of_compact_support`, `CoarseDeGiorgi.Weighted.IsWeightedSubsolution.max_sub_const` | `CoarseDeGiorgi/Weighted/Testing.lean`, `CoarseDeGiorgi/Weighted/TestingCompactSupport.lean`, `CoarseDeGiorgi/Weighted/TestingTruncation.lean` | proved |
| Lemma A.2 (iv), `i.testing.powers`, with (A.10) and (A.11) | `CoarseDeGiorgi.Harnack.Powers.signedPower_source_package`; for $`\log w`$, `CoarseDeGiorgi.Harnack.Log.log_memH1a` and `CoarseDeGiorgi.log_estimate` | `CoarseDeGiorgi/Harnack/Powers/SignedPower.lean`, `CoarseDeGiorgi/Harnack/Log/Membership.lean`, `LogEstimate.lean` | partial |
| Appendix B (averages over simplices or cubes and Gaussian averages), `a.besov`: the Gaussian $`G_t`$ | `CoarseDeGiorgi.gaussianKernel` | `GaussianKernel.lean` | definition |
| Appendix B: Proposition B.1 (averages and Gaussian averages), `p.besov.averages`, with (B.1) and (B.2), for both families $`\mathscr P_k`$ and $`1\le p\lt\infty`$ | `CoarseDeGiorgi.besov_averages` | `BesovAverages.lean` | partial |
| proof of Proposition B.1: the lower bound on each cell, the upper bound by the wider Gaussian $`G_{2t}`$, and the sums | `CoarseDeGiorgi.NegSobolev.besov_averages_proved` | `CoarseDeGiorgi/NegSobolev/BesovAverages.lean` | proved |
| after Proposition B.1: comparison with the Besov space $`B^{-2s}_{p,1/2}(\mathbb R^d)`$ defined through the Fourier transform (Kerkyacharian and Petrushev) | — | — | not formalized |
| Appendix B: Lemma B.2 (negative Sobolev norms), `l.negative.sobolev`, for $`1\lt p\lt\infty`$ | `CoarseDeGiorgi.negative_sobolev_bound` | `NegativeSobolevBound.lean` | partial |
| after Lemma B.2: comparison with the negative Sobolev norms of the earlier paper | — | — | not formalized |
| proof of Lemma B.2: the bound $`\lVert G_t*g\rVert_{W^{2s-\varepsilon,p'}(\square_0)}\le Ct^{-(2s-\varepsilon)/2}\lVert g\rVert_{L^{p'}(\mathbb R^d)}`$, then duality, Fubini, (B.3), Proposition B.1 for cubes and the geometric series | `CoarseDeGiorgi.NegSobolev.gaussian_test_sobolev_bound`, `CoarseDeGiorgi.NegSobolev.negative_sobolev_bound_of_inputs` (applied to `CoarseDeGiorgi.besov_averages`) | `CoarseDeGiorgi/NegSobolev/TestNormGaussian.lean`, `CoarseDeGiorgi/NegSobolev/LemmaB2Assembly.lean` | proved |
| Appendix C (comparison of cubical and simplicial constants), `a.cubical.simplicial`: Lemma C.1, `l.cubical.simplicial.moments`, with (C.1), for both choices of $`\mathbf B`$ | `CoarseDeGiorgi.cubical_simplicial_moments` | `CubicalSimplicialMoments.lean` | partial |
| proof of Lemma C.1: the Whitney decomposition $`\mathscr W(\triangle)`$ of a simplex and the layer bound (C.2) | `CoarseDeGiorgi.Cubical.exists_maxGood`, `CoarseDeGiorgi.Cubical.maxGood_unique`, `CoarseDeGiorgi.Cubical.layer_weight` (a slightly different admissibility; see the note below) | `CoarseDeGiorgi/Cubical/WhitneyIdx.lean`, `CoarseDeGiorgi/Cubical/WhitneyLayer.lean` | proved |
| Appendix C: proof of Proposition 3.4 | `CoarseDeGiorgi.cubical_simplicial_equivalence` (Section 3), from `CoarseDeGiorgi.Cubical.cubical_simplicial_equivalence_of_moments` | `CubicalSimplicialEquivalence.lean`, `CoarseDeGiorgi/Cubical/Comparison/Equivalence.lean` | partial |
| Appendix D: Lemma D.1 (Bombieri's lemma), `l.bombieri`, with (D.1) | `CoarseDeGiorgi.bombieri_integral_bound` | `BombieriIntegralBound.lean` | proved |

Proposition A.1 is formalized as the facts that the proofs use; there is no
single bundled statement. Not stated in Lean as such: in (i), continuity and
injectivity of the embedding into $`W^{1,1}(U)`$ (membership in $`W^{1,1}`$,
integrability of the flux and completeness are proved); in (ii), the
inclusion $`H^1_{\mathbf a,0}(U)\subseteq W^{1,1}_0(U)`$; in (iii), continuity
of restriction and zero extension (membership is proved, with the restricted
or zero-extended gradient); in (iv), convergence $`T_N(u)\to u`$ in the norm of
$`H^1_{\mathbf a}(U)`$ (pointwise convergence with an energy bound is proved);
in (v), only the variants used are stated (general smooth approximations,
nonnegative compactly supported ones in $`H^1_{\mathbf a,0}(U)`$, bounded ones
for bounded compositions); in (vi), the product $`\varphi w`$ for a general
Lipschitz $`\varphi`$ (smooth cutoffs, products of bounded elements and
Lipschitz functions are treated separately). Lemma A.2 (iv): the statements
on the powers $`w^m`$ hold on every bounded open convex domain; that
$`\log w\in H^1_{\mathbf a}`$ with $`\nabla\log w=w^{-1}\nabla u`$ is proved on
$`\square_0`$, where Section 9 uses it.

**Appendix B.** Proposition B.1 is one declaration, for both families
$`\mathscr P_k`$ and both (B.1) and (B.2), with the single constant
$`\max\{d!\,(4\pi)^{d/2}e^{d/4},\,2^{d/2}e^{d/4}\}`$, which is the paper's
$`d!\,(4\pi)^{d/2}e^{d/4}`$; the means over $`\mathscr T_k`$ are arithmetic means
over its $`d!\,3^{kd}`$ simplices. The upper bound is proved cell by cell for
the operator norm, from the triangle inequality and
$`\bigl|\int_QG_t(x-y)\mathbf b(y)\,dy\bigr|\le2^{d/2}e^{d/4}\bigl(\int_QG_{2t}(x-z)\,dz\bigr)|(\mathbf b)_Q|`$,
where the paper averages over $`z`$ and sums. The proof of Lemma B.2 differs
in four steps.
- The derivatives of $`G_t*g`$ are bounded through the pointwise bound
  $`|\partial^\iota G_t|\le Ct^{-j/2}G_{2t}`$ and the contraction of $`G_{2t}*`$ on
  $`L^{p'}`$, in place of $`\lVert\nabla^jG_t\rVert_{L^1}\le Ct^{-j/2}`$ and Young's
  inequality (the $`L^1`$ bound is also proved). Small translations use the mean
  value theorem with a bound by $`G_{4t}`$, and the seminorm of the array
  $`\nabla^m(G_t*g)`$ is bounded by the sum of the seminorms of its entries.
- The weak derivatives of $`G_t*g`$ are its classical derivatives, by
  integration by parts against test functions supported in any set; the index
  tuples are reversed to match the order in which Lean's iterated derivative
  takes its directions, which only permutes the entries of the array.
- In place of the supremum over $`\lVert g\rVert_{L^{p'}(\mathbb R^d)}\le1`$, the
  proof tests with $`g=(G_t*\mathrm{tr}\,\widetilde{\mathbf b})^{p-1}`$, which is
  bounded and lies in $`L^{p'}`$ because $`\widetilde{\mathbf b}\in L^1`$; this gives
  (B.3) exactly. Test functions are normalized by the homogeneity of
  `sobolevNorm`.
- The last step compares the sums (B.2) for cubes, where the paper applies
  (B.1) at each scale and sums.

Theorem D (iii) takes one constant, $`d!`$ times the larger of the constants
of Lemma B.2 for $`(p,s)`$ and $`(q,t)`$, for both bounds.

**Lemma C.1** is formalized for finite $`1\le p\lt\infty`$, with one constant
$`C(d)`$ for both choices of $`\mathbf B`$; the case $`p=\infty`$ is not formalized.
The Whitney decomposition of a simplex $`\triangle`$ in the proof consists of the
maximal triadic cubes $`Q`$ whose closed concentric cube of twice the side,
$`2\overline Q`$, lies in $`\triangle`$; the paper uses $`3\overline Q\subseteq\triangle`$.
This changes only the constant in the layer bound (C.2); the decomposition
has the same properties, and only (C.1) is part of the statement.

**Lemma D.1.** The exponent $`\kappa`$ of the paper is called `ξ` in Lean.

## Results cited from the literature

The fractional Sobolev inequalities are taken from Di Nezza, Palatucci and
Valdinoci, *Hitchhiker's guide to the fractional Sobolev spaces*
([arXiv:1104.4345](https://arxiv.org/abs/1104.4345)), and proved here. The
other cited results are available in Mathlib or proved in the library.

| Source | Lean declaration | File | Status |
|---|---|---|---|
| Di Nezza–Palatucci–Valdinoci, Theorem 6.5: the fractional Sobolev inequality in the whole space | `CoarseDeGiorgi.dnpv_theorem_6_5`, `CoarseDeGiorgi.dnpvCriticalExponent` | `DnpvTheorem6_5.lean`, `DnpvCriticalExponent.lean` | proved |
| Di Nezza–Palatucci–Valdinoci, Theorem 6.7 on the unit cube (used for Lemma 5.1) | `CoarseDeGiorgi.dnpv_theorem_6_7_unitCube`, `CoarseDeGiorgi.dnpvUnitCube`, `CoarseDeGiorgi.MemDnpvSobolev` | `DnpvTheorem6_7UnitCube.lean`, `DnpvUnitCube.lean`, `MemDnpvSobolev.lean` | proved |

## Mathlib-only restatements

Each restatement is a comparator challenge in
[`CoarseDeGiorgiAudit/Challenge/`](CoarseDeGiorgiAudit/Challenge/), proved
from the library by the file of the same name in
[`CoarseDeGiorgiAudit/Solution/`](CoarseDeGiorgiAudit/Solution/); see
[`COMPARATORS.md`](COMPARATORS.md) for the statements.

| Source | Challenge | Status |
|---|---|---|
| Theorem C, (1.11) | `CoarseDeGiorgiAudit.Harnack.harnack` | proved |
| Theorem C, (1.10), for every $`0\lt\eta\le r^*/2`$ | `CoarseDeGiorgiAudit.WeakHarnack.weakHarnack` | proved |
| Propositions 2.2 and 2.3 on the simplices of $`\mathscr T_k`$ | `CoarseDeGiorgiAudit.ResponseQuadraticForms.responseQuadraticForms` | proved |
| Theorem D (i) with Theorems A and C (the weak Harnack inequality for every $`0\lt\eta\lt\frac{dq}{dq+d-2q}`$) and Corollary B | `CoarseDeGiorgiAudit.LocalBoundednessLpLq.localBoundednessLpLq`, `CoarseDeGiorgiAudit.HarnackLpLq.harnackLpLq`, `CoarseDeGiorgiAudit.WeakHarnackLpLq.weakHarnackLpLq` | proved |
| Theorem D (i) for uniformly elliptic coefficients, with $`p=q`$ chosen for each statement (the weak Harnack inequality for every $`0\lt\eta\lt\frac d{d-2}`$, as after Theorem C) | `CoarseDeGiorgiAudit.LocalBoundednessUniform.localBoundednessUniform`, `CoarseDeGiorgiAudit.HarnackUniform.harnackUniform`, `CoarseDeGiorgiAudit.WeakHarnackUniform.weakHarnackUniform` | proved |
| Theorem D (ii) with Theorems A and C (the weak Harnack inequality for every $`0\lt\eta\le r^*/2`$) and Corollary B | `CoarseDeGiorgiAudit.LocalBoundednessBesov.localBoundednessBesov`, `CoarseDeGiorgiAudit.HarnackBesov.harnackBesov`, `CoarseDeGiorgiAudit.WeakHarnackBesov.weakHarnackBesov` | proved |
| Corollary E, (1.18) and (1.19), with the negative Sobolev norms (1.22) written out | `CoarseDeGiorgiAudit.LocalBoundednessSobolev.localBoundednessSobolev`, `CoarseDeGiorgiAudit.HarnackSobolev.harnackSobolev` | proved |
| Theorem F, (1.20) | `CoarseDeGiorgiAudit.Sharpness.sharpness` | proved |
| Proposition 11.2, (11.12)–(11.15) | `CoarseDeGiorgiAudit.SharpnessPolynomial.sharpnessPolynomial` | proved |
| Proposition 11.3, (11.19) | `CoarseDeGiorgiAudit.SharpnessWeakHarnack.sharpnessWeakHarnack` | proved |

## Differences between the printed and the formal statements

| Where | Paper | Lean |
|---|---|---|
| Theorem A and Corollary B | two statements | one declaration, `CoarseDeGiorgi.local_boundedness`, with one $`\gamma`$ shared by the $`L^2`$ bound and every $`L^\eta`$ bound, $`0\lt\eta\lt2`$ |
| Theorem D | $`1\lt p,q\le\infty`$; three parts in one statement | the three parts for $`1\lt p,q\lt\infty`$, in three declarations, `CoarseDeGiorgi.moment_bounds_lebesgue`, `CoarseDeGiorgi.moment_bounds_besov` and `CoarseDeGiorgi.moment_bounds_sobolev`, each assuming $`d\ge3`$, the standing assumption of the paper; in part (iii), $`0\lt\varepsilon\le2\min\{s,t\}`$ is written $`\varepsilon\le2s`$, $`\varepsilon\le2t`$ |
| Corollary E | one statement with constants $`C`$, $`\gamma`$; $`\mathbf a\in W^{-\alpha,p}\cap L^1`$, $`\mathbf a^{-1}\in W^{-\beta,q}\cap L^1`$ | two declarations, `CoarseDeGiorgi.local_boundedness_sobolev` and `CoarseDeGiorgi.harnack_sobolev`, with independent constants (the larger serves both); $`\theta`$ is an argument fixed by its defining equation; $`L^1`$ is the entrywise integrability that the negative Sobolev norms take as arguments; the finite right side for $`\rho_2\lt1`$ is the finiteness of $`\lVert u_+\rVert_{L^2(\rho_2\square_0)}`$ |
| Section 1.7 and (1.22) | norms on open sets; $`\nabla^jw`$ the array of weak derivatives; $`1\lt p\le\infty`$ in (1.22) | `CoarseDeGiorgi.sobolevNorm` and `CoarseDeGiorgi.negSobolevNorm` take a proof that the set is open; `sobolevNorm` is an infimum over arrays of weak derivatives, equal to the value at $`\nabla^jw`$ (`CoarseDeGiorgi.sobolevNorm_eq_of_isWeakDerivArray`) and $`\infty`$ when they do not exist; the norm of an array is the Euclidean norm over its $`d^j`$ ordered index tuples; `negSobolevNorm` is defined for $`1\lt p\lt\infty`$ and takes the entrywise integrability of the matrix field as an argument; the Mathlib-only restatements carry no such arguments |
| Proposition B.1 | $`1\le p\le\infty`$; $`\mathscr P_k`$ one of two families | $`1\le p\lt\infty`$; one declaration for both families, (B.1) and (B.2), with one constant |
| Lemma B.2 | $`1\lt p\le\infty`$ | $`1\lt p\lt\infty`$ |
| proof of Proposition B.1 | the upper bound averaged over $`z\in Q`$ and summed | the upper bound cell by cell, for the operator norm, through the triangle inequality |
| proof of Lemma B.2 | $`\lVert\nabla^jG_t\rVert_{L^1}\le Ct^{-j/2}`$ and Young's inequality; a supremum over $`\lVert g\rVert_{L^{p'}}\le1`$; (B.1) at each scale | pointwise domination of $`\partial^\iota G_t`$ by $`Ct^{-j/2}G_{2t}`$; the single test function $`(G_t*\mathrm{tr}\,\widetilde{\mathbf b})^{p-1}`$; the sums (B.2) for cubes |
| (1.12) and Theorem D (ii) | the quasi-norm for $`\lvert\mathbf b\rvert\in L^1`$ and $`1\le p\le\infty`$ | `CoarseDeGiorgi.besovCubeNorm`, for finite $`p`$, takes the entrywise integrability of the matrix field as an argument; the Mathlib-only restatements carry no such argument |
| (1.4) | $`\mathbf a(U)`$ defined by the minimum with affine boundary values | `CoarseDeGiorgi.upperResponse` is defined through (2.6); that its quadratic form is the minimum (1.4) is part of `CoarseDeGiorgi.upperResponse_spec` |
| Theorem F | integrabilities $`p,q`$; a measurable $`a`$ on $`(-\frac12,\frac12)^{d-1}`$, the field $`a(y)I`$, the quasi-norms or Lebesgue norms finite, and $`u\in\mathcal C_{\mathrm{sol}}(\square_0)`$ with $`u\ge1`$, (1.20) and unboundedness near every point of the segment | `CoarseDeGiorgi.sharpness` names the integrabilities $`\xi,\zeta`$; it gives $`a`$ as a Borel function on all of $`\mathbb R^d`$, positive everywhere and invariant under changes of $`x_1`$; the field is `fun x => a x • 1`; it also provides the entrywise integrability of $`\mathbf a`$ and $`\mathbf a^{-1}`$ that the quasi-norms take as arguments; $`\mathrm{ess\,sup}\,u=\infty`$ is `eLpNorm u ⊤ … = ⊤`, the infimum is `nonnegativeEssInf`, valued in `ℝ≥0∞`, and the unboundedness near a point $`x`$ says that `eLpNorm u ⊤` is infinite on $`N\cap\square_0`$ for every neighborhood $`N`$ of $`x`$ |
| Proposition 11.2 | families for $`0\lt\varepsilon\lt\frac18`$; comparisons $`\asymp`$; (11.14) for $`\frac12\le\rho_1\lt\rho_2\le1`$ | `CoarseDeGiorgi.optimal_powers`: families indexed by every real $`\varepsilon`$, with the properties asserted for $`0\lt\varepsilon\lt\frac18`$; each $`\asymp`$ written with one explicit constant $`C\ge1`$; the height for $`\frac12\le\rho_1\lt1`$ and the $`L^\eta`$ comparison for $`\frac12\lt\rho_2\le1`$; the limit (11.15) in `ℝ≥0∞` along $`\varepsilon\to0^+`$ |
| Definition 3.3, Proposition 3.4, (3.20), Lemma C.1 | indices $`1\le\mathsf m,p,q\le\infty`$; in Proposition 3.4, a constant independent of $`\mathsf m`$ | $`\mathsf m=1`$ and finite $`p,q`$ |
| Proposition 3.4 | one statement | two declarations: the comparison in the range (3.16), and the inequalities with constant one for all $`s,t\gt0`$ |
| (3.20) | under (3.19) and (3.16) | under (3.16) only, in $`[0,\infty]`$ |
| Section 2 and Appendix A | bounded connected Lipschitz domains | bounded open convex domains |
| (2.14) | arbitrary domains | $`U=\square_0`$ |
| (2.15), (2.16) | partitions into bounded connected Lipschitz subdomains | partitions of a bounded open convex domain into bounded open convex pieces |
| Lemma 3.2 and $`L_hf`$ | functions on $`\mathbb R^d\setminus\tau\overline{\square}_0`$ | functions on $`\mathbb R^d`$ that vanish on $`\tau\overline{\square}_0`$ |
| Lemma 4.1 | $`P_k(\nabla w;Q)`$ | $`P_{k-1}(\nabla w;Q)`$, a weaker bound |
| Lemma 4.2 | proof through Neumann problems | a different proof, with explicit reconstruction kernels |
| Lemma 5.1 | $`1\le\xi\lt\infty`$ | $`1\lt\xi\lt\infty`$ |
| Proposition 7.2 | "a good radius" given by Proposition 5.6 | the conclusions of Proposition 5.6 that the proof uses, as hypotheses with an explicit constant |
| (9.7) and Lemma 9.5 | $`p_*=c/\sqrt\Theta`$ with $`c=\min\{r/4,1/(1+C_{(9.5)})\}`$ | $`p_*=c/\sqrt{1+\Theta}`$ for some $`0\lt c\le r/4`$ depending only on $`d,p,q,s,t`$ |
| Lemmas 9.3 and 9.4 | the powers $`\gamma_5r`$ and $`\gamma_6`$ of $`(\rho_2-\rho_1)^{-1}`$ | larger powers |
| proofs of (9.14) and (9.15) | chains of cubes whose centres differ in one coordinate | centres may differ in several coordinates; one more layer of cubes for (9.15) |
| Lemma 9.6 | $`v=\sum_kv_k`$ in $`L^r(\square_0)`$, with $`v_k\in L^\infty(\square_0)`$ | the partial sums converge to $`v`$ in $`L^r(\square_0)`$; each $`v_k`$ is a.e. strongly measurable, with finite $`L^\infty`$ norm by (9.17) |
| proof of Lemma 9.6 | Newtonian potentials and the Calderón–Zygmund estimate on $`\mathbb R^d`$ | Dirichlet problems on $`\square_0`$, Calderón–Zygmund estimates for cubes, and Morrey's inequality on cubes |
| Proposition 9.7 | the potential of a finite nonnegative Radon measure $`\nu`$ on $`\square_0`$ whose action extends continuously to $`H^1_{\mathbf a,0}(\square_0)`$ | every $`v\in H^1_{\mathbf a,0}(\square_0)`$ satisfying the equation of the potential against $`C^\infty_c(\square_0)`$, for a finite measure $`\nu`$ on $`\mathbb R^d`$ vanishing outside $`\square_0`$ whose action is bounded by the energy |
| proof of Proposition 9.7 | positivity of $`v`$, the truncations $`v\wedge K`$, the decreasing rearrangement | symmetric truncations, without positivity; a sum over level sets |
| Lemma 9.8 | a nonnegative Radon measure on $`\square_0`$; the action of $`\nu`$ extends continuously to $`H^1_{\mathbf a,0}(\square_0)`$, and $`V`$ is its potential | a measure on $`\mathbb R^d`$ vanishing outside $`\square_0`$, finite on compact subsets of $`\square_0`$; $`\nu`$ is finite and its action is bounded by the energy; $`V\in H^1_{\mathbf a,0}(\square_0)`$ satisfies the equation of the potential against $`C^\infty_c(\square_0)`$ |
| proof of Lemma 9.8 | the measure $`\mu`$ by uniform approximation; the potential by the Lax–Milgram lemma; the unique capacitary function; monotone convergence in Step 6 | M. Riesz's extension theorem; the Riesz representation theorem in $`H^1_{\mathbf a,0}(\square_0)`$; a least-energy capacitary function cut off at $`0`$ and $`1`$, without uniqueness; inner regularity of $`\nu`$ |
| Proposition 11.3 | a field $`\mathbf a(x)=a(\lvert x\rvert)I`$; supersolutions for $`0\lt\varepsilon\lt\frac18`$ | a profile $`a`$ and the field $`a(\lvert x\rvert)I`$ with the Euclidean norm; families indexed by every real $`\varepsilon`$, with the properties for $`0\lt\varepsilon\lt\frac18`$; the limit (11.19) in `ℝ≥0∞` |
| proof of Proposition 11.3 | $`u_\varepsilon=G(\max\{\lvert x\rvert,\varepsilon\})`$, infimum $`G(R/4)`$, the asymptotics (11.24) | smooth supersolutions with a smooth source in $`\varepsilon\le\lvert x\rvert\le2\varepsilon`$, infimum $`G(R/4)-G(R/\sqrt2)`$, an elementary bound for the logarithm |
| proof of Lemma C.1 | Whitney cubes with $`3\overline Q\subseteq\triangle`$ | Whitney cubes with $`2\overline Q\subseteq\triangle`$ |
| Lemma 11.1 | $`0\lt\varepsilon\lt1`$, $`y_0\in\mathbb R^{d-1}`$ | $`0\lt\varepsilon\lt\frac14`$, coordinates of $`y_0`$ in $`[-\frac14,\frac14]`$ |
| proof of Theorem F | the power $`\kappa`$ of (11.3), the subsolution (11.5) | a $`\kappa`$ satisfying (11.3), and a different subsolution in each cylinder (see Section 11 above) |
| all estimates | real-valued norms and constants | values in `ℝ≥0∞`; the Harnack constants use the real value of $`\Theta`$ |
