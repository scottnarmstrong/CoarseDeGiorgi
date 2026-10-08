import Mathlib

/-!
Local boundedness for coefficients in negative Sobolev spaces (Corollary E of the manuscript,
(1.18)).

Let `d ≥ 3`, `1 < p, q < ∞` and `α, β ≥ 0`, with `θ = 1 − (α+β)/2 − (d−1)(1/p+1/q)/2 > 0`. Let `a`
satisfy the standing assumption on `cube 1`, with `|a|, |a⁻¹| ∈ L¹(cube 1)` and finite negative
Sobolev norms (1.22) `‖a‖_{W^{−α,p}(cube 1)}` and `‖a⁻¹‖_{W^{−β,q}(cube 1)}`, and put
`N = ‖a‖_{W^{−α,p}(cube 1)} ‖a⁻¹‖_{W^{−β,q}(cube 1)}`. There are `C ≥ 0` and `γ > 0`, depending
only on `d, p, q, α, β`, such that every weighted subsolution `u` on `cube 1` satisfies, for
`1/2 ≤ ρ₁ < ρ₂ ≤ 1`,
  `‖u₊‖_{L∞(cube ρ₁)} ≤ C (ρ₂−ρ₁)^{−γ} N^{(d−1)/(2θ)} ‖u₊‖_{L²(cube ρ₂)}`,
with a finite right side when `ρ₂ < 1`.
The negative Sobolev norm of order `−s` (`s = α` for `a`, `s = β` for `a⁻¹`) is dual to the
Sobolev norm `W^{s,p'}`, `p' = p/(p−1)`, of the open cube, tested on bounded functions; the
Sobolev norm combines the `L^{p'}` norms of the weak
derivatives up to order `⌊s⌋₊` (defined by integration by parts against smooth compactly
supported functions) with the fractional seminorm (1.21) of the highest ones. The `L¹`
hypotheses are the manuscript's `a ∈ W^{−α,p} ∩ L¹`, `a⁻¹ ∈ W^{−β,q} ∩ L¹`; they also follow from
the standing assumption.
-/

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.LocalBoundednessSobolev

/-! ## Ambient space and cubes -/

/-- Vectors in the ambient space `ℝᵈ`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on ambient vectors. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The open cube `(-ρ/2, ρ/2)ᵈ`. -/
def cube {d : ℕ} (ρ : ℝ) : Set (Vec d) :=
  {x | ∀ i, (-(ρ / 2)) < x i ∧ x i < ρ / 2}


/-! ## Coefficient fields -/

/-- A coefficient field: a `d × d` matrix at each point (no regularity is assumed here). -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

/-- Coefficients are measurable and positive definite a.e.
Their trace and inverse trace are integrable on the domain. -/
def IsWeightedCoeffOn {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) : Prop :=
  AEStronglyMeasurable a (volume.restrict V) ∧
    (∀ᵐ x ∂(volume.restrict V), (a x).PosDef) ∧
    Integrable (fun x => (a x).trace) (volume.restrict V) ∧
    Integrable (fun x => ((a x)⁻¹).trace) (volume.restrict V)


/-! ## Averages and energies -/

/-- Weighted energy `∫_U G · aG` of a vector field `G` (for `G = ∇u`, the energy of `u`),
as an extended nonnegative real. -/
noncomputable def weightedEnergy {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal (G x ⬝ᵥ (a x *ᵥ G x))

/-- Normalized average `⨍_U f = |U|⁻¹ ∫_U f`. -/
noncomputable def averageOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, f x ∂volume


/-! ## The weighted space `H¹ₐ` -/

/-- Coordinate gradient of a smooth function: `(∇φ x)ᵢ = Dφ(x)eᵢ`. -/
noncomputable def smoothGrad {d : ℕ} (φ : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => fderiv ℝ φ x (Pi.single i (1 : ℝ))

/-- A smooth core function is `C^∞` on `V`, integrable on `V`, and has finite weighted energy. -/
noncomputable def IsSmoothCore {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) φ V ∧
    Integrable φ (volume.restrict V) ∧
    weightedEnergy a V (smoothGrad φ) < ⊤

/-- `H¹ₐ(V)` is the smooth-core closure in squared mean plus weighted energy.
Approximants converge in `L¹` on compact subsets and gradients in weighted energy. -/
noncomputable def MemH1a {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  AEStronglyMeasurable u (volume.restrict V) ∧
  AEStronglyMeasurable G (volume.restrict V) ∧
  ∃ φ : ℕ → Vec d → ℝ,
    (∀ n, IsSmoothCore a V (φ n)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
        ENNReal.ofReal ((averageOn V (fun x => φ n x - φ m x)) ^ 2) +
          weightedEnergy a V
            (fun x => smoothGrad (φ n) x - smoothGrad (φ m) x) <
          ENNReal.ofReal ε) ∧
    (∀ K : Set (Vec d), IsCompact K → K ⊆ V →
      Filter.Tendsto
        (fun n => ∫⁻ x in K, ‖φ n x - u x‖ₑ)
        Filter.atTop (nhds (0 : ENNReal))) ∧
    Filter.Tendsto
      (fun n => weightedEnergy a V (fun x => smoothGrad (φ n) x - G x))
      Filter.atTop (nhds (0 : ENNReal))


/-! ## Subsolutions, supersolutions, and solutions -/

/-- A weighted subsolution has nonpositive flux pairing with every nonnegative
smooth compactly supported test: `∫_V ∇φ · a∇u ≤ 0`. -/
noncomputable def IsWeightedSubsolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) →
      Integrable
        (fun x => smoothGrad φ x ⬝ᵥ (a x *ᵥ G x))
        (volume.restrict V) ∧
      ∫ x in V,
        smoothGrad φ x ⬝ᵥ (a x *ᵥ G x) ∂volume ≤ 0

/-- Positive part `u₊ = max(u, 0)`. -/
def positivePart {d : ℕ} (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => max (u x) 0

/-! ## Sobolev norms and negative Sobolev norms -/

/-- `D` is the array `∇ʲw` of the weak partial derivatives of order `j` of `w` on `U`. The entry
`D ι`, for an ordered index tuple `ι = (ι 0, …, ι (j−1))`, is the weak derivative
`∂_{ι 0} ⋯ ∂_{ι (j−1)} w`. The function `w` and every entry are locally integrable on `U`, and for
every smooth `φ` with compact support in `U`, `∫_U w ∂^ι φ = (−1)ʲ ∫_U (D ι) φ`, where
`∂^ι φ(x) = Dʲφ(x)(e_{ι 0}, …, e_{ι (j−1)})` is the iterated derivative in the coordinate
directions. For `j = 0` the array has one entry, equal to `w` almost everywhere. -/
def IsWeakDerivArray {d : ℕ} (U : Set (Vec d)) (j : ℕ) (w : Vec d → ℝ)
    (D : (Fin j → Fin d) → Vec d → ℝ) : Prop :=
  LocallyIntegrableOn w U volume ∧
    ∀ ι : Fin j → Fin d,
      LocallyIntegrableOn (D ι) U volume ∧
        ∀ φ : Vec d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ →
          HasCompactSupport φ →
          tsupport φ ⊆ U →
          ∫ x in U, w x * iteratedFDeriv ℝ j φ x (fun k => Pi.single (ι k) (1 : ℝ)) ∂volume =
            (-1 : ℝ) ^ j * ∫ x in U, D ι x * φ x ∂volume

/-- The Euclidean distance `|x − y| = (∑ᵢ (xᵢ − yᵢ)²)^{1/2}`. (Mathlib's `dist` on `Fin d → ℝ` is
the sup distance, and it is not used.) -/
noncomputable def euclidDist {d : ℕ} (x y : Vec d) : ℝ :=
  Real.sqrt (∑ i, (x i - y i) ^ 2)

/-- The fractional seminorm (1.21) of order `σ` and integrability `r` of an array-valued function
`F = (F i)ᵢ` on `V`:
`[F]_{W^{σ,r}(V)} = (∫_V ∫_V |F(x) − F(y)|^r / |x − y|^{d+σr} dx dy)^{1/r}`,
where `|F(x) − F(y)| = (∑ᵢ (F i x − F i y)²)^{1/2}` is the Euclidean norm of the array difference.
The double integral is the lower integral for the product measure on `V × V`. -/
noncomputable def arrayFracSeminorm {d : ℕ} {ι : Type*} [Fintype ι] (V : Set (Vec d))
    (σ r : ℝ) (F : ι → Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ z : Vec d × Vec d,
      ENNReal.ofReal
        (Real.sqrt (∑ i, (F i z.1 - F i z.2) ^ 2) ^ r /
          euclidDist z.1 z.2 ^ ((d : ℝ) + σ * r))
    ∂((volume.restrict V).prod (volume.restrict V))).rpow (1 / r)

/-- The Sobolev norm `‖w‖_{W^{s,ξ}(U)}` of order `s ≥ 0` and integrability `1 ≤ ξ < ∞`. Write
`s = m + σ` with `m = ⌊s⌋₊` and `0 ≤ σ < 1`. Then
`‖w‖_{W^{s,ξ}(U)} = (∑_{j=0}^m ‖∇ʲw‖_{L^ξ(U)}^ξ + [∇ᵐw]_{W^{σ,ξ}(U)}^ξ)^{1/ξ}`,
the seminorm omitted if `σ = 0`. Here `∇ʲw` is the array of the weak partial derivatives of
order `j` (`∇⁰w = w`), and `‖∇ʲw‖_{L^ξ(U)}` is the `L^ξ(U)` norm of its pointwise Euclidean norm
`|∇ʲw(x)| = (∑_ι (∂^ι w(x))²)^{1/2}` over the `dʲ` ordered index tuples `ι`. The infimum runs
over all families `D 0, …, D m` of weak derivative arrays of `w` on `U`. On an open set (here
always `cube 1`) weak derivatives are unique almost everywhere, so the infimum is the value at
`∇⁰w, …, ∇ᵐw`; it is `∞` if `w` has no weak derivatives up to order `m`. -/
noncomputable def sobolevNorm {d : ℕ} (U : Set (Vec d)) (s ξ : ℝ) (w : Vec d → ℝ) : ℝ≥0∞ :=
  ⨅ (D : (j : Fin (⌊s⌋₊ + 1)) → (Fin j → Fin d) → Vec d → ℝ)
    (_ : ∀ j : Fin (⌊s⌋₊ + 1), IsWeakDerivArray U j w (D j)),
    ((∑ j : Fin (⌊s⌋₊ + 1),
        (eLpNorm (fun x => Real.sqrt (∑ ι, D j ι x ^ 2)) (ENNReal.ofReal ξ)
          (volume.restrict U)).rpow ξ) +
      (if s - ⌊s⌋₊ = 0 then 0
        else (arrayFracSeminorm U (s - ⌊s⌋₊) ξ (D (Fin.last ⌊s⌋₊))).rpow ξ)).rpow
      (1 / ξ)

/-- The negative Sobolev norm (1.22) `‖b‖_{W^{−s,p}(U)}` of a matrix field `b`, of order `−s ≤ 0`
and integrability `1 < p < ∞`: with `p' = p/(p−1)`, it is the dual norm tested on bounded
functions,
`‖b‖_{W^{−s,p}(U)} = sup {|∫_U g b| : g ∈ L^∞(U), ‖g‖_{W^{s,p'}(U)} ≤ 1}`.
Here `∫_U g b` is the matrix of the integrals `∫_U g b_{ij}`, and `|·|` is the `ℓ²` operator
norm. It is used for fields with `|b| ∈ L¹(U)`, for which these are genuine integrals. The value
lies in `[0, ∞]`. -/
noncomputable def negSobolevNorm {d : ℕ} (U : Set (Vec d)) (b : CoeffField d)
    (s p : ℝ) : ℝ≥0∞ :=
  ⨆ (g : Vec d → ℝ) (_ : MemLp g ⊤ (volume.restrict U))
    (_ : sobolevNorm U s (p / (p - 1)) g ≤ 1),
    ENNReal.ofReal ‖Matrix.of fun i j => ∫ x in U, g x * b x i j ∂volume‖

/-! ## Parameters -/

/-- `θ = 1 − (α+β)/2 − (d−1)(1/p+1/q)/2`. -/
noncomputable def theta (d : ℕ) (p q α β : ℝ) : ℝ :=
  1 - (α + β) / 2 - (((d : ℝ) - 1) / 2) * (1 / p + 1 / q)

/-! ## The theorem -/

theorem localBoundednessSobolev
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) (p q α β : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hθ : 0 < theta d p q α β) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧
      ∀
        -- coefficient field: `a ∈ W^{−α,p} ∩ L¹` and `a⁻¹ ∈ W^{−β,q} ∩ L¹`
        (a : CoeffField d), IsWeightedCoeffOn (cube 1) a →
        Integrable (fun x => ‖a x‖) (volume.restrict (cube 1)) →
        Integrable (fun x => ‖(a x)⁻¹‖) (volume.restrict (cube 1)) →
        negSobolevNorm (cube 1) a α p < ⊤ →
        negSobolevNorm (cube 1) (fun x => (a x)⁻¹) β q < ⊤ →
        let N : ℝ≥0∞ :=
          negSobolevNorm (cube 1) a α p *
            negSobolevNorm (cube 1) (fun x => (a x)⁻¹) β q
        ∀
          -- weighted subsolution
          (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (cube 1) u G →
          -- conclusion
          ∀ (ρ₁ ρ₂ : ℝ), 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
            let rhs := ENNReal.ofReal C *
              (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-γ) *
              N.rpow (((d : ℝ) - 1) / (2 * theta d p q α β)) *
              eLpNorm (positivePart u) 2 (volume.restrict (cube ρ₂))
            eLpNorm (positivePart u) ⊤ (volume.restrict (cube ρ₁)) ≤ rhs ∧
              (ρ₂ < 1 →
                eLpNorm (positivePart u) 2 (volume.restrict (cube ρ₂)) < ⊤) := by
  sorry

end CoarseDeGiorgiAudit.LocalBoundednessSobolev
