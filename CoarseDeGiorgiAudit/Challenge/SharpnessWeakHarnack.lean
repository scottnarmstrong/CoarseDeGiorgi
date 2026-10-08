import Mathlib

/-!
# Proposition 11.3 (Sharpness of the weak Harnack exponent)

Let `d ≥ 3`, `1 < p,q`, `s,t > 0`, and suppose
`θ = 1 − s − t − (d−1)(1/p+1/q)/2 > 0`. Let `r = 2q/(q+1)`, let
`r* = dr/(d − (1−t)r)` be the Sobolev exponent of `W^{1−t,r}`, and let
`η_c = r*/2 = d/(d−2+2t+d/q)`. Theorem C gives the weak Harnack inequality (1.10)
for `0 < η ≤ η_c`. There are a radial weighted coefficient field `x ↦ a(|x|) I` on
`cube 1` (measurable, positive definite, with `tr a, tr a⁻¹ ∈ L¹`) with
`Λ_{s,1,p} < ∞` and `λ_{t,1,q} > 0`, and nonnegative weighted supersolutions `u_ε`
on `cube 1`, `0 < ε < 1/8`, such that `essinf_{cube(1/2)} u_ε > 0` does not depend
on `ε` and, for every `η > η_c`,
`(⨍_{cube(5/8)} u_ε^η)^{1/η} / essinf_{cube(1/2)} u_ε → ∞` as `ε → 0⁺` (11.19).
The field and the supersolutions are the same for every `η > η_c`. Since `Θ < ∞`
for this field, (1.10) fails for every `η > η_c`, with any finite constant.

Here `|x|` is the Euclidean norm, and `a(△)` is the upper response and `a_*⁻¹(△)`
the inverse lower response of each cell `△`, both defined below by polarization.
The paper's proof takes `a(ϱ) = ϱ^β log³(e√d/ϱ)` with `β = 2t + d/q`; the
statement, like the paper's, asserts that a radial field with these properties
exists.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.SharpnessWeakHarnack

/-! ## Ambient space and cubes -/

/-- Vectors in the ambient space `ℝᵈ`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on ambient vectors. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The open cube `(-ρ/2, ρ/2)ᵈ`. -/
def cube {d : ℕ} (ρ : ℝ) : Set (Vec d) :=
  {x | ∀ i, (-(ρ / 2)) < x i ∧ x i < ρ / 2}

/-! ## Coefficient fields -/

/-- A coefficient field assigns a real matrix to each point of `ℝᵈ`. -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

/-- Coefficients are measurable and positive definite a.e., with integrable trace
and inverse trace on the domain. -/
def IsWeightedCoeffOn {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) : Prop :=
  AEStronglyMeasurable a (volume.restrict V) ∧
    (∀ᵐ x ∂(volume.restrict V), (a x).PosDef) ∧
    Integrable (fun x => (a x).trace) (volume.restrict V) ∧
    Integrable (fun x => ((a x)⁻¹).trace) (volume.restrict V)

/-! ## Averages and energies -/

/-- Weighted energy `∫_U ∇u · a ∇u`, recorded as an extended nonnegative real. -/
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

/-- A smooth core function has finite weighted energy and is integrable on `V`. -/
noncomputable def IsSmoothCore {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) φ V ∧
    Integrable φ (volume.restrict V) ∧
    weightedEnergy a V (smoothGrad φ) < ⊤

/-- `H¹ₐ(V)` is the smooth-core closure in squared mean plus weighted energy.
Approximants converge in L¹ on compact subsets of V, with gradients to G
in weighted energy. -/
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
      ∫ x in V, smoothGrad φ x ⬝ᵥ (a x *ᵥ G x) ∂volume ≤ 0

/-- A weighted supersolution is the negative of a weighted subsolution. -/
noncomputable def IsWeightedSupersolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  IsWeightedSubsolution a V (fun x => -u x) (fun x => -G x)

/-- A weighted solution has zero flux pairing with every smooth compactly
supported test: `∫_V ∇φ · a∇u = 0`. -/
noncomputable def IsWeightedSolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      Integrable
        (fun x => smoothGrad φ x ⬝ᵥ (a x *ᵥ G x))
        (volume.restrict V) ∧
      ∫ x in V, smoothGrad φ x ⬝ᵥ (a x *ᵥ G x) ∂volume = 0

/-! ## Norms, moments, and parameters -/

/-- Essential infimum of `u` on `V`, encoded in `ℝ≥0∞` for `u ≥ 0` a.e. -/
noncomputable def essInfNonneg {d : ℕ}
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict V)

/-- Normalized `Lᵇ` moment `(|V|⁻¹ ∫_V |u|ᵇ)^(1/b)`, defined for all `b`. -/
noncomputable def normalizedLpMoment {d : ℕ} (b : ℝ)
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  ((volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |u x|).rpow b).rpow (1 / b)

/-- Triadic offset of the grid index `j` at level `k` (cells of side `3⁻ᵏ`). -/
def gridOffset {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Fin d → ℤ :=
  fun i => (j i : ℤ) - (((3 ^ k - 1) / 2 : ℕ) : ℤ)

/-- The triangulation has `3^k` grid points per axis and cells of side `3⁻ᵏ`. -/
noncomputable def triangulation {d : ℕ} (k : ℕ) :
    Finset ((Fin d → ℤ) × Equiv.Perm (Fin d)) := by
  classical
  exact
    (Finset.univ : Finset ((Fin d → Fin (3 ^ k)) × Equiv.Perm (Fin d))).image
      (fun jp => (gridOffset k jp.1, jp.2))

/-- Indices for the simplices in the triangulation at level `k` (cells of side `3⁻ᵏ`). -/
def SimplexIndex (d k : ℕ) :=
  {η : (Fin d → ℤ) × Equiv.Perm (Fin d) // η ∈ triangulation k}

/-- The simplex with triadic scale `3^n`, permutation `π`, and offset `z`. -/
def simplex {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) : Set (Vec d) :=
  {x | ∃ y : Vec d,
    x = z + (fun i => (3 : ℝ) ^ n * y i) ∧
      (∀ i, (-(1 / 2 : ℝ)) < y i ∧ y i < 1 / 2) ∧
      (∀ i j : Fin d, i < j → y (π i) < y (π j))}

/-- The simplex cell indexed by `η` at resolution `3⁻ᵏ`. -/
def simplexCell {d : ℕ} (k : ℕ) (η : SimplexIndex d k) : Set (Vec d) :=
  simplex (-(k : ℤ)) η.1.2
    (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.1.1 i : ℝ))

/-- Positive moment margin `1 − s − t − (d−1)(1/p+1/q)/2`. -/
noncomputable def paramTheta (d : ℕ) (p q s t : ℝ) : ℝ :=
  1 - s - t - (((d : ℝ) - 1) / 2) * (1 / p + 1 / q)

/-- The exponent `r = 2q/(q+1)` of (1.7). -/
noncomputable def paramR (q : ℝ) : ℝ := 2 * q / (q + 1)

/-- The Sobolev exponent `r* = dr/(d − (1−t)r)` of `W^{1−t,r}` (Theorem C, (3.22)).
The critical weak Harnack exponent is `η_c = r*/2`. -/
noncomputable def rStar (d : ℕ) (q t : ℝ) : ℝ :=
  (d : ℝ) * paramR q / ((d : ℝ) - (1 - t) * paramR q)

/-- The upper directional response is the supremum of
`⨍_V (-∇w · a∇w + 2e · a∇w)` over weighted solutions `w`. -/
noncomputable def upperDirectionalResponse {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (e : Vec d) : EReal :=
  ⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
    (_ : IsWeightedSolution a V w G),
    ((averageOn V
      (fun x =>
        - (G x ⬝ᵥ (a x *ᵥ G x)) +
          2 * (e ⬝ᵥ (a x *ᵥ G x))) : ℝ) : EReal)

/-- The paper's upper response `a(V)` (Prop. 2.2, (2.7)) is the symmetric matrix
with `e·a(V)e = upperDirectionalResponse a V e`, written by polarization:
`a(V)ᵢⱼ = (F(eᵢ+eⱼ) − F(eᵢ−eⱼ))/4`, where
`F = upperDirectionalResponse a V`. -/
noncomputable def upperResponse {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) : Mat d :=
  Matrix.of fun i j =>
    ((upperDirectionalResponse a V
        (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))).toReal -
      (upperDirectionalResponse a V
        (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ))).toReal) / 4

/-- The lower directional response is the supremum of
`⨍_V (-∇w · a∇w + 2e · ∇w)` over weighted solutions `w`. -/
noncomputable def lowerDirectionalResponse {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (e : Vec d) : EReal :=
  ⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
    (_ : IsWeightedSolution a V w G),
    ((averageOn V
      (fun x =>
        - (G x ⬝ᵥ (a x *ᵥ G x)) +
          2 * (e ⬝ᵥ G x)) : ℝ) : EReal)

/-- The paper's inverse lower response `a_*⁻¹(V)` (Prop. 2.3, (1.5)) is the
symmetric matrix with `e·a_*⁻¹(V)e = lowerDirectionalResponse a V e`, written by
polarization: `a_*⁻¹(V)ᵢⱼ = (F(eᵢ+eⱼ) − F(eᵢ−eⱼ))/4`, where
`F = lowerDirectionalResponse a V`. -/
noncomputable def lowerResponseInv {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) : Mat d :=
  Matrix.of fun i j =>
    ((lowerDirectionalResponse a V
        (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))).toReal -
      (lowerDirectionalResponse a V
        (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ))).toReal) / 4

/-- Upper response moment (3.12):
`Λ_{s,1,p} = ((1−3^{−s}) Σ_k 3^{−ks}
(⨍_{△∈𝒯_k} |a(△)|^p)^{1/(2p)})²`, where `|·|` is the operator norm.
Level `k` has `d!·3^{kd}` cells, the Kuhn simplices of triadic cubes of side `3⁻ᵏ`. -/
noncomputable def upperMoment {d : ℕ} (a : CoeffField d)
    (s p : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
    ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal (
          ((triangulation (d := d) k).attach.sum fun η =>
            Real.rpow ‖upperResponse a
              (simplexCell k ⟨η.1, η.2⟩)‖ p) /
            ((triangulation (d := d) k).card : ℝ))).rpow (1 / (2 * p))) ^ 2

/-- Inverse lower response moment (3.13):
`λ_{t,1,q} = ((1−3^{−t}) Σ_k 3^{−kt}
(⨍_{△∈𝒯_k} |a_*⁻¹(△)|^q)^{1/(2q)})^{−2}`, where `|·|` is the operator norm.
Level `k` has `d!·3^{kd}` cells, the Kuhn simplices of triadic cubes of side `3⁻ᵏ`. -/
noncomputable def lowerMoment {d : ℕ} (a : CoeffField d)
    (t q : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 - Real.rpow 3 (-t)) *
    ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
        (ENNReal.ofReal (
          ((triangulation (d := d) k).attach.sum fun η =>
            Real.rpow ‖lowerResponseInv a
              (simplexCell k ⟨η.1, η.2⟩)‖ q) /
            ((triangulation (d := d) k).card : ℝ))).rpow (1 / (2 * q))).rpow (-2)

/-! ## Radial coefficient fields -/

/-- The Euclidean norm `|x| = (∑ᵢ xᵢ²)^{1/2}`. -/
noncomputable def euclidNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The radial isotropic coefficient field `x ↦ a(|x|) I` with profile `a : ℝ → ℝ`. -/
noncomputable def radialField (d : ℕ) (a : ℝ → ℝ) : CoeffField d :=
  fun x => a (euclidNorm x) • (1 : Mat d)

/-! ## Proposition 11.3 -/

/-- **Proposition 11.3 (Sharpness of the weak Harnack exponent).** For `d ≥ 3`,
`1 < p,q`, `s,t > 0`, and `θ > 0`, there are a profile `a`, for which the radial
field `a(|x|) I` is a weighted coefficient field on `cube 1` with
`Λ_{s,1,p} < ∞` and `λ_{t,1,q} > 0`, and nonnegative weighted supersolutions `u_ε`
on `cube 1` for `0 < ε < 1/8`, such that `essinf_{cube(1/2)} u_ε` is positive and
does not depend on `ε` and, for every `η > η_c = r*/2`,
`(⨍_{cube(5/8)} u_ε^η)^{1/η} / essinf_{cube(1/2)} u_ε → ∞` as `ε → 0⁺`. -/
theorem sharpnessWeakHarnack
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ a : ℝ → ℝ,
      -- the radial field: tr a, tr a⁻¹ ∈ L¹, Λ_{s,1,p} < ∞ and λ_{t,1,q} > 0
      IsWeightedCoeffOn (cube 1) (radialField d a) ∧
      upperMoment (radialField d a) s p < ⊤ ∧
      0 < lowerMoment (radialField d a) t q ∧
      ∃ (u : ℝ → Vec d → ℝ) (G : ℝ → Vec d → Vec d),
        -- nonnegative weighted supersolutions u_ε for 0 < ε < 1/8
        (∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
          (∀ᵐ x ∂(volume.restrict (cube 1)), 0 ≤ u ε x) ∧
          IsWeightedSupersolution (radialField d a) (cube 1) (u ε) (G ε)) ∧
        -- essinf_{cube(1/2)} u_ε is positive and does not depend on ε
        (∃ m : ℝ≥0∞, 0 < m ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
          essInfNonneg (cube (1 / 2)) (u ε) = m) ∧
        -- (11.19): for every η > η_c = r*/2 the weak Harnack ratio tends to ∞
        ∀ η : ℝ, rStar d q t / 2 < η →
          Tendsto (fun ε : ℝ =>
            normalizedLpMoment η (cube (5 / 8)) (u ε) /
              essInfNonneg (cube (1 / 2)) (u ε))
            (𝓝[>] 0) (𝓝 ⊤) := by
  sorry

end CoarseDeGiorgiAudit.SharpnessWeakHarnack
