import Mathlib
import CoarseDeGiorgiAudit.Defs
import CoarseDeGiorgiAudit.DefsCells
import CoarseDeGiorgiAudit.DefsResponses
import CoarseDeGiorgiAudit.Solution.BridgeChallengeLp
import CoarseDeGiorgiAudit.Solution.BridgeCells
import CoarseDeGiorgiAudit.Solution.ResponseQuadraticForms
import CoarseDeGiorgi.Statements.Harnack

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-!
# Theorem C: Harnack inequality (1.11)

Assume `d ≥ 3`, `1 < p,q`, `s,t > 0`, and
`θ = 1 − s − t − (d−1)(1/p+1/q)/2 > 0`. For a weighted coefficient field on
`cube 1` with `Λ_{s,1,p} < ∞` and `λ_{t,1,q} > 0`, every nonnegative weighted
solution on `cube 1` satisfies
`esssup_{cube(1/2)} u ≤ exp(C√Θ) essinf_{cube(1/2)} u`, where
`Θ = Λ_{s,1,p}/λ_{t,1,q}`.

Here `a(△)` is the upper response and `a_*⁻¹(△)` the inverse lower response of
each cell `△`, both defined below by polarization.
-/

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.Harnack

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

/-- A function in `IsSmoothCore` is `C^∞` on `V`, integrable on `V`, and has
finite weighted energy. -/
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

/-- The contrast (1.6): `Θ = Λ_{s,1,p}/λ_{t,1,q}`. -/
noncomputable def contrast {d : ℕ} (a : CoeffField d)
    (s t p q : ℝ) : ℝ≥0∞ :=
  upperMoment a s p / lowerMoment a t q


private theorem triangulation_eq_statement (d k : ℕ) :
    triangulation (d := d) k = CoarseDeGiorgi.triangulation k := rfl

private theorem responseIndex_eq (d k : ℕ) :
    SimplexIndex d k = CoarseDeGiorgiAudit.ResponseQuadraticForms.SimplexIndex d k := rfl

private def toResponseIndex {d k : ℕ} (η : SimplexIndex d k) :
    CoarseDeGiorgiAudit.ResponseQuadraticForms.SimplexIndex d k :=
  (responseIndex_eq d k) ▸ η

private theorem upperResponse_eq_statement {d : ℕ} (a : CoeffField d)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (k : ℕ) (η : SimplexIndex d k) :
    upperResponse a (simplexCell k η) =
      CoarseDeGiorgi.upperResponseOnCell k a ha
        (CoarseDeGiorgiAudit.ResponseQuadraticForms.simplexIndexToStatement
          (toResponseIndex η)) := by
  let ηR := toResponseIndex η
  have hCell : simplexCell k η =
      CoarseDeGiorgiAudit.ResponseQuadraticForms.simplexCell k ηR := by
    dsimp [ηR, toResponseIndex]
    cases responseIndex_eq d k
    rfl
  have hLocal : upperResponse a (simplexCell k η) =
      CoarseDeGiorgiAudit.ResponseQuadraticForms.upperResponse a
        (CoarseDeGiorgiAudit.ResponseQuadraticForms.simplexCell k ηR) := by
    rw [← hCell]
    rfl
  have haR : CoarseDeGiorgiAudit.ResponseQuadraticForms.IsWeightedCoeffOn
      (CoarseDeGiorgi.originCube 1) a := by
    change CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a
    exact ha
  exact hLocal.trans
    (CoarseDeGiorgiAudit.ResponseQuadraticForms.upperResponseOnCell_eq
      a haR k ηR)

private theorem lowerResponseInv_eq_statement {d : ℕ} (a : CoeffField d)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (k : ℕ) (η : SimplexIndex d k) :
    lowerResponseInv a (simplexCell k η) =
      CoarseDeGiorgi.lowerResponseInvOnCell k a ha
        (CoarseDeGiorgiAudit.ResponseQuadraticForms.simplexIndexToStatement
          (toResponseIndex η)) := by
  let ηR := toResponseIndex η
  have hCell : simplexCell k η =
      CoarseDeGiorgiAudit.ResponseQuadraticForms.simplexCell k ηR := by
    dsimp [ηR, toResponseIndex]
    cases responseIndex_eq d k
    rfl
  have hLocal : lowerResponseInv a (simplexCell k η) =
      CoarseDeGiorgiAudit.ResponseQuadraticForms.lowerResponseInv a
        (CoarseDeGiorgiAudit.ResponseQuadraticForms.simplexCell k ηR) := by
    rw [← hCell]
    rfl
  have haR : CoarseDeGiorgiAudit.ResponseQuadraticForms.IsWeightedCoeffOn
      (CoarseDeGiorgi.originCube 1) a := by
    change CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a
    exact ha
  exact hLocal.trans
    (CoarseDeGiorgiAudit.ResponseQuadraticForms.lowerResponseInvOnCell_eq
      a haR k ηR)

private theorem upperCellAverage_eq_statement {d : ℕ} (a : CoeffField d)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (k : ℕ) (p : ℝ) :
    ((triangulation (d := d) k).attach.sum fun η =>
      Real.rpow ‖upperResponse a (simplexCell k ⟨η.1, η.2⟩)‖ p) /
        ((triangulation (d := d) k).card : ℝ) =
      CoarseDeGiorgi.upperCellAverage a ha k p := by
  classical
  unfold CoarseDeGiorgi.upperCellAverage
  change ((CoarseDeGiorgi.triangulation (d := d) k).attach.sum fun η =>
      Real.rpow ‖upperResponse a
        (simplexCell k ⟨η.1, η.2⟩)‖ p) /
        ((CoarseDeGiorgi.triangulation (d := d) k).card : ℝ) =
    ((CoarseDeGiorgi.triangulation (d := d) k).attach.sum fun η =>
      Real.rpow ‖CoarseDeGiorgi.upperResponseOnCell k a ha
        ⟨η.1, η.2⟩‖ p) /
        ((CoarseDeGiorgi.triangulation (d := d) k).card : ℝ)
  congr 1
  apply Finset.sum_congr rfl
  intro η hη
  let ηH : SimplexIndex d k := ⟨η.1,
    (triangulation_eq_statement d k).symm ▸ η.2⟩
  let ηRoot : CoarseDeGiorgi.SimplexIndex d k := ⟨η.1, η.2⟩
  have hResp := upperResponse_eq_statement a ha k ηH
  have hIndex :
      CoarseDeGiorgiAudit.ResponseQuadraticForms.simplexIndexToStatement
        (toResponseIndex ηH) = ηRoot := by
    apply Subtype.ext
    rfl
  rw [hIndex] at hResp
  exact congrArg (fun A : Mat d => Real.rpow ‖A‖ p) hResp

private theorem lowerCellAverage_eq_statement {d : ℕ} (a : CoeffField d)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (k : ℕ) (q : ℝ) :
    ((triangulation (d := d) k).attach.sum fun η =>
      Real.rpow ‖lowerResponseInv a (simplexCell k ⟨η.1, η.2⟩)‖ q) /
        ((triangulation (d := d) k).card : ℝ) =
      CoarseDeGiorgi.lowerCellAverage a ha k q := by
  classical
  unfold CoarseDeGiorgi.lowerCellAverage
  change ((CoarseDeGiorgi.triangulation (d := d) k).attach.sum fun η =>
      Real.rpow ‖lowerResponseInv a
        (simplexCell k ⟨η.1, η.2⟩)‖ q) /
        ((CoarseDeGiorgi.triangulation (d := d) k).card : ℝ) =
    ((CoarseDeGiorgi.triangulation (d := d) k).attach.sum fun η =>
      Real.rpow ‖CoarseDeGiorgi.lowerResponseInvOnCell k a ha
        ⟨η.1, η.2⟩‖ q) /
        ((CoarseDeGiorgi.triangulation (d := d) k).card : ℝ)
  congr 1
  apply Finset.sum_congr rfl
  intro η hη
  let ηH : SimplexIndex d k := ⟨η.1,
    (triangulation_eq_statement d k).symm ▸ η.2⟩
  let ηRoot : CoarseDeGiorgi.SimplexIndex d k := ⟨η.1, η.2⟩
  have hResp := lowerResponseInv_eq_statement a ha k ηH
  have hIndex :
      CoarseDeGiorgiAudit.ResponseQuadraticForms.simplexIndexToStatement
        (toResponseIndex ηH) = ηRoot := by
    apply Subtype.ext
    rfl
  rw [hIndex] at hResp
  exact congrArg (fun A : Mat d => Real.rpow ‖A‖ q) hResp

private theorem upperMoment_eq_statement {d : ℕ} (a : CoeffField d)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (s p : ℝ) (hs : 0 < s) (hp : 1 ≤ p) :
    upperMoment a s p = CoarseDeGiorgi.upperMoment a ha s p hs hp := by
  unfold upperMoment CoarseDeGiorgi.upperMoment
  simp_rw [upperCellAverage_eq_statement a ha]

private theorem lowerMoment_eq_statement {d : ℕ} (a : CoeffField d)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (t q : ℝ) (ht : 0 < t) (hq : 1 ≤ q) :
    lowerMoment a t q = CoarseDeGiorgi.lowerMoment a ha t q ht hq := by
  unfold lowerMoment CoarseDeGiorgi.lowerMoment
  simp_rw [lowerCellAverage_eq_statement a ha]

/-! ## Theorem -/

/-- For `d ≥ 3`, `1 < p,q`, `s,t > 0`, and `θ > 0`, there is
`C = C(d,p,q,s,t) ≥ 0` such that if `Λ_{s,1,p} < ∞` and `λ_{t,1,q} > 0`,
every nonnegative weighted solution on `cube 1` satisfies
`esssup_{cube(1/2)} u ≤ exp(C√Θ) essinf_{cube(1/2)} u`. -/
theorem harnack
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀
        -- coefficient field and response moments
        (a : CoeffField d), IsWeightedCoeffOn (cube 1) a →
        upperMoment a s p < ⊤ →
        0 < lowerMoment a t q →
        ∀
          -- nonnegative weighted solution
        (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (cube 1)), 0 ≤ u x) →
          IsWeightedSolution a (cube 1) u G →
          -- conclusion
          eLpNorm u ⊤ (volume.restrict (cube (1 / 2))) ≤
            ENNReal.ofReal
              (Real.exp (C * Real.sqrt (contrast a s t p q).toReal)) *
              essInfNonneg (cube (1 / 2)) u := by
  have hθRoot : 0 < CoarseDeGiorgi.paramTheta d p q s t := by
    simpa [paramTheta, CoarseDeGiorgi.paramTheta] using hθ
  obtain ⟨C, hC, hroot⟩ :=
    CoarseDeGiorgi.harnack d hd p q s t hp hq hs ht hθRoot
  refine ⟨C, hC, ?_⟩
  intro a ha hUpper hLower u G hu hsol
  have haOld : CoarseDeGiorgiAudit.HarnackLpLq.IsWeightedCoeffOn
      (CoarseDeGiorgiAudit.HarnackLpLq.cube 1) a := by
    exact ha
  have haAudit : CoarseDeGiorgiAudit.IsWeightedCoeffOn
      (CoarseDeGiorgiAudit.originCube 1) a := by
    have h := (CoarseDeGiorgiAudit.HarnackLpLq.isWeightedCoeffOn_iff
      (CoarseDeGiorgiAudit.HarnackLpLq.cube 1) a).mp haOld
    simpa only [CoarseDeGiorgiAudit.HarnackLpLq.cube_eq] using h
  have haRoot : CoarseDeGiorgi.IsWeightedCoeffOn
      (CoarseDeGiorgi.originCube 1) a :=
    (CoarseDeGiorgiAudit.isWeightedCoeffOn_iff
      (CoarseDeGiorgiAudit.originCube 1) a).mp haAudit
  have hUpperRoot :
      CoarseDeGiorgi.upperMoment a haRoot s p hs hp.le < ⊤ := by
    rw [← upperMoment_eq_statement a haRoot s p hs hp.le]
    exact hUpper
  have hLowerRoot :
      0 < CoarseDeGiorgi.lowerMoment a haRoot t q ht hq.le := by
    rw [← lowerMoment_eq_statement a haRoot t q ht hq.le]
    exact hLower
  have hcontrast : contrast a s t p q =
      CoarseDeGiorgi.contrast a haRoot s t p q hs ht hp.le hq.le := by
    simp only [contrast, CoarseDeGiorgi.contrast,
      upperMoment_eq_statement a haRoot s p hs hp.le,
      lowerMoment_eq_statement a haRoot t q ht hq.le]
  have huRoot :
      ∀ᵐ x ∂(volume.restrict (CoarseDeGiorgi.originCube 1)), 0 ≤ u x := by
    simpa [cube, CoarseDeGiorgiAudit.originCube,
      CoarseDeGiorgi.originCube] using hu
  have hsolOld : CoarseDeGiorgiAudit.HarnackLpLq.IsWeightedSolution a
      (CoarseDeGiorgiAudit.HarnackLpLq.cube 1) u G := by
    exact hsol
  have hsolAudit : CoarseDeGiorgiAudit.IsWeightedSolution a
      (CoarseDeGiorgiAudit.originCube 1) u G := by
    have h := (CoarseDeGiorgiAudit.HarnackLpLq.isWeightedSolution_iff
      a (CoarseDeGiorgiAudit.HarnackLpLq.cube 1) u G).mp hsolOld
    simpa only [CoarseDeGiorgiAudit.HarnackLpLq.cube_eq] using h
  have hsolRoot : CoarseDeGiorgi.IsWeightedSolution a
      (CoarseDeGiorgi.originCube 1) u G :=
    (CoarseDeGiorgiAudit.isWeightedSolution_iff
      a (CoarseDeGiorgiAudit.originCube 1) u G).mp hsolAudit
  have hroot_bound := hroot a haRoot hUpperRoot hLowerRoot u G huRoot hsolRoot
  simpa [hcontrast, cube, CoarseDeGiorgiAudit.originCube,
    CoarseDeGiorgi.originCube, essInfNonneg,
    CoarseDeGiorgi.nonnegativeEssInf] using hroot_bound

end CoarseDeGiorgiAudit.Harnack
