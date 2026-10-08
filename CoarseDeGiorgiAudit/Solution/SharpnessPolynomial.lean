import Mathlib
import CoarseDeGiorgi.Statements.OptimalPowers
import CoarseDeGiorgiAudit.Solution.BridgeBesov
import CoarseDeGiorgiAudit.Solution.ResponseQuadraticForms

/-!
# Proposition 11.2 (Sharpness of the polynomial bound)

Let `d ≥ 3`, `p,q > 1`, and `s,t > 0`, and suppose
`θ = 1 − s − t − (d−1)(1/p+1/q)/2 > 0`. There are total families `a_ε`, `u_ε`,
and `G_ε` such that every `a_ε` is a weighted coefficient on `originCube 1`;
for `0 < ε < 1/8`, it is symmetric and uniformly elliptic with constants that
may depend on `ε`, `u_ε` is a weighted solution, and `(u_ε)₊` is a weighted
subsolution. The trace integrals are bounded uniformly in `ε`. The response
moments and contrast satisfy `Λ_ε ≍ ε^(−2θ)`, `λ_ε ≍ 1`, and
`Θ_ε ≍ ε^(−2θ)`. On `1/2 ≤ ρ < 1`,
`‖(u_ε)₊‖_{L∞(ρ□₀)} = 1 + ρ²/4`; for each `η > 0`, uniformly for
`1/2 < R ≤ 1`, `‖(u_ε)₊‖_{L^η(R□₀)} ≍ ε^((d−1)/η)`. For every admissible
`ρ,R,η` and every `υ < (d−1)/(2ηθ)`, the normalized ratio in the theorem
tends to `⊤` as `ε → 0⁺`. Weighted solutions and subsolutions use the
smooth-core closure `H¹ₐ` and their weak flux equations against smooth compactly
supported tests.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.SharpnessPolynomial

attribute [-instance] Homogenization.instMeasurableSpaceVec
attribute [-instance] Homogenization.instMeasurableSpaceMat
attribute [-instance] Homogenization.instMeasurableSpaceCoeffField

/-! ## Ambient space and cubes -/

/-- Vectors in the ambient space `ℝᵈ`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on ambient vectors. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The open cube `(-ρ/2, ρ/2)ᵈ`. -/
def originCube {d : ℕ} (ρ : ℝ) : Set (Vec d) :=
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


/-! ## Weighted subsolutions -/

/-- A subsolution has nonpositive flux pairing with every nonnegative smooth,
compactly supported test: `∫_V ∇φ · a∇u ≤ 0`. -/
noncomputable def IsWeightedSubsolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) →
      Integrable
        (fun x => smoothGrad φ x ⬝ᵥ ((a x) *ᵥ G x))
        (volume.restrict V) ∧
      ∫ x in V, smoothGrad φ x ⬝ᵥ ((a x) *ᵥ G x) ∂volume ≤ 0

/-- The positive part `u₊ = max(u, 0)`. -/
def positivePart {d : ℕ} (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => max (u x) 0

/-! ## Norms, moments, and parameters -/

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

/-- The paper's upper response `a(V)` (Prop. 2.2, (2.6)) is the symmetric matrix
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



private theorem paramTheta_eq (d : ℕ) (p q s t : ℝ) :
    paramTheta d p q s t = CoarseDeGiorgi.paramTheta d p q s t := rfl

private theorem positivePart_eq {d : ℕ} (u : Vec d → ℝ) :
    positivePart u = CoarseDeGiorgi.positivePart u := rfl

private theorem matVecMul_to_matrix {d : ℕ} (A : Mat d) (x : Vec d) :
    Homogenization.matVecMul A x = A *ᵥ x := by
  ext i
  simp only [Homogenization.matVecMul, Matrix.mulVec_apply_eq_sum]

private theorem vecDot_to_dotProduct {d : ℕ} (x y : Vec d) :
    Homogenization.vecDot x y = x ⬝ᵥ y := by
  simp [Homogenization.vecDot, dotProduct]

private theorem contrast_eq_statement {d : ℕ} (a : CoeffField d)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (s t p q : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hp : 1 ≤ p) (hq : 1 ≤ q) :
    contrast a s t p q =
      CoarseDeGiorgi.contrast a ha s t p q hs ht hp hq := by
  simp only [contrast, CoarseDeGiorgi.contrast,
    upperMoment_eq_statement a ha s p hs hp,
    lowerMoment_eq_statement a ha t q ht hq]

/-! ## Proposition 11.2 -/

/-- **Proposition 11.2 (Sharpness of the polynomial bound).** For `d ≥ 3`,
`p,q > 1`, `s,t > 0`, and `θ = 1 − s − t − (d−1)(1/p+1/q)/2 > 0`, there are
total families `a_ε`, `u_ε`, and `G_ε` with weighted coefficients for all `ε`;
for `0 < ε < 1/8`, their fields are symmetric and uniformly elliptic with
ε-dependent constants, `u_ε` is a weighted solution, and `(u_ε)₊` is a weighted
subsolution. Their trace integrals are bounded uniformly in `ε`, their upper
moment, lower moment, and contrast have respective orders
`ε^(−2θ)`, `1`, and `ε^(−2θ)`, and `(u_ε)₊` has the stated `L∞` height and
`L^η` size. For every admissible `ρ,R,η` and every
`υ < (d−1)/(2ηθ)`, the normalized ratio tends to `⊤` as `ε → 0⁺`. -/
theorem sharpnessPolynomial
    -- parameters
    (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ (a : ℝ → CoeffField d) (u : ℝ → Vec d → ℝ) (G : ℝ → Vec d → Vec d),
      (∀ ε, IsWeightedCoeffOn (originCube 1) (a ε)) ∧
      -- each field is symmetric and uniformly elliptic, with constants depending on ε
      (∀ ε, 0 < ε → ε < 1 / 8 → ∃ lam Λ : ℝ, 0 < lam ∧
        ∀ᵐ x ∂(volume.restrict (originCube 1)), (a ε x).IsHermitian ∧
          ∀ ξ : Vec d, lam * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ ((a ε x) *ᵥ ξ) ∧
            ξ ⬝ᵥ ((a ε x) *ᵥ ξ) ≤ Λ * (ξ ⬝ᵥ ξ)) ∧
      -- u_ε solves the equation and its positive part is a subsolution
      (∀ ε, 0 < ε → ε < 1 / 8 →
        IsWeightedSolution (a ε) (originCube 1) (u ε) (G ε) ∧
        ∃ G' : Vec d → Vec d,
          IsWeightedSubsolution (a ε) (originCube 1) (positivePart (u ε)) G') ∧
      -- trace integrals bounded uniformly in ε
      (∃ C : ℝ, ∀ ε, 0 < ε → ε < 1 / 8 →
        ∫ x in originCube 1, ((a ε x).trace + ((a ε x)⁻¹).trace) ≤ C) ∧
      -- the moments: Λ_ε ≍ ε^{-2θ}, λ_ε ≍ 1, Θ_ε ≍ ε^{-2θ}
      (∃ C : ℝ, 1 ≤ C ∧ ∀ ε, 0 < ε → ε < 1 / 8 →
        ENNReal.ofReal (C⁻¹ * ε ^ (-(2 * paramTheta d p q s t))) ≤
            upperMoment (a ε) s p ∧
          upperMoment (a ε) s p ≤
            ENNReal.ofReal (C * ε ^ (-(2 * paramTheta d p q s t))) ∧
          ENNReal.ofReal C⁻¹ ≤ lowerMoment (a ε) t q ∧
          lowerMoment (a ε) t q ≤ ENNReal.ofReal C ∧
          ENNReal.ofReal (C⁻¹ * ε ^ (-(2 * paramTheta d p q s t))) ≤
            contrast (a ε) s t p q ∧
          contrast (a ε) s t p q ≤
            ENNReal.ofReal (C * ε ^ (-(2 * paramTheta d p q s t)))) ∧
      -- the height of the positive part
      (∀ ε, 0 < ε → ε < 1 / 8 → ∀ ρ : ℝ, 1 / 2 ≤ ρ → ρ < 1 →
        eLpNorm (positivePart (u ε)) ⊤ (volume.restrict (originCube ρ)) =
          ENNReal.ofReal (1 + ρ ^ 2 / 4)) ∧
      -- the L^η size: ≍ ε^{(d-1)/η}, uniformly in ε and R
      (∀ η : ℝ, 0 < η → ∃ C : ℝ, 1 ≤ C ∧
        ∀ ε, 0 < ε → ε < 1 / 8 → ∀ R : ℝ, 1 / 2 < R → R ≤ 1 →
          ENNReal.ofReal (C⁻¹ * ε ^ (((d : ℝ) - 1) / η)) ≤
            eLpNorm (positivePart (u ε)) (ENNReal.ofReal η)
              (volume.restrict (originCube R)) ∧
          eLpNorm (positivePart (u ε)) (ENNReal.ofReal η)
              (volume.restrict (originCube R)) ≤
            ENNReal.ofReal (C * ε ^ (((d : ℝ) - 1) / η))) ∧
      -- for every smaller power, the ratio tends to infinity at ε = 0
      (∀ ρ R η υ : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 → 0 < η → η ≤ 2 →
        υ < ((d : ℝ) - 1) / (2 * η * paramTheta d p q s t) →
        Tendsto
          (fun ε =>
            eLpNorm (positivePart (u ε)) ⊤ (volume.restrict (originCube ρ)) /
              ((contrast (a ε) s t p q).rpow υ *
                eLpNorm (positivePart (u ε)) (ENNReal.ofReal η)
                  (volume.restrict (originCube R))))
          (𝓝[>] 0) (𝓝 ⊤)) := by
  classical
  have hθroot : 0 < CoarseDeGiorgi.paramTheta d p q s t := by
    simpa only [paramTheta, CoarseDeGiorgi.paramTheta] using _hθ
  obtain ⟨a, u, G, ha, hEll, hsol, hTrace, hMom, hHeight, hLeta, hRatio⟩ :=
    CoarseDeGiorgi.optimal_powers d _hd p q s t hp hq hs ht hθroot
  refine ⟨a, u, G, ?_, ?_, ?_, hTrace, ?_, ?_, ?_, ?_⟩
  · intro ε
    change CoarseDeGiorgi.IsWeightedCoeffOn
      (CoarseDeGiorgi.originCube 1) (a ε)
    exact ha ε
  · intro ε hε0 hε8
    obtain ⟨lam, Λ, hlam, hEllε⟩ := hEll ε hε0 hε8
    refine ⟨lam, Λ, hlam, ?_⟩
    filter_upwards [hEllε] with x hx
    refine ⟨hx.1, ?_⟩
    intro ξ
    obtain ⟨hlo, hhi⟩ := hx.2 ξ
    refine ⟨?_, ?_⟩
    · rw [vecDot_to_dotProduct, matVecMul_to_matrix] at hlo
      exact hlo
    · rw [vecDot_to_dotProduct, matVecMul_to_matrix] at hhi
      exact hhi
  · intro ε hε0 hε8
    obtain ⟨hsolε, G', hsubε⟩ := hsol ε hε0 hε8
    refine ⟨?_, G', ?_⟩
    · change CoarseDeGiorgi.IsWeightedSolution
        (a ε) (CoarseDeGiorgi.originCube 1) (u ε) (G ε)
      exact hsolε
    · change CoarseDeGiorgi.IsWeightedSubsolution
        (a ε) (CoarseDeGiorgi.originCube 1)
        (CoarseDeGiorgi.positivePart (u ε)) G'
      simpa only [positivePart_eq] using hsubε
  · obtain ⟨C, hC, hMom⟩ := hMom
    refine ⟨C, hC, ?_⟩
    intro ε hε0 hε8
    obtain ⟨hUL, hUU, hLL, hLU, hCL, hCU⟩ := hMom ε hε0 hε8
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [paramTheta_eq,
        ← upperMoment_eq_statement (a ε) (ha ε) s p hs hp.le] using hUL
    · simpa only [paramTheta_eq,
        ← upperMoment_eq_statement (a ε) (ha ε) s p hs hp.le] using hUU
    · simpa only [paramTheta_eq,
        ← lowerMoment_eq_statement (a ε) (ha ε) t q ht hq.le] using hLL
    · simpa only [paramTheta_eq,
        ← lowerMoment_eq_statement (a ε) (ha ε) t q ht hq.le] using hLU
    · simpa only [paramTheta_eq,
        ← contrast_eq_statement (a ε) (ha ε) s t p q hs ht hp.le hq.le] using hCL
    · simpa only [paramTheta_eq,
        ← contrast_eq_statement (a ε) (ha ε) s t p q hs ht hp.le hq.le] using hCU
  · intro ε hε0 hε8 ρ hρ0 hρ1
    simpa only [positivePart_eq, originCube, CoarseDeGiorgi.originCube]
      using hHeight ε hε0 hε8 ρ hρ0 hρ1
  · intro η hη
    obtain ⟨C, hC, hLeta⟩ := hLeta η hη
    refine ⟨C, hC, ?_⟩
    intro ε hε0 hε8 R hR0 hR1
    obtain ⟨hlo, hhi⟩ := hLeta ε hε0 hε8 R hR0 hR1
    exact ⟨by simpa only [positivePart_eq, originCube, CoarseDeGiorgi.originCube] using hlo,
      by simpa only [positivePart_eq, originCube, CoarseDeGiorgi.originCube] using hhi⟩
  · intro ρ R η υ hρ0 hρR hR1 hη0 hη2 hυ
    have hcontrast (ε : ℝ) :=
      contrast_eq_statement (a ε) (ha ε) s t p q hs ht hp.le hq.le
    simpa only [paramTheta_eq, positivePart_eq, originCube, CoarseDeGiorgi.originCube,
      ← hcontrast] using
      hRatio ρ R η υ hρ0 hρR hR1 hη0 hη2 hυ

end CoarseDeGiorgiAudit.SharpnessPolynomial
