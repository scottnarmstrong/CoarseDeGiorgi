module

public import Mathlib

/-!
# Response quadratic forms

The matrices `a(△)` and `a_*⁻¹(△)` are defined by polarizing the upper and lower
directional responses. This theorem certifies that both matrices are positive definite
and that their quadratic forms equal the corresponding directional responses.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.ResponseQuadraticForms

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

/-- Weighted energy `∫_U ∇w · a ∇w`, recorded as an extended nonnegative real. -/
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

/-- A weighted solution has zero flux pairing with every smooth compactly
supported test: `∫_V ∇φ · a∇w = 0`. -/
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

/-! ## Cell geometry and directional responses -/

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

/-- Upper directional response: the supremum of `⨍_V (−∇w·a∇w + 2e·a∇w)`.
The supremum ranges over weighted solutions and their weak gradients. -/
noncomputable def upperDirectionalResponse {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (e : Vec d) : EReal :=
  ⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
    (_ : IsWeightedSolution a V w G),
    ((averageOn V
      (fun x =>
        - (G x ⬝ᵥ (a x *ᵥ G x)) +
          2 * (e ⬝ᵥ (a x *ᵥ G x))) : ℝ) : EReal)

/-- Lower directional response: the supremum of `⨍_V (−∇w·a∇w + 2e·∇w)`.
The supremum ranges over weighted solutions and their weak gradients. -/
noncomputable def lowerDirectionalResponse {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (e : Vec d) : EReal :=
  ⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
    (_ : IsWeightedSolution a V w G),
    ((averageOn V
      (fun x =>
        - (G x ⬝ᵥ (a x *ᵥ G x)) +
          2 * (e ⬝ᵥ G x)) : ℝ) : EReal)

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

/-! ## Theorem -/

/-- Every weighted coefficient field on `cube 1` has upper and lower
positive-definite response matrices on all simplex cells, whose quadratic forms
equal their directional responses. -/
theorem responseQuadraticForms (d : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (cube 1) a) :
    ∀ k (η : SimplexIndex d k),
      ((upperResponse a (simplexCell k η)).PosDef ∧
        ∀ e : Vec d,
          ((e ⬝ᵥ (upperResponse a (simplexCell k η) *ᵥ e) : ℝ) : EReal) =
            upperDirectionalResponse a (simplexCell k η) e) ∧
      ((lowerResponseInv a (simplexCell k η)).PosDef ∧
        ∀ e : Vec d,
          ((e ⬝ᵥ (lowerResponseInv a (simplexCell k η) *ᵥ e) : ℝ) : EReal) =
            lowerDirectionalResponse a (simplexCell k η) e) := by
  sorry

end CoarseDeGiorgiAudit.ResponseQuadraticForms
