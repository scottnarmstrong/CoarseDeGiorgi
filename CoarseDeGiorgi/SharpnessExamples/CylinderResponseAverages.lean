import CoarseDeGiorgi.SharpnessExamples.CylinderResponseDefs
import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra

/-! # Coefficient averages for the anisotropic cylinder -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A cell fraction always lies in [0,1]. -/
theorem cylinderResponseFraction_bounds {d : ℕ} {V : Set (Vec d)} (hV : volume V ≠ ⊤)
    (epsilon : ℝ) : 0 ≤ cylinderResponseFraction V epsilon ∧ cylinderResponseFraction V epsilon ≤ 1 := by
  rw [cylinderResponseFraction_eq_volume]
  have hint : volume (V ∩ responseCylinder epsilon) ≠ ⊤ :=
    ne_top_of_le_ne_top hV (measure_mono Set.inter_subset_left)
  have hle : (volume (V ∩ responseCylinder epsilon)).toReal ≤ (volume V).toReal :=
    ENNReal.toReal_mono hV (measure_mono Set.inter_subset_left)
  constructor
  · positivity
  · by_cases hz : (volume V).toReal = 0
    · simp only [hz, div_zero, zero_le_one]
    · exact (div_le_one (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz))).2 hle

/-- Averaging the two values c₁ and c₀ gives c₀+(c₁-c₀)f. -/
theorem cylinder_average_scalar {d : ℕ} {V : Set (Vec d)}
    (hV : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0)
    (epsilon c₁ c₀ : ℝ) :
    volumeAverage V (fun x : Vec d => if x ∈ responseCylinder epsilon then c₁ else c₀) =
      c₀ + (c₁ - c₀) * cylinderResponseFraction V epsilon := by
  classical
  let f : Vec d → ℝ := (responseCylinder epsilon).indicator (fun _ => 1)
  have hf : IntegrableOn f V volume :=
    (integrableOn_const hV).indicator (responseCylinder_measurable epsilon)
  have hc : IntegrableOn (fun _ : Vec d => c₀) V volume := integrableOn_const hV
  have heq : (fun x : Vec d => if x ∈ responseCylinder epsilon then c₁ else c₀) =
      (fun _ => c₀) + (c₁ - c₀) • f := by
    funext x
    dsimp [f]
    by_cases hx : x ∈ responseCylinder epsilon <;> simp [hx]
  rw [heq, volumeAverage_add hc (hf.smul _), volumeAverage_const hvol,
    volumeAverage_smul]
  rfl

/-- The average coefficient is diagonal with axial value 1+(A-1)f and
transverse value 1-(1-b)f. -/
theorem cylinderCoefficient_average {d : ℕ} {V : Set (Vec d)}
    (hV : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0)
    (epsilon parallel perpendicular : ℝ) :
    volumeAverageMat V (cylinderCoefficient epsilon parallel perpendicular) =
      cylinderDiagonal (1 + (parallel - 1) * cylinderResponseFraction V epsilon)
        (1 + (perpendicular - 1) * cylinderResponseFraction V epsilon) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    change volumeAverage V (fun x => cylinderCoefficient epsilon parallel perpendicular x i i) = _
    have heq : (fun x : Vec d => cylinderCoefficient epsilon parallel perpendicular x i i) =
        (fun x => if x ∈ responseCylinder epsilon then
          (if i.val = 0 then parallel else perpendicular) else 1) := by
      funext x
      unfold cylinderCoefficient
      split_ifs <;> simp_all [cylinderDiagonal]
    rw [heq, cylinder_average_scalar hV hvol]
    simp only [cylinderDiagonal, Matrix.diagonal_apply_eq]
    split_ifs <;> rfl
  · have heq : (fun x : Vec d => cylinderCoefficient epsilon parallel perpendicular x i j) =
        fun _ => 0 := by
      funext x
      unfold cylinderCoefficient
      split_ifs <;> simp [cylinderDiagonal, hij]
    change volumeAverage V (fun x => cylinderCoefficient epsilon parallel perpendicular x i j) = _
    rw [heq]
    simp [volumeAverage, cylinderDiagonal, hij]

/-- The inverse average has the same formula with reciprocal conductivities. -/
theorem cylinderCoefficient_inverse_average {d : ℕ} {V : Set (Vec d)}
    (hV : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0) (epsilon : ℝ)
    {parallel perpendicular : ℝ} (hp : parallel ≠ 0) (ht : perpendicular ≠ 0) :
    volumeAverageMat V (fun x => (cylinderCoefficient epsilon parallel perpendicular x)⁻¹) =
      cylinderDiagonal (1 + (parallel⁻¹ - 1) * cylinderResponseFraction V epsilon)
        (1 + (perpendicular⁻¹ - 1) * cylinderResponseFraction V epsilon) := by
  simp_rw [cylinderCoefficient_inv epsilon hp ht]
  exact cylinderCoefficient_average hV hvol epsilon parallel⁻¹ perpendicular⁻¹

/-- The operator norm of a positive diagonal matrix is its largest diagonal
entry, witnessed by a coordinate attaining that entry. -/
theorem cylinderDiagonal_norm {d : ℕ} (i : Fin d) {parallel perpendicular M : ℝ}
    (hM : 0 ≤ M) (hp : |parallel| ≤ M) (ht : |perpendicular| ≤ M)
    (hi : (if i.val = 0 then parallel else perpendicular) = M) :
    ‖cylinderDiagonal (d := d) parallel perpendicular‖ = M := by
  rw [cylinderDiagonal, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg hM).2
    intro j
    simp only [Real.norm_eq_abs]
    split_ifs <;> assumption
  · have h := norm_le_pi_norm (fun j : Fin d => if j.val = 0 then parallel else perpendicular) i
    rw [hi, Real.norm_eq_abs, abs_of_nonneg hM] at h
    exact h

end

end CoarseDeGiorgi.SharpnessExamples
