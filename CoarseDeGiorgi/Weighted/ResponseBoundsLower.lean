module

public import CoarseDeGiorgi.Weighted.ResponseBounds
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Matrix inversion is measurable, including singular matrices. -/
theorem response_matrix_inverse_measurable : Measurable (fun A : Mat d => A⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul
    continuous_id.matrix_adjugate.measurable

/-- The inverse coefficient satisfies the same integrability conditions. -/
theorem response_inverse_coefficient (ha : IsWeightedCoeffOn V a) :
    IsWeightedCoeffOn V (fun x => (a x)⁻¹) := by
  let : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  let : TopologicalSpace.PseudoMetrizableSpace (Mat d) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  refine ⟨(response_matrix_inverse_measurable.comp_aemeasurable
    ha.1.aemeasurable).aestronglyMeasurable, ha.2.1.mono (fun _ h => h.inv),
    ha.2.2.2, ?_⟩
  apply ha.2.2.1.congr
  filter_upwards [ha.2.1] with x hx
  exact congrArg Matrix.trace
    (Matrix.nonsing_inv_nonsing_inv (A := a x)
      ((Matrix.isUnit_iff_isUnit_det (A := a x)).mp hx.isUnit)).symm

/-- Pointwise square completion for the lower objective. -/
theorem lower_square_completion (A : Mat d) (hA : A.PosDef) (e g : Vec d) :
    -vecDot g (matVecMul A g) + 2 * vecDot e g =
      vecDot e (matVecMul A⁻¹ e) -
        vecDot (g - matVecMul A⁻¹ e) (matVecMul A (g - matVecMul A⁻¹ e)) := by
  have he : matVecMul A (matVecMul A⁻¹ e) = e := by
    rw [matVecMul_mul, Matrix.mul_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det (A := A)).mp hA.isUnit)]
    exact matVecMul_one e
  have hs : A.IsSymm := by simpa [Matrix.IsSymm, Matrix.IsHermitian] using hA.1
  have hu := upper_square_completion A hs (matVecMul A⁻¹ e) g
  rw [vecDot_matVecMul_comm_of_isSymm hs (matVecMul A⁻¹ e) g, he,
    vecDot_comm g e, vecDot_comm (matVecMul A⁻¹ e) e] at hu
  exact hu

/-- The lower objective is integrable for a literal weighted-space pair. -/
theorem lower_response_objective_integrable (hV : IsOpen V)
    (ha : IsWeightedCoeffOn V a) (e : Vec d)
    {w : Vec d → ℝ} {G : Vec d → Vec d} (hw : MemH1a a V w G) :
    IntegrableOn (fun x => -vecDot (G x) (matVecMul (a x) (G x)) +
      2 * vecDot e (G x)) V := by
  have hG := GradientCore.integrable ha (memH1aEnergyField hV ha hw)
  have hp := (responseAffine e).integrable_comp hG
  exact (quadratic_integrable ha hw.2.1 (hw.energy_lt_top hV ha)).neg.add
    (hp.const_mul 2)

/-- Averaged square completion bounds each lower competitor. -/
theorem lower_response_objective_le (hV : IsOpen V)
    (ha : IsWeightedCoeffOn V a) (e : Vec d)
    {w : Vec d → ℝ} {G : Vec d → Vec d} (hw : MemH1a a V w G) :
    volumeAverage V (fun x => -vecDot (G x) (matVecMul (a x) (G x)) +
      2 * vecDot e (G x)) ≤
        volumeAverage V (fun x => vecDot e (matVecMul ((a x)⁻¹) e)) := by
  unfold volumeAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply integral_mono_ae (lower_response_objective_integrable hV ha e hw)
    (GradientCore.quadratic_integrable (response_inverse_coefficient ha)
      (constantEnergyField (response_inverse_coefficient ha) e))
  filter_upwards [ha.2.1] with x hx
  rw [lower_square_completion (a x) hx e (G x)]
  apply sub_le_self
  simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
    hx.posSemidef.dotProduct_mulVec_nonneg (x := G x - matVecMul ((a x)⁻¹) e)

/-- Source e.lower.coefficient.bound in directional form, for every dimension. -/
theorem lower_coefficient_bound (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    lowerDirectionalResponse a V e ≤
      ((vecDot e (matVecMul (volumeAverageMat V (fun x => (a x)⁻¹)) e) : ℝ) : EReal) := by
  rw [← response_quadratic_average (response_inverse_coefficient ha) e]
  unfold lowerDirectionalResponse
  refine iSup_le fun w => iSup_le fun G => iSup_le fun hw => ?_
  exact EReal.coe_le_coe_iff.mpr (lower_response_objective_le hV ha e hw.1)


end CoarseDeGiorgi.Weighted
