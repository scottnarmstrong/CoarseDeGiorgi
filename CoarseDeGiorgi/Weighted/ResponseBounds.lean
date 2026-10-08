import CoarseDeGiorgi.Weighted.UpperResponseAffine
import CoarseDeGiorgi.Weighted.LowerResponseZero
import CoarseDeGiorgi.Statements.UpperDirectionalResponseSol
import CoarseDeGiorgi.Statements.UpperDirectionalResponseSub

/-! Coefficient bounds for the literal directional responses. -/

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory
open scoped BigOperators

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Pointwise square completion for the upper objective. -/
theorem upper_square_completion (A : Mat d) (hA : A.IsSymm) (e g : Vec d) :
    -vecDot g (matVecMul A g) + 2 * vecDot e (matVecMul A g) =
      vecDot e (matVecMul A e) - vecDot (g - e) (matVecMul A (g - e)) := by
  have hc := vecDot_matVecMul_comm_of_isSymm hA g e
  simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg,
    vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right]
  rw [hc]
  ring

/-- A solution satisfies the subsolution testing inequality. -/
theorem response_solution_subsolution {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : IsWeightedSolution a V w G) : IsWeightedSubsolution a V w G := by
  refine ⟨hw.1, ?_⟩
  intro φ hφ hc hs _
  exact ⟨(hw.2 φ hφ hc hs).1, (hw.2 φ hφ hc hs).2.le⟩

/-- Zero is a competitor in the solution supremum, in every dimension. -/
theorem upperDirectionalResponseSol_nonneg (a : CoeffField d) (V : Set (Vec d))
    (e : Vec d) : 0 ≤ upperDirectionalResponseSol a V e := by
  have hz : ((volumeAverage V (fun x =>
      -vecDot ((0 : Vec d → Vec d) x) (matVecMul (a x) 0) +
        2 * vecDot e (matVecMul (a x) 0)) : ℝ) : EReal) = 0 := by
    simp [vecDot, matVecMul, volumeAverage]
  rw [← hz]
  exact le_iSup_of_le (0 : Vec d → ℝ) (le_iSup_of_le (0 : Vec d → Vec d)
    (le_iSup_of_le (lower_zero_solution a V) le_rfl))

/-- Inclusion of the admissible classes orders the suprema. -/
theorem upperDirectionalResponseSol_le_sub (a : CoeffField d) (V : Set (Vec d))
    (e : Vec d) : upperDirectionalResponseSol a V e ≤ upperDirectionalResponseSub a V e := by
  unfold upperDirectionalResponseSol upperDirectionalResponseSub
  refine iSup_le fun w => iSup_le fun G => iSup_le fun hw => ?_
  exact le_iSup_of_le w (le_iSup_of_le G
    (le_iSup_of_le (response_solution_subsolution hw) le_rfl))

/-- The upper objective is integrable for every literal weighted-space pair. -/
theorem upper_response_objective_integrable (hV : IsOpen V)
    (ha : IsWeightedCoeffOn V a) (e : Vec d)
    {w : Vec d → ℝ} {G : Vec d → Vec d} (hw : MemH1a a V w G) :
    IntegrableOn (fun x => -vecDot (G x) (matVecMul (a x) (G x)) +
      2 * vecDot e (matVecMul (a x) (G x))) V := by
  have hE := hw.energy_lt_top hV ha
  have hq := quadratic_integrable ha hw.2.1 hE
  have hp := (pairing_integrable_and_bound ha aestronglyMeasurable_const hw.2.1
    (GradientCore.energy_lt_top ha (constantEnergyField ha e)) hE).1
  exact hq.neg.add (hp.const_mul 2)

/-- Pointwise square completion passes to the averaged upper objective. -/
theorem upper_response_objective_le (hV : IsOpen V)
    (ha : IsWeightedCoeffOn V a) (e : Vec d)
    {w : Vec d → ℝ} {G : Vec d → Vec d} (hw : MemH1a a V w G) :
    volumeAverage V (fun x => -vecDot (G x) (matVecMul (a x) (G x)) +
      2 * vecDot e (matVecMul (a x) (G x))) ≤
        volumeAverage V (fun x => vecDot e (matVecMul (a x) e)) := by
  unfold volumeAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply integral_mono_ae (upper_response_objective_integrable hV ha e hw)
    (GradientCore.quadratic_integrable ha (constantEnergyField ha e))
  filter_upwards [ha.2.1] with x hx
  rw [upper_square_completion (a x)
    (by simpa [Matrix.IsSymm, Matrix.IsHermitian] using hx.1)]
  apply sub_le_self
  simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
    hx.posSemidef.dotProduct_mulVec_nonneg (x := G x - e)

/-- The coefficient bound for the subsolution supremum. -/
theorem upperDirectionalResponseSub_le_average (hV : IsOpen V)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    upperDirectionalResponseSub a V e ≤
      ((volumeAverage V (fun x => vecDot e (matVecMul (a x) e)) : ℝ) : EReal) := by
  unfold upperDirectionalResponseSub
  refine iSup_le fun w => iSup_le fun G => iSup_le fun hw => ?_
  exact EReal.coe_le_coe_iff.mpr (upper_response_objective_le hV ha e hw.1)

/-- Each coefficient entry is integrable, using constant-field flux bounds. -/
theorem response_coefficient_entry_integrable (ha : IsWeightedCoeffOn V a)
    (i j : Fin d) : IntegrableOn (fun x => a x i j) V := by
  have hf := flux_aestronglyMeasurable ha
    (aestronglyMeasurable_const (b := basisVec j))
  have hl := (flux_length_integrable_and_bound ha
    (aestronglyMeasurable_const (b := basisVec j))
    (GradientCore.energy_lt_top ha (constantEnergyField ha (basisVec j)))).1
  have hi := coord_integrable_of_length hf hl i
  simpa only [basisVec, matVecMul_single] using hi

/-- Averaging a quadratic form agrees with taking the quadratic form of the entrywise average. -/
theorem response_quadratic_average (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    volumeAverage V (fun x => vecDot e (matVecMul (a x) e)) =
      vecDot e (matVecMul (volumeAverageMat V a) e) := by
  classical
  have hi (i j : Fin d) := response_coefficient_entry_integrable ha i j
  unfold volumeAverage volumeAverageMat vecDot matVecMul
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => ((hi i j).mul_const (e j)).const_mul (e i)))]
  simp_rw [integral_finsetSum _ (fun j _ =>
    ((hi _ j).mul_const (e j)).const_mul (e _)), integral_const_mul, integral_mul_const]
  simp only [Finset.mul_sum, volumeAverage]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The display `e.upper.coefficient.bound`, for the directional responses. -/
theorem upper_coefficient_bound (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    0 ≤ upperDirectionalResponseSol a V e ∧
      upperDirectionalResponseSol a V e ≤ upperDirectionalResponseSub a V e ∧
      upperDirectionalResponseSub a V e ≤
        ((vecDot e (matVecMul (volumeAverageMat V a) e) : ℝ) : EReal) := by
  refine ⟨upperDirectionalResponseSol_nonneg a V e,
    upperDirectionalResponseSol_le_sub a V e, ?_⟩
  rw [← response_quadratic_average ha e]
  exact upperDirectionalResponseSub_le_average hV ha e


end CoarseDeGiorgi.Weighted
