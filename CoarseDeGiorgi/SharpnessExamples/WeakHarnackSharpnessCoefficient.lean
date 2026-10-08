module

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessLevels
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Besov.CellBounds
public import CoarseDeGiorgi.SharpnessExamples.ScalarSeries

/-! # The scalar radial coefficient: geometry and weighted-coefficient membership -/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem euclidNorm_eq {d : ℕ} (x : Vec d) : euclidNorm x = Real.sqrt (∑ i, x i ^ 2) := by
  unfold euclidNorm vecNormSq vecDot
  congr 1
  exact Finset.sum_congr rfl (fun i _ => (sq (x i)).symm)

theorem norm_le_euclidNorm {d : ℕ} (x : Vec d) : ‖x‖ ≤ euclidNorm x := by
  rw [euclidNorm_eq]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 (fun i => ?_)
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem euclidNorm_le {d : ℕ} (x : Vec d) : euclidNorm x ≤ whR d * ‖x‖ := by
  rw [euclidNorm_eq, whR, ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at this
        exact sq_le_sq' (by linarith [abs_nonneg (x i), neg_abs_le (x i)])
          (le_trans (le_abs_self _) this)
    _ = d * ‖x‖ ^ 2 := by simp

theorem euclidNorm_nonneg' {d : ℕ} (x : Vec d) : 0 ≤ euclidNorm x := Real.sqrt_nonneg _

theorem euclidNorm_eq_zero_iff {d : ℕ} (x : Vec d) : euclidNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := norm_le_euclidNorm x
    rw [h] at this
    exact norm_le_zero_iff.mp this
  · rintro rfl
    simp [euclidNorm_eq]

theorem continuous_euclidNorm {d : ℕ} : Continuous (fun x : Vec d => euclidNorm x) := by
  simp only [euclidNorm_eq]
  fun_prop

theorem mem_originCube_iff {d : ℕ} [NeZero d] (x : Vec d) :
    x ∈ originCube (d := d) 1 ↔ ‖x‖ < 1 / 2 := by
  rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1 / 2)]
  simp only [originCube, mem_ofPred_eq, Real.norm_eq_abs, abs_lt]

theorem originCube_eq_ball {d : ℕ} [NeZero d] :
    originCube (d := d) 1 = Metric.ball (0 : Vec d) (1 / 2) := by
  ext x
  rw [mem_originCube_iff, mem_ball_zero_iff]

theorem measurableSet_originCube {d : ℕ} [NeZero d] : MeasurableSet (originCube (d := d) 1) := by
  rw [originCube_eq_ball]
  exact Metric.isOpen_ball.measurableSet

theorem volume_originCube_ne_top {d : ℕ} [NeZero d] : volume (originCube (d := d) 1) ≠ ⊤ := by
  rw [originCube_eq_ball]
  exact measure_ball_lt_top.ne

/-- The scalar matrix inverse. -/
theorem smul_one_inv {d : ℕ} (c : ℝ) : ((c • (1 : Mat d))⁻¹ : Mat d) = c⁻¹ • (1 : Mat d) := by
  by_cases hc : c = 0
  · subst hc
    simp
  · apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- A scalar field is weighted when it is a.e. positive, integrable and has integrable
reciprocal. -/
theorem scalar_weightedCoeffOn {d : ℕ} {V : Set (Vec d)} (f : Vec d → ℝ) (hf : Measurable f)
    (hpos : ∀ᵐ x ∂(volume.restrict V), 0 < f x) (hb : IntegrableOn f V)
    (hbi : IntegrableOn (fun x => (f x)⁻¹) V) :
    IsWeightedCoeffOn V (fun x => f x • (1 : Mat d)) := by
  refine ⟨hf.aestronglyMeasurable.smul aestronglyMeasurable_const, ?_, ?_, ?_⟩
  · filter_upwards [hpos] with x hx
    have : f x • (1 : Mat d) = Matrix.diagonal (fun _ : Fin d => f x) := by
      ext i j
      simp [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
    rw [this, Matrix.posDef_diagonal_iff]
    intro i
    exact hx
  · have : (fun x => (f x • (1 : Mat d)).trace) = fun x => (d : ℝ) * f x := by
      funext x
      simp [Matrix.trace_smul, mul_comm]
    rw [this]
    exact hb.const_mul _
  · have : (fun x => ((f x • (1 : Mat d))⁻¹).trace) = fun x => (d : ℝ) * (f x)⁻¹ := by
      funext x
      rw [smul_one_inv]
      simp [Matrix.trace_smul, mul_comm]
    rw [this]
    exact hbi.const_mul _

end

end CoarseDeGiorgi.SharpnessExamples
