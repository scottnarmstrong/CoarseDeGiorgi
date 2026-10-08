import CoarseDeGiorgi.Foundations.Reconstruction.SignReflection

/-! # Ordinary volume integration over the reflected box -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The open reflected fundamental box; its faces can be changed to half-open faces a.e. -/
def reflectionBox (m : ℤ) : Set (Vec d) := {x | ∀ i, |x i| < auxSide m}

theorem isOpen_reflectionPositiveBox (m : ℤ) :
    IsOpen (reflectionPositiveBox (d := d) m) := by
  simp only [reflectionPositiveBox, ← Set.iInter_ofPred]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)

theorem measurableSet_reflectionOrthant (m : ℤ) (s : Fin d → Bool) :
    MeasurableSet (reflectionOrthant m s) :=
  (isOpen_reflectionPositiveBox m).measurableSet.preimage (signLinear s).continuous.measurable

theorem mem_iUnion_reflectionOrthant (m : ℤ) (x : Vec d) :
    x ∈ ⋃ s : Fin d → Bool, reflectionOrthant m s ↔
      x ∈ reflectionBox m ∧ ∀ i, x i ≠ 0 := by
  classical
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩
    have hcoord (i : Fin d) : |x i| < auxSide m ∧ x i ≠ 0 := by
      have h := hs i
      change 0 < reflectionSign (s i) * x i ∧ reflectionSign (s i) * x i < auxSide m at h
      cases hi : s i
      · simp only [hi, reflectionSign, Bool.false_eq_true, ite_false, neg_one_mul] at h
        have hn : x i < 0 := neg_pos.mp h.1
        exact ⟨by rw [abs_of_neg hn]; exact h.2, ne_of_lt hn⟩
      · simp only [hi, reflectionSign, ite_true, one_mul] at h
        exact ⟨by rw [abs_of_pos h.1]; exact h.2, ne_of_gt h.1⟩
    exact ⟨fun i => (hcoord i).1, fun i => (hcoord i).2⟩
  · rintro ⟨hx, hn⟩
    refine ⟨fun i => decide (0 < x i), ?_⟩
    intro i
    change 0 < reflectionSign (decide (0 < x i)) * x i ∧
      reflectionSign (decide (0 < x i)) * x i < auxSide m
    by_cases hi : 0 < x i
    · simp only [hi, decide_true, reflectionSign, ite_true, one_mul]
      exact ⟨trivial, by simpa only [abs_of_pos hi] using hx i⟩
    · have hi' : x i < 0 := lt_of_le_of_ne (le_of_not_gt hi) (hn i)
      simp only [hi, decide_false, reflectionSign, Bool.false_eq_true, ite_false, neg_one_mul]
      exact ⟨neg_pos.mpr hi', by simpa only [abs_of_neg hi'] using hx i⟩

/-- All coordinate reflection planes are Lebesgue null, without a dimension assumption. -/
theorem ae_all_coordinates_ne_zero : ∀ᵐ x : Vec d ∂volume, ∀ i, x i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  exact (Measure.quasiMeasurePreserving_eval (fun _ : Fin d => (volume : Measure ℝ)) i).ae
    (show ∀ᵐ t : ℝ ∂volume, t ≠ 0 from by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (0 : ℝ)))

theorem reflectionBox_ae_eq_iUnion_orthant (m : ℤ) :
    reflectionBox (d := d) m =ᵐ[volume] ⋃ s : Fin d → Bool, reflectionOrthant m s := by
  filter_upwards [ae_all_coordinates_ne_zero (d := d)] with x hx
  exact propext (by rw [mem_iUnion_reflectionOrthant]; exact ⟨fun h => ⟨h, hx⟩, And.left⟩)

/-- Decomposition of ordinary unnormalized volume integration into open reflection cells. -/
theorem setIntegral_reflectionBox_eq_sum (m : ℤ) (f : Vec d → ℝ)
    (hf : ∀ s : Fin d → Bool, IntegrableOn f (reflectionOrthant m s) volume) :
    ∫ x in reflectionBox m, f x ∂volume =
      ∑ s : Fin d → Bool, ∫ x in reflectionPositiveBox m, f (signLinear s x) ∂volume := by
  rw [setIntegral_congr_set (reflectionBox_ae_eq_iUnion_orthant m),
    integral_iUnion_fintype (measurableSet_reflectionOrthant m)
      (pairwise_disjoint_reflectionOrthant m) hf]
  apply Finset.sum_congr rfl
  intro s _
  have h := setIntegral_signLinear_orthant m s (fun x => f (signLinear s x))
  have hinv (y : Vec d) := signLinear_involutive s y
  simpa only [hinv] using h

/-- Integrability on the reflected box is exactly cellwise integrability. -/
theorem integrableOn_reflectionBox_iff (m : ℤ) (f : Vec d → ℝ) :
    IntegrableOn f (reflectionBox m) volume ↔
      ∀ s : Fin d → Bool, IntegrableOn f (reflectionOrthant m s) volume := by
  rw [integrableOn_congr_set_ae (reflectionBox_ae_eq_iUnion_orthant m)]
  exact integrableOn_finite_iUnion

end

end CoarseDeGiorgi.Foundations.Reconstruction
