import CoarseDeGiorgi.Foundations.Reconstruction.CellPairing

/-! # A bounded smooth kernel pairs with each increment through parent cancellation -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Every reflected gradient-average increment is integrable, regardless of the input exponent. -/
theorem integrableOn_reflectedAverage_increment (m : ℤ) (z : Fin d → ℤ)
    (j : ℕ) (f : Vec d → Vec d) :
    IntegrableOn (fun y => reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y)
      (reflectionBox m) volume := by
  have hi (k : ℕ) : IntegrableOn (reflectedAverage m k z f) (reflectionBox m) volume :=
    integrableOn_reflectedGradient
      (memLp_one_iff_integrable.mp (memLp_auxAverage m (m + k) z f 1))
  exact (hi (j + 1)).sub (hi j)

/-- The parent-center pairing is integrable for every globally bounded continuous kernel. -/
theorem integrableOn_parentCenter_pairing (m : ℤ) (z : Fin d → ℤ) (j : ℕ)
    (f : Vec d → Vec d) (K : Vec d → Vec d) (hK : Continuous K)
    {M : ℝ} (hM : ∀ v, ‖K v‖ ≤ M) (x : Vec d) :
    IntegrableOn (fun y => vecDot (K (x - reflectedParentCenter m z j y))
      (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y)) (reflectionBox m) volume := by
  have hi := (integrableOn_reflectedAverage_increment m z j f).norm.const_mul ((d : ℝ) * M)
  have hm : Measurable (fun y => vecDot (K (x - reflectedParentCenter m z j y))
      (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y)) :=
    measurable_vecDot (hK.measurable.comp (measurable_const.sub
      (measurable_reflectedParentCenter m z j)))
      ((measurable_reflectedAverage m (j + 1) z f).sub (measurable_reflectedAverage m j z f))
  apply hi.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun y => (norm_vecDot_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hM _) (Nat.cast_nonneg d)) (norm_nonneg _))

/-- The exact increment convolution equals its parent-center-subtracted convolution. -/
theorem integral_increment_eq_cancellation {m : ℤ} {z : Fin d → ℤ} (j : ℕ)
    (f : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume)
    (K : Vec d → Vec d) (hK : Continuous K) {M : ℝ}
    (hM : ∀ v, ‖K v‖ ≤ M) (x : Vec d) :
    ∫ y in reflectionBox m, vecDot (K (x - y))
      (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y) =
    ∫ y in reflectionBox m,
      vecDot (kernelCancellation K y (reflectedParentCenter m z j y) x)
        (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y) := by
  have hi1 := integrableOn_kernel_dot (integrableOn_reflectedAverage_increment m z j f) K hK x
  have hi2 := integrableOn_parentCenter_pairing m z j f K hK hM x
  have heq : (fun y => vecDot (kernelCancellation K y (reflectedParentCenter m z j y) x)
      (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y)) =
      fun y => vecDot (K (x - y)) (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y) -
        vecDot (K (x - reflectedParentCenter m z j y))
          (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y) := by
    funext y
    simp only [kernelCancellation, vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [heq, integral_sub hi1 hi2, integral_parentCenter_pairing_eq_zero j f hf K x hi2, sub_zero]

/-- Difference of two averaged-gradient pairings is the pairing with their increment. -/
theorem integral_kernel_reflectedAverage_sub (m : ℤ) (z : Fin d → ℤ) (j : ℕ)
    (f : Vec d → Vec d) (K : Vec d → Vec d) (hK : Continuous K) (x : Vec d) :
    (∫ y in reflectionBox m, vecDot (K (x - y)) (reflectedAverage m (j + 1) z f y)) -
      (∫ y in reflectionBox m, vecDot (K (x - y)) (reflectedAverage m j z f y)) =
    ∫ y in reflectionBox m, vecDot (K (x - y))
      (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y) := by
  have hi (k : ℕ) : IntegrableOn (fun y => vecDot (K (x - y)) (reflectedAverage m k z f y))
      (reflectionBox m) volume := integrableOn_kernel_dot (integrableOn_reflectedGradient
    (memLp_one_iff_integrable.mp (memLp_auxAverage m (m + k) z f 1))) K hK x
  rw [← integral_sub (hi (j + 1)) (hi j)]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

end

end CoarseDeGiorgi.Foundations.Reconstruction
