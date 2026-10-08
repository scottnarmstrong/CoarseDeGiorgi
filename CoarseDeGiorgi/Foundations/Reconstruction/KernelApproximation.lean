import CoarseDeGiorgi.Foundations.Reconstruction.KernelBlocks
import CoarseDeGiorgi.Foundations.Reconstruction.AuxIncrementLp

/-! # Fixed-kernel limits use only strong L¹ convergence of gradient averages -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

variable {d : ℕ}

/-- A sup-norm dot-product estimate, used only in the fixed-kernel limit. -/
theorem norm_vecDot_le (v w : Vec d) : ‖vecDot v w‖ ≤ (d : ℝ) * ‖v‖ * ‖w‖ := by
  calc
    _ ≤ ∑ i : Fin d, ‖v i * w i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖v‖ * ‖w‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm v i) (norm_le_pi_norm w i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem integrableOn_kernel_dot {m : ℤ} {f : Vec d → Vec d}
    (hf : IntegrableOn f (reflectionBox m) volume) (K : Vec d → Vec d)
    (hK : Continuous K) (x : Vec d) :
    IntegrableOn (fun y => vecDot (K (x - y)) (f y)) (reflectionBox m) volume := by
  unfold vecDot
  apply integrable_finsetSum
  intro i _
  apply ((integrableOn_reflectionBox_mul_continuous (hf.eval i)
    ((continuous_apply i).comp (hK.comp (continuous_const.sub continuous_id))))).congr
  exact ae_of_all _ fun y => mul_comm _ _

/-- The fixed-kernel supremum controls its action on an L¹ error. -/
theorem norm_kernel_pairing_sub_le {m : ℤ} {f g : Vec d → Vec d}
    (hf : IntegrableOn f (reflectionBox m) volume) (hg : IntegrableOn g (reflectionBox m) volume)
    (K : Vec d → Vec d) (hK : Continuous K) {M : ℝ} (_hM0 : 0 ≤ M)
    (hM : ∀ v, ‖K v‖ ≤ M) (x : Vec d) :
    ‖(∫ y in reflectionBox m, vecDot (K (x - y)) (g y) ∂volume) -
      ∫ y in reflectionBox m, vecDot (K (x - y)) (f y) ∂volume‖ ≤
        ((d : ℝ) * M) * ∫ y in reflectionBox m, ‖g y - f y‖ ∂volume := by
  rw [← integral_sub (integrableOn_kernel_dot hg K hK x) (integrableOn_kernel_dot hf K hK x),
    ← integral_const_mul]
  have heq (y : Vec d) : vecDot (K (x - y)) (g y) - vecDot (K (x - y)) (f y) =
      vecDot (K (x - y)) (g y - f y) := by
    simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  apply norm_integral_le_of_norm_le ((hg.sub hf).norm.const_mul ((d : ℝ) * M))
  exact ae_of_all _ fun y => by
    rw [heq]
    change ‖vecDot (K (x - y)) (g y - f y)‖ ≤ ((d : ℝ) * M) * ‖g y - f y‖
    exact (norm_vecDot_le _ _).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hM (x - y)) (Nat.cast_nonneg d)) (norm_nonneg _))

/-- Averaged-gradient reconstruction converges uniformly for every fixed bounded smooth kernel. -/
theorem tendstoUniformly_kernelPairing_reflectedAverage {m : ℤ} {z : Fin d → ℤ}
    (Dw : Vec d → Vec d) (hDw : IntegrableOn Dw (auxCube m z) volume)
    (K : Vec d → Vec d) (hK : Continuous K) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ v, ‖K v‖ ≤ M) :
    TendstoUniformly
      (fun j x => ∫ y in reflectionBox m, vecDot (K (x - y)) (reflectedAverage m j z Dw y) ∂volume)
      (kernelPairing m z K Dw) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hlim := (tendsto_integral_norm_reflectedAverage_sub m z Dw hDw).const_mul ((d : ℝ) * M)
  have hevent : ∀ᶠ j : ℕ in atTop, ((d : ℝ) * M) * ∫ y in reflectionBox m,
      ‖reflectedAverage m j z Dw y - reflectedGradient m z Dw y‖ ∂volume < ε := by
    exact hlim.eventually (p := fun s : ℝ => s < ε)
      (by simpa only [mul_zero] using gt_mem_nhds hε)
  filter_upwards [hevent] with j hj
  intro x
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt (norm_kernel_pairing_sub_le
    (integrableOn_reflectedGradient hDw)
    (integrableOn_reflectedGradient
      (memLp_one_iff_integrable.mp (memLp_auxAverage m (m + j) z Dw 1))) K hK hM0 hM x) hj

end

end CoarseDeGiorgi.Foundations.Reconstruction
