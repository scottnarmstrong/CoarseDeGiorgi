module

public import CoarseDeGiorgi.Foundations.Slicing.Tonelli
public import CoarseDeGiorgi.Foundations.Slicing.SurfaceGrowth

/-! Uniform surface-to-bulk estimates before cubical coarea. -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Slicing

open Homogenization MeasureTheory Set FracGeometry
open scoped ENNReal

noncomputable section

/-- Integration in the second surface variable uses the uniform exterior tail. -/
theorem averagedKernel_surface_row_le {n : ℕ} (τ : ℝ) {γ r : ℝ}
    (hγ : 0 ≤ γ) (hr : 0 < r) {F : Vec (n + 1) → ℝ} (hF : Measurable F)
    (x : Vec (n + 1)) :
    (∫⁻ y, averagedKernel (2 * (n : ℝ) + 1 + γ) r F (x, y)
      ∂CoarseDeGiorgi.surfaceMeasure τ) ≤
      ENNReal.ofReal (4 * (n + 1 : ℕ) * (2 : ℝ) ^ (2 * (n : ℝ))) *
        ∫⁻ z, Euclid.euclidKernel ((n : ℝ) + 1 + γ) r F (x, z) := by
  rw [lintegral_averagedKernel_row _ _ _ hF x,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro z
  dsimp only
  rw [euclidKernel_eq_product]
  by_cases hxz : x = z
  · subst z
    simp only [differencePower, sub_self, abs_zero, Real.zero_rpow hr.ne',
      ENNReal.ofReal_zero, zero_mul, mul_zero]
    exact le_rfl
  have ht := surface_kernel_tail_le τ x hγ (Euclid.eDist2_pos hxz)
  have h := mul_le_mul_right ht (differencePower r F x z)
  refine h.trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  dsimp only [inversePower]
  ring

/-- The two symmetric contributions give a dimension-only coefficient times `2^r`. -/
theorem surface_kernel_integral_le {n : ℕ} (τ : ℝ) {γ r : ℝ}
    (hγ : 0 ≤ γ) (hr : 0 < r) {F : Vec (n + 1) → ℝ} (hF : Measurable F) :
    (∫⁻ xy, Euclid.euclidKernel ((n : ℝ) + γ) r F xy
      ∂(CoarseDeGiorgi.surfaceMeasure τ).prod (CoarseDeGiorgi.surfaceMeasure τ)) ≤
      ENNReal.ofReal (2 * (((n : ℝ) + 2) ^ (n + 1)) *
        (4 * (n + 1 : ℕ) * (2 : ℝ) ^ (2 * (n : ℝ)))) * (2 : ℝ≥0∞) ^ r *
      ∫⁻ x, ∫⁻ z, Euclid.euclidKernel ((n : ℝ) + 1 + γ) r F (x, z)
        ∂volume ∂CoarseDeGiorgi.surfaceMeasure τ := by
  let μ := CoarseDeGiorgi.surfaceMeasure (d := n + 1) τ
  let q := 2 * (n : ℝ) + 1 + γ
  let A : ℝ := ((n : ℝ) + 2) ^ (n + 1)
  let D : ℝ := 4 * (n + 1 : ℕ) * (2 : ℝ) ^ (2 * (n : ℝ))
  let J := ∫⁻ xy, averagedKernel q r F xy ∂μ.prod μ
  have hq : (n : ℝ) + γ + (n + 1 : ℕ) = q := by dsimp only [q]; push_cast; ring
  have hA : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have hJ : J ≤ ENNReal.ofReal D *
      ∫⁻ x, ∫⁻ z, Euclid.euclidKernel ((n : ℝ) + 1 + γ) r F (x, z) ∂volume ∂μ := by
    dsimp only [J]
    rw [lintegral_prod _ (measurable_averagedKernel q r hF).aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono (averagedKernel_surface_row_le τ hγ hr hF)
  have hcoef : ENNReal.ofReal A * (2 : ℝ≥0∞) ^ r ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hr.le (by norm_num))
  calc
    _ ≤ ∫⁻ xy, ENNReal.ofReal A * (2 : ℝ≥0∞) ^ r *
        (averagedKernel q r F xy + averagedKernel q r F xy.swap) ∂μ.prod μ := by
      apply lintegral_mono
      intro ⟨x, y⟩
      simpa only [hq, hA, A, Prod.swap] using euclidKernel_le_averaged hr hF ((n : ℝ) + γ) x y
    _ = ENNReal.ofReal A * (2 : ℝ≥0∞) ^ r * (J + J) := by
      rw [lintegral_const_mul' _ _ hcoef,
        lintegral_add_left (measurable_averagedKernel q r hF), lintegral_prod_swap]
    _ ≤ ENNReal.ofReal A * (2 : ℝ≥0∞) ^ r *
        (ENNReal.ofReal D * (∫⁻ x, ∫⁻ z, Euclid.euclidKernel ((n : ℝ) + 1 + γ) r F (x, z)
          ∂volume ∂μ) + ENNReal.ofReal D * (∫⁻ x, ∫⁻ z,
            Euclid.euclidKernel ((n : ℝ) + 1 + γ) r F (x, z) ∂volume ∂μ)) :=
      mul_le_mul_right (add_le_add hJ hJ) _
    _ = _ := by
      have hc : ENNReal.ofReal (2 * A * D) = 2 * ENNReal.ofReal A * ENNReal.ofReal D := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      change ENNReal.ofReal A * (2 : ℝ≥0∞) ^ r *
          (ENNReal.ofReal D * _ + ENNReal.ofReal D * _) =
        ENNReal.ofReal (2 * A * D) * (2 : ℝ≥0∞) ^ r * _
      rw [hc]
      ring

end

end CoarseDeGiorgi.Foundations.Slicing
