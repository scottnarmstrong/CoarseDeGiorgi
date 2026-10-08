module

public import CoarseDeGiorgi.Foundations.Slicing.SurfaceEstimate
public import CoarseDeGiorgi.Foundations.FracGeometry.SurfaceSum
public import CoarseDeGiorgi.Selection.CoareaPartition

/-! Integrated slicing with a single constant for all fractional exponents. -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Slicing

open Homogenization MeasureTheory Set FracGeometry
open scoped ENNReal

noncomputable section

/-- `l.fractional.slicing` with its uniform dimension-only constant, in positive dimension. -/
theorem integrated_slicing_succ {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α ξ : ℝ}, 0 < α → α < 1 → 1 < ξ →
      ∀ F : Vec (n + 1) → ℝ, Measurable F →
        ∀ I : Set ℝ, MeasurableSet I → I ⊆ Ioo (1 / 2 : ℝ) 1 →
          ∫⁻ τ in I, ENNReal.rpow (CoarseDeGiorgi.surfaceFracNorm τ α ξ F) ξ ≤
            ENNReal.ofReal (C * (2 : ℝ) ^ ξ) *
              ENNReal.rpow (CoarseDeGiorgi.fracNorm univ α ξ F) ξ := by
  let B : ℝ := 2 * (((n : ℝ) + 2) ^ (n + 1)) *
    (4 * (n + 1 : ℕ) * (2 : ℝ) ^ (2 * (n : ℝ)))
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨2 * (1 + B), by positivity, ?_⟩
  intro α ξ hα _hα1 hξ F hF I hI hsub
  have hr : 0 < ξ := zero_lt_one.trans hξ
  have hγ : 0 ≤ α * ξ := (mul_pos hα hr).le
  let L : Vec (n + 1) → ℝ≥0∞ := fun x => ENNReal.ofReal (|F x| ^ ξ)
  let H : Vec (n + 1) → ℝ≥0∞ := fun x =>
    ∫⁻ z, Euclid.euclidKernel ((n : ℝ) + 1 + α * ξ) ξ F (x, z)
  have hL : Measurable L := measurable_power ξ hF
  have hH : Measurable H :=
    (measurable_euclidKernel ((n : ℝ) + 1 + α * ξ) ξ hF).lintegral_prod_right'
  let K : ℝ≥0∞ := ENNReal.ofReal (1 + B) * (2 : ℝ≥0∞) ^ ξ
  have hKfin : K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hr.le (by norm_num))
  have hKone : 1 ≤ K := by
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + B) := by
      exact_mod_cast ENNReal.ofReal_le_ofReal (by linarith only [hB] : (1 : ℝ) ≤ 1 + B)
    exact one_le_mul h1 (ENNReal.one_le_rpow (by norm_num) hr)
  have hBK : ENNReal.ofReal B * (2 : ℝ≥0∞) ^ ξ ≤ K :=
    mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith only [hB] : B ≤ 1 + B)) _
  have hsurface (τ : ℝ) : CoarseDeGiorgi.surfaceFracNorm τ α ξ F ^ ξ ≤
      K * ∫⁻ x, L x + H x ∂CoarseDeGiorgi.surfaceMeasure τ := by
    rw [surfaceNorm_power_eq τ α hr F hF,
      lintegral_add_left hL, mul_add]
    apply add_le_add
    · change (∫⁻ x, L x ∂CoarseDeGiorgi.surfaceMeasure τ) ≤ _
      simpa only [one_mul] using mul_le_mul_left hKone
        (∫⁻ x, L x ∂CoarseDeGiorgi.surfaceMeasure τ)
    · have hsemi := surface_kernel_integral_le τ hγ hr hF
      have hβ : ((n + 1 : ℕ) : ℝ) - 1 + α * ξ = (n : ℝ) + α * ξ := by push_cast; ring
      rw [hβ]
      exact hsemi.trans (mul_le_mul_left hBK _)
  have hbulk : (∫⁻ x, L x + H x) = CoarseDeGiorgi.fracNorm univ α ξ F ^ ξ := by
    rw [lintegral_add_left hL]
    dsimp only [H]
    rw [← lintegral_prod _ (measurable_euclidKernel ((n : ℝ) + 1 + α * ξ) ξ hF).aemeasurable,
      fracNorm_rpow univ α hr, fracSeminorm_rpow univ α hr, Measure.restrict_univ,
      eLpNorm_ofReal_rpow hr hF]
    simp only [L, Nat.cast_add, Nat.cast_one]
  simp only [ENNReal.rpow_eq_pow]
  calc
    _ ≤ ∫⁻ τ in I, K * ∫⁻ x, L x + H x ∂CoarseDeGiorgi.surfaceMeasure τ :=
      setLIntegral_mono' hI (fun τ _ => hsurface τ)
    _ = K * ∫⁻ τ in I, ∫⁻ x, L x + H x ∂CoarseDeGiorgi.surfaceMeasure τ :=
      lintegral_const_mul' _ _ hKfin
    _ ≤ K * ∫⁻ τ in Ioo (1 / 2 : ℝ) 1,
        ∫⁻ x, L x + H x ∂CoarseDeGiorgi.surfaceMeasure τ :=
      mul_le_mul_right (lintegral_mono_set hsub) _
    _ = K * (2 * ∫⁻ x in CoarseDeGiorgi.Selection.cubicalAnnulus (n + 1) (1 / 2) 1,
        L x + H x) := by
      rw [CoarseDeGiorgi.Selection.cubical_coarea (n := n) (R := 1)
        (g := fun x => L x + H x) (by norm_num : (0 : ℝ) ≤ 1 / 2) (hL.add hH)]
    _ ≤ K * (2 * ∫⁻ x, L x + H x) :=
      mul_le_mul_right (mul_le_mul_right (setLIntegral_le_lintegral _ _) _) _
    _ = _ := by
      rw [hbulk]
      dsimp only [K]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat, ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr.le]
      norm_num only [ENNReal.ofReal_ofNat]
      ring

/-- Integrated slicing in all dimensions, including the empty zero-dimensional surface. -/
theorem integrated_slicing_proved {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α ξ : ℝ}, 0 < α → α < 1 → 1 < ξ →
      ∀ F : Vec d → ℝ, Measurable F →
        ∀ I : Set ℝ, MeasurableSet I → I ⊆ Ioo (1 / 2 : ℝ) 1 →
          ∫⁻ τ in I, ENNReal.rpow (CoarseDeGiorgi.surfaceFracNorm τ α ξ F) ξ ≤
            ENNReal.ofReal (C * (2 : ℝ) ^ ξ) *
              ENNReal.rpow (CoarseDeGiorgi.fracNorm univ α ξ F) ξ := by
  cases d with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro α ξ _hα _hα1 hξ F hF I _hI _hsub
    have he (τ : ℝ) : CoarseDeGiorgi.surfaceFracNorm τ α ξ F ^ ξ = 0 := by
      rw [surfaceNorm_power_eq τ α (zero_lt_one.trans hξ) F hF, surfaceMeasure_zero_dim]
      simp only [powerIntegral, lintegral_zero_measure, Measure.zero_prod, add_zero]
    simp only [ENNReal.rpow_eq_pow, he, lintegral_zero]
    exact bot_le
  | succ n => exact integrated_slicing_succ

end

end CoarseDeGiorgi.Foundations.Slicing
