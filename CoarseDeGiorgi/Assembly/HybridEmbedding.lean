module

public import CoarseDeGiorgi.Statements.CriticalSurfaceEmbedding
public import CoarseDeGiorgi.Statements.DnpvTheorem6_5
public import CoarseDeGiorgi.Statements.FracSeminorm

@[expose] public section

namespace CoarseDeGiorgi.Assembly

open Homogenization MeasureTheory
open scoped ENNReal

/-- The bulk embedding `dnpv_theorem_6_5`, in the norm form needed by inner localization. -/
theorem hybrid_compact_embedding {d : ℕ} {α r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : 1 ≤ r) (hcrit : α * r < d) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ f : Vec d → ℝ,
      Measurable f → HasCompactSupport f →
      eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent d α r)) volume ≤
        C * fracSeminorm Set.univ α r f := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  obtain ⟨C, hC, hbound⟩ := CoarseDeGiorgi.dnpv_theorem_6_5 d α r hα hα1 hr hcrit
  refine ⟨(ENNReal.ofReal C) ^ (1 / r), by positivity,
    ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top, ?_⟩
  intro f hf hc
  have h := ENNReal.rpow_le_rpow (hbound f hf hc) (by positivity : 0 ≤ 1 / r)
  change (eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent d α r)) volume ^ r) ^
    (1 / r) ≤ (ENNReal.ofReal C *
      ∫⁻ xy : Vec d × Vec d, fracKernel α r f xy ∂(volume.prod volume)) ^ (1 / r) at h
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at h
  simpa only [fracSeminorm, Measure.restrict_univ, ENNReal.rpow_eq_pow] using h

/-- The pointwise level-gap inequality, valid also below the upper level. -/
theorem hybrid_level_power {x Δ p s : ℝ} (hΔ : 0 < Δ) (hp : 0 < p)
    (hps : p ≤ s) (hx : 0 ≤ x) :
    (max (x - Δ) 0) ^ p ≤ Δ ^ (p - s) * x ^ s := by
  by_cases hlevel : x ≤ Δ
  · rw [max_eq_right (by linarith), Real.zero_rpow hp.ne']
    positivity
  · have hΔx : Δ ≤ x := (lt_of_not_ge hlevel).le
    have hx0 : 0 < x := hΔ.trans_le hΔx
    have hmax : max (x - Δ) 0 ≤ x := max_le (by linarith) hx
    have hnegative := Real.rpow_le_rpow_of_nonpos hΔ hΔx (sub_nonpos.mpr hps)
    calc
      _ ≤ x ^ p := Real.rpow_le_rpow (le_max_right _ _) hmax hp.le
      _ = x ^ (p - s) * x ^ s := by rw [← Real.rpow_add hx0]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hnegative (Real.rpow_nonneg hx _)

/-- The level-gap estimate for arbitrary measures, including surface measure. -/
theorem hybrid_level_norm_power {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ} {Δ p s : ℝ} (hΔ : 0 < Δ) (hp : 0 < p) (hps : p ≤ s)
    (hf : ∀ x, 0 ≤ f x) (hfm : AEStronglyMeasurable f μ) :
    (eLpNorm (fun x => max (f x - Δ) 0) (ENNReal.ofReal p) μ) ^ p ≤
      ENNReal.ofReal (Δ ^ (p - s)) * (eLpNorm f (ENNReal.ofReal s) μ) ^ s := by
  have hs : 0 < s := hp.trans_le hps
  have hbm : AEStronglyMeasurable (fun x => max (f x - Δ) 0) μ :=
    continuous_max.comp_aestronglyMeasurable₂
      (hfm.sub (aestronglyMeasurable_const (b := Δ)))
      (aestronglyMeasurable_const (b := (0 : ℝ)))
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
      hbm,
    eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top hfm,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hs.le]
  rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' hp,
    ← lintegral_rpow_enorm_eq_rpow_eLpNorm' hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  have h := ENNReal.ofReal_le_ofReal (hybrid_level_power hΔ hp hps (hf x))
  rw [ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hp.le,
    ← ENNReal.ofReal_rpow_of_nonneg (hf x) hs.le] at h
  simpa only [← ofReal_norm, Real.norm_eq_abs,
    abs_of_nonneg (le_max_right (f x - Δ) (0 : ℝ)), abs_of_nonneg (hf x)] using h

/-- Raising the integrated level-gap inequality to the power used in Y². -/
theorem hybrid_level_norm_sq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {f : X → ℝ} {Δ p s : ℝ} (hΔ : 0 < Δ) (hp : 0 < p) (hps : p ≤ s)
    (hf : ∀ x, 0 ≤ f x) (hfm : AEStronglyMeasurable f μ) :
    (eLpNorm (fun x => max (f x - Δ) 0) (ENNReal.ofReal p) μ) ^ (2 : ℝ) ≤
      ENNReal.ofReal (Δ ^ (2 - 2 * s / p)) *
        (eLpNorm f (ENNReal.ofReal s) μ) ^ (2 * s / p) := by
  have h := ENNReal.rpow_le_rpow (hybrid_level_norm_power μ hΔ hp hps hf hfm)
    (show 0 ≤ 2 / p by positivity)
  rw [← ENNReal.rpow_mul, show p * (2 / p) = 2 by field_simp,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hΔ.le _) (by positivity),
    ← Real.rpow_mul hΔ.le, ← ENNReal.rpow_mul] at h
  simpa only [show (p - s) * (2 / p) = 2 - 2 * s / p by field_simp,
    show s * (2 / p) = 2 * s / p by ring] using h

/-- The selected trace level estimate uses the critical surface embedding.
Its embedding constant depends only on the dimension and exponents. -/
theorem hybrid_surface_level_bound {d : ℕ} {α r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : 1 < r) (hcrit : α * r < (d : ℝ) - 1)
    (hs : 2 ≤ ((d : ℝ) - 1) * r / ((d : ℝ) - 1 - α * r)) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 1 / 2 ≤ τ → τ ≤ 1 →
      ∀ f : Vec d → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
      ∀ Δ : ℝ, 0 < Δ →
        (eLpNorm (fun x => max (f x - Δ) 0) 2 (surfaceMeasure τ)) ^ (2 : ℝ) ≤
          ENNReal.ofReal (Δ ^ (2 - ((d : ℝ) - 1) * r / ((d : ℝ) - 1 - α * r))) *
            (ENNReal.ofReal C * surfaceFracNorm τ α r f) ^
              (((d : ℝ) - 1) * r / ((d : ℝ) - 1 - α * r)) := by
  obtain ⟨C, hC, hbound⟩ := CoarseDeGiorgi.critical_surface_embedding hα hα1 hr hcrit
  refine ⟨C, hC, ?_⟩
  intro τ hτ hτ1 f hf hf0 Δ hΔ
  have hlevel := hybrid_level_norm_power (surfaceMeasure τ) hΔ
    (by norm_num : (0 : ℝ) < 2) hs hf0 hf.aestronglyMeasurable
  norm_num only [ENNReal.ofReal_ofNat] at hlevel
  exact hlevel.trans (mul_le_mul_right
    (ENNReal.rpow_le_rpow (hbound τ hτ hτ1 f hf).1
      ((by norm_num : (0 : ℝ) ≤ 2).trans hs)) _)

/-- Shifting and taking a positive part contracts the fractional surface seminorm. -/
theorem hybrid_surface_seminorm_level_le {d : ℕ} (τ α Δ : ℝ) {r : ℝ}
    (hr : 0 < r) (f : Vec d → ℝ) :
    surfaceFracSeminorm τ α r (fun x => max (f x - Δ) 0) ≤
      surfaceFracSeminorm τ α r f := by
  unfold surfaceFracSeminorm
  simp only [ENNReal.rpow_eq_pow]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply lintegral_mono
  intro xy
  unfold fracKernelWithDimension
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _
    (Real.rpow_nonneg (Foundations.FractionalSobolev.euclidDist_nonneg _ _) _)
  apply Real.rpow_le_rpow (abs_nonneg _) _ hr.le
  have h := abs_max_sub_max_le_abs (f xy.1 - Δ) (f xy.2 - Δ) (0 : ℝ)
  simpa only [sub_sub_sub_cancel_right] using h

/-- The norm part selected by the source also controls the surface seminorm. -/
theorem hybrid_surface_seminorm_le_norm {d : ℕ} (τ α : ℝ) {r : ℝ}
    (hr : 0 < r) (f : Vec d → ℝ) :
    surfaceFracSeminorm τ α r f ≤ surfaceFracNorm τ α r f := by
  unfold surfaceFracNorm
  simp only [ENNReal.rpow_eq_pow]
  calc
    _ = (surfaceFracSeminorm τ α r f ^ r) ^ (1 / r) := by
      rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]
    _ ≤ _ := ENNReal.rpow_le_rpow (le_add_left le_rfl) (by positivity)

end CoarseDeGiorgi.Assembly
