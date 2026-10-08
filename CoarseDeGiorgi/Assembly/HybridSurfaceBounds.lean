import CoarseDeGiorgi.Assembly.HybridEmbedding
import CoarseDeGiorgi.Assembly.HybridParameters

namespace CoarseDeGiorgi.Assembly
open Homogenization MeasureTheory
open scoped ENNReal

/-- The selected lower trace controls the upper trace's seminorm and L² norm.
This is the surface embedding step in the recurrence, with a uniform constant. -/
theorem hybrid_selected_level_bounds {d : ℕ} {α r : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hr : 1 < r) (hcrit : α * r < (d : ℝ) - 1)
    (hs : 2 ≤ ((d : ℝ) - 1) * r / ((d : ℝ) - 1 - α * r)) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ (τ δ Δ b : ℝ) (K Y : ℝ≥0∞) (f : Vec d → ℝ),
      1 / 2 ≤ τ → τ ≤ 1 → 0 < Δ → Measurable f → (∀ x, 0 ≤ f x) →
      surfaceFracNorm τ α r f ≤ K * ENNReal.ofReal δ ^ (-b) * Y →
      surfaceFracSeminorm τ α r (fun x => max (f x - Δ) 0) ≤
          K * ENNReal.ofReal δ ^ (-b) * Y ∧
      eLpNorm (fun x => max (f x - Δ) 0) 2 (surfaceMeasure τ) ≤
          A * (K * ENNReal.ofReal δ ^ (-b) * Y) ^
              ((((d : ℝ) - 1) * r / ((d : ℝ) - 1 - α * r)) / 2) *
            ENNReal.ofReal Δ ^ (1 - (((d : ℝ) - 1) * r / ((d : ℝ) - 1 - α * r)) / 2) := by
  obtain ⟨C, hC, hlevel⟩ := hybrid_surface_level_bound hα hα1 hr hcrit hs
  let z := ((d : ℝ) - 1) * r / ((d : ℝ) - 1 - α * r)
  refine ⟨ENNReal.ofReal C ^ (z / 2), ENNReal.rpow_lt_top_of_nonneg
    (by dsimp [z]; linarith only [hs]) ENNReal.ofReal_ne_top, ?_⟩
  intro τ δ Δ b K Y f hτ hτ1 hΔ hfm hf hbound
  refine ⟨(hybrid_surface_seminorm_level_le τ α Δ (zero_lt_one.trans hr) f).trans
    ((hybrid_surface_seminorm_le_norm τ α (zero_lt_one.trans hr) f).trans hbound), ?_⟩
  have h := ENNReal.rpow_le_rpow (hlevel τ hτ hτ1 f hfm hf Δ hΔ) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hΔ.le _) (by norm_num),
    ← Real.rpow_mul hΔ.le, ← ENNReal.rpow_mul,
    ENNReal.mul_rpow_of_nonneg _ _ (by linarith only [hs])] at h
  have he : (2 - z) * (1 / 2 : ℝ) = 1 - z / 2 := by ring
  change _ ≤ ENNReal.ofReal (Δ ^ ((2 - z) * (1 / 2))) *
    (ENNReal.ofReal C ^ (z * (1 / 2)) * surfaceFracNorm τ α r f ^ (z * (1 / 2))) at h
  rw [he, ← ENNReal.ofReal_rpow_of_pos hΔ, show z * (1 / 2) = z / 2 by ring] at h
  apply h.trans
  calc
    _ ≤ ENNReal.ofReal Δ ^ (1 - z / 2) *
        (ENNReal.ofReal C ^ (z / 2) * (K * ENNReal.ofReal δ ^ (-b) * Y) ^ (z / 2)) := by
      gcongr
    _ = _ := by ring

end CoarseDeGiorgi.Assembly
