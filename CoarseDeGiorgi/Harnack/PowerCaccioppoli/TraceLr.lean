module

public import CoarseDeGiorgi.Statements.SurfaceFracNorm
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm

/-! # Surface Lʳ trace control -/

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

private theorem eLpNorm_le_surfaceFracNorm_local {d : ℕ} {τ α r : ℝ}
    (hr : 1 < r) (f : Vec d → ℝ) :
    eLpNorm f (ENNReal.ofReal r) (surfaceMeasure τ) ≤
      surfaceFracNorm τ α r f := by
  unfold CoarseDeGiorgi.surfaceFracNorm
  have hbase : eLpNorm f (ENNReal.ofReal r) (surfaceMeasure τ) ^ r ≤
      eLpNorm f (ENNReal.ofReal r) (surfaceMeasure τ) ^ r +
        surfaceFracSeminorm τ α r f ^ r := le_add_right le_rfl
  have h := ENNReal.rpow_le_rpow hbase (show 0 ≤ 1 / r by positivity)
  simpa only [ENNReal.rpow_eq_pow, ← ENNReal.rpow_mul,
    mul_one_div_cancel (zero_lt_one.trans hr).ne', ENNReal.rpow_one] using h

/-- Convergence of the combined surface norm `surfaceFracNorm` controls the `Lʳ` trace of
approximants, with an arbitrarily small additive error. This is the second
trace input used in the exterior pairing bound.
-/
theorem surfaceLpNorm_eventually_close_of_surfaceFracNorm_tendsto
    {d : ℕ} {τ α r : ℝ} (hr : 1 < r)
    (w : Vec d → ℝ) (vi : ℕ → Vec d → ℝ)
    (herror : Tendsto (fun i => surfaceFracNorm τ α r (vi i - w))
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      eLpNorm (vi i) (ENNReal.ofReal r) (surfaceMeasure τ) ≤
        eLpNorm w (ENNReal.ofReal r) (surfaceMeasure τ) + ENNReal.ofReal ε := by
  intro ε hε
  have hsmall : ∀ᶠ i in atTop,
      surfaceFracNorm τ α r (vi i - w) < ENNReal.ofReal ε := by
    have heps : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    exact (tendsto_order.1 herror).2 (ENNReal.ofReal ε) heps
  have hrp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr.le
  filter_upwards [hsmall] with i hi
  have htriangle : eLpNorm (vi i) (ENNReal.ofReal r) (surfaceMeasure τ) ≤
      eLpNorm w (ENNReal.ofReal r) (surfaceMeasure τ) +
        eLpNorm (vi i - w) (ENNReal.ofReal r) (surfaceMeasure τ) := by
    calc
      eLpNorm (vi i) (ENNReal.ofReal r) (surfaceMeasure τ) =
          eLpNorm (w + (vi i - w)) (ENNReal.ofReal r) (surfaceMeasure τ) := by
        congr 1
        funext x
        change vi i x = w x + (vi i x - w x)
        ring
      _ ≤ _ := eLpNorm_add_le hrp
  have herr := eLpNorm_le_surfaceFracNorm_local (τ := τ) (α := α) hr (vi i - w)
  exact htriangle.trans (by
    simpa only [add_comm] using
      add_le_add_left (herr.trans hi.le)
        (eLpNorm w (ENNReal.ofReal r) (surfaceMeasure τ)))

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
