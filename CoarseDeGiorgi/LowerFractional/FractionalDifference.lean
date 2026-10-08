module

public import CoarseDeGiorgi.Statements.FracSeminorm
public import CoarseDeGiorgi.Weighted.L1Tools
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A raw Lᵖ representation of the fractional seminorm and its
Fatou property. The scalar carrier norm is used only on scalar differences. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

noncomputable def fractionalDifference {d : ℕ} (α r : ℝ) (w : Vec d → ℝ)
    (p : Vec d × Vec d) : ℝ :=
  (w p.1 - w p.2) / euclidDist p.1 p.2 ^ ((d : ℝ) / r + α)

theorem continuous_euclidDist {d : ℕ} :
    Continuous (fun p : Vec d × Vec d => euclidDist p.1 p.2) := by
  unfold euclidDist vecNormSq vecDot
  fun_prop

theorem fractionalDifference_aestronglyMeasurable {d : ℕ} {μ : Measure (Vec d)}
    [SFinite μ] {w : Vec d → ℝ} (hw : AEStronglyMeasurable w μ) (α r : ℝ) :
    AEStronglyMeasurable (fractionalDifference α r w) (μ.prod μ) := by
  exact ((hw.comp_fst.sub hw.comp_snd).aemeasurable.div
    (continuous_euclidDist.measurable.pow_const _).aemeasurable).aestronglyMeasurable

theorem fracKernel_eq_fractionalDifference {d : ℕ} (α : ℝ) {r : ℝ} (hr : 0 < r)
    (w : Vec d → ℝ) (p : Vec d × Vec d) :
    fracKernel α r w p = ‖fractionalDifference α r w p‖ₑ ^ r := by
  have hd : 0 ≤ euclidDist p.1 p.2 := Real.sqrt_nonneg _
  have hexp : ((d : ℝ) / r + α) * r = (d : ℝ) + α * r := by
    field_simp
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr.le]
  unfold fracKernel fracKernelWithDimension fractionalDifference
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg hd _),
    Real.div_rpow (abs_nonneg _) (Real.rpow_nonneg hd _),
    ← Real.rpow_mul hd, hexp]

/-- Exact identification with the fractional seminorm `fracSeminorm`. -/
theorem fracSeminorm_eq_eLpNorm {d : ℕ} {V : Set (Vec d)} {α r : ℝ} (hr : 0 < r)
    {w : Vec d → ℝ} (hw : AEStronglyMeasurable w (volume.restrict V)) :
    fracSeminorm V α r w = eLpNorm (fractionalDifference α r w)
      (ENNReal.ofReal r) ((volume.restrict V).prod (volume.restrict V)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top (fractionalDifference_aestronglyMeasurable hw α r),
    ENNReal.toReal_ofReal hr.le]
  unfold fracSeminorm
  simp only [ENNReal.rpow_eq_pow]
  congr 1
  exact lintegral_congr fun p => fracKernel_eq_fractionalDifference α hr w p

/-- Fatou for the fractional seminorm under a.e. value convergence. -/
theorem fracSeminorm_le_of_ae_tendsto {d : ℕ} {V : Set (Vec d)} {α r : ℝ}
    (hr : 0 < r) {f : ℕ → Vec d → ℝ} {w : Vec d → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict V))
    (hw : AEStronglyMeasurable w (volume.restrict V)) {B : ℝ≥0∞}
    (hB : ∀ᶠ n in atTop, fracSeminorm V α r (f n) ≤ B)
    (ht : ∀ᵐ x ∂volume.restrict V, Tendsto (fun n => f n x) atTop (𝓝 (w x))) :
    fracSeminorm V α r w ≤ B := by
  rw [fracSeminorm_eq_eLpNorm hr hw]
  apply Lp.eLpNorm_le_of_ae_tendsto
    (hB.mono fun n hn => (fracSeminorm_eq_eLpNorm hr (hf n)) ▸ hn)
    (fun n => fractionalDifference_aestronglyMeasurable (hf n) α r)
    (fractionalDifference_aestronglyMeasurable hw α r)
  have hp : ∀ᵐ p ∂(volume.restrict V).prod (volume.restrict V),
      Tendsto (fun n => f n p.1) atTop (𝓝 (w p.1)) ∧
        Tendsto (fun n => f n p.2) atTop (𝓝 (w p.2)) :=
    (Measure.quasiMeasurePreserving_fst.ae ht).and
      (Measure.quasiMeasurePreserving_snd.ae ht)
  filter_upwards [hp] with p hp
  exact (hp.1.sub hp.2).div_const _



end CoarseDeGiorgi.LowerFractional
