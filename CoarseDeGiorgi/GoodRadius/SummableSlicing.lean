module

public import CoarseDeGiorgi.Selection.SurfaceMeasurability
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import CoarseDeGiorgi.Selection.TraceTransport
public import CoarseDeGiorgi.Selection.SourceRadius
public import CoarseDeGiorgi.Statements.IntegratedSlicing
public import CoarseDeGiorgi.Statements.CriticalSurfaceEmbedding

/-!
# A subsequence with a.e. summable surface errors (Proposition `p.good.radius`, Step 1)

Global fractional convergence `fracNorm univ α r (G i) → 0` gives a subsequence along which,
for almost every radius `τ` in a measurable interval, the series of `r`-th powers of the surface
fractional norms is finite (so the terms tend to zero), and the `L²` surface norms tend to zero.
-/

@[expose] public section

namespace CoarseDeGiorgi.GoodRadius

open Homogenization MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

theorem summable_surface_subsequence {n : ℕ} {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r)
    (hcritical : α * r < ((n + 1 : ℕ) : ℝ) - 1)
    (h2 : 2 ≤ (((n + 1 : ℕ) : ℝ) - 1) * r / (((n + 1 : ℕ) : ℝ) - 1 - α * r))
    {I : Set ℝ} (hI : MeasurableSet I) (hIrange : I ⊆ Ioo (1 / 2 : ℝ) 1)
    (G : ℕ → Vec (n + 1) → ℝ) (hG : ∀ i, Measurable (G i))
    (hlim : Tendsto (fun i => fracNorm univ α r (G i)) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ τ ∂volume.restrict I,
      (∑' i, surfaceFracNorm τ α r (G (ns i)) ^ r ≠ ⊤) ∧
      Tendsto (fun i => eLpNorm (G (ns i)) 2 (surfaceMeasure τ)) atTop (𝓝 0) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  obtain ⟨C₀, _hC₀, hslicing₀⟩ := CoarseDeGiorgi.integrated_slicing (d := n + 1)
  let C := C₀ * (2 : ℝ) ^ r
  have hslicing := hslicing₀ hα0 hα1 hr
  have hpow : Tendsto (fun i => fracNorm univ α r (G i) ^ r) atTop (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := r)).tendsto 0 |>.comp hlim
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos hr0] using this
  have hev : ∀ k : ℕ, ∀ᶠ i in atTop, fracNorm univ α r (G i) ^ r ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    have hpos : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ k := ENNReal.pow_pos (by norm_num) k
    exact ((tendsto_order.1 hpow).2 _ hpos).mono fun _ h => h.le
  obtain ⟨ns, hns, hbd⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨ns, hns, ?_⟩
  let μ := (volume : Measure ℝ).restrict I
  let S : ℕ → ℝ → ℝ≥0∞ := fun i τ => surfaceFracNorm τ α r (G (ns i)) ^ r
  have hSm : ∀ i, Measurable (S i) := fun i =>
    (CoarseDeGiorgi.Selection.measurable_surfaceFracNorm (hG (ns i)) α hr0).pow_const r
  have hint : ∫⁻ τ, ∑' i, S i τ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun i => (hSm i).aemeasurable]
    have hle : ∀ i, ∫⁻ τ, S i τ ∂μ ≤ ENNReal.ofReal C * (2⁻¹ : ℝ≥0∞) ^ i := fun i =>
      (hslicing (G (ns i)) (hG (ns i)) I hI hIrange).trans
        (by gcongr; exact hbd i)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    simp [ENNReal.ofReal_ne_top, ENNReal.mul_eq_top]
  have hlt := ae_lt_top (Measurable.tsum hSm) hint
  obtain ⟨D, _hD, hemb⟩ := CoarseDeGiorgi.critical_surface_embedding hα0 hα1 hr hcritical
  filter_upwards [hlt, ae_restrict_mem hI] with τ hτ hτI
  refine ⟨hτ.ne, ?_⟩
  have hterm : Tendsto (fun i => S i τ) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hτ.ne
  have hnorm : Tendsto (fun i => surfaceFracNorm τ α r (G (ns i))) atTop (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0 |>.comp hterm
    rw [ENNReal.zero_rpow_of_pos (by positivity)] at this
    refine this.congr fun i => ?_
    simp only [Function.comp_def, S, ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne',
      ENNReal.rpow_one]
  have hupper : Tendsto (fun i => ENNReal.ofReal D * surfaceFracNorm τ α r (G (ns i)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hnorm (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => zero_le)
  intro i
  exact (hemb τ (hIrange hτI).1.le (hIrange hτI).2.le (G (ns i)) (hG (ns i))).2 h2

end

end CoarseDeGiorgi.GoodRadius
