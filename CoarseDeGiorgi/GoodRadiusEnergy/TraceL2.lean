module

public import CoarseDeGiorgi.Assembly.HybridParameters
public import CoarseDeGiorgi.Selection.SurfaceMeasurability
public import CoarseDeGiorgi.Statements.CriticalSurfaceEmbedding

/-! # Surface L² convergence from fractional trace convergence

The critical trace embedding applies to measurable representatives. Surface norms
respect almost-everywhere equality, so almost-everywhere strong measurability suffices.
-/

@[expose] public section

namespace CoarseDeGiorgi.GoodRadiusEnergy.WideWidth

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-- `l.critical.trace.embedding` upgrades the good-radius fractional convergence to L² convergence. -/
theorem trace_l2_tendsto {d : ℕ} (hd : 3 ≤ d) {p q s t τ : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ ≤ 1)
    {f : ℕ → Vec d → ℝ} (hf : ∀ i, AEStronglyMeasurable (f i) (surfaceMeasure τ))
    (hlim : Tendsto (fun i => surfaceFracNorm τ (alphaParam t) (paramR q) (f i))
      atTop (nhds 0)) :
    Tendsto (fun i => eLpNorm (f i) 2 (surfaceMeasure τ)) atTop (nhds 0) := by
  obtain ⟨hα0, hα1, hr, -, hcrit, -, h2, -⟩ :=
    Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  obtain ⟨C, -, hemb⟩ := critical_surface_embedding hα0 hα1 hr hcrit
  have hupper : Tendsto
      (fun i => ENNReal.ofReal C * surfaceFracNorm τ (alphaParam t) (paramR q) (f i))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => zero_le)
  intro i
  have hrep := (hf i).ae_eq_mk
  have hbound := (hemb τ hτ0 hτ1 ((hf i).mk (f i))
    (hf i).stronglyMeasurable_mk.measurable).2 h2.le
  rw [← eLpNorm_congr_ae hrep, ← Selection.surfaceFracNorm_congr_ae hrep] at hbound
  exact hbound

end CoarseDeGiorgi.GoodRadiusEnergy.WideWidth
