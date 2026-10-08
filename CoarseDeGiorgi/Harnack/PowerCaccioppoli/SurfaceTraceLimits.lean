module

public import CoarseDeGiorgi.Harnack.PowerCaccioppoli.TraceControl
public import CoarseDeGiorgi.Harnack.PowerCaccioppoli.TraceLr

/-! # Joint surface-trace limit bounds -/

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-- The selected surface error convergence gives simultaneous asymptotically sharp
upper bounds for the fractional seminorm and the `Lʳ` norm of the smooth trace
approximants.
-/
theorem selected_trace_components_eventually_close
    {d : ℕ} {τ α r : ℝ} (hr : 1 < r)
    (w : Vec d → ℝ) (vi : ℕ → Vec d → ℝ)
    (hw : AEStronglyMeasurable w (surfaceMeasure τ))
    (hvi : ∀ i, AEStronglyMeasurable (vi i) (surfaceMeasure τ))
    (hfinite : surfaceFracSeminorm τ α r w < ⊤)
    (herror : Tendsto (fun i => surfaceFracNorm τ α r (vi i - w))
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      surfaceFracSeminorm τ α r (vi i) ≤
          surfaceFracSeminorm τ α r w + ENNReal.ofReal ε ∧
        eLpNorm (vi i) (ENNReal.ofReal r) (surfaceMeasure τ) ≤
          eLpNorm w (ENNReal.ofReal r) (surfaceMeasure τ) + ENNReal.ofReal ε := by
  intro ε hε
  have hsemi := surfaceFracSeminorm_eventually_close_of_tendsto
    hr w vi hw hvi hfinite herror ε hε
  have hlp := surfaceLpNorm_eventually_close_of_surfaceFracNorm_tendsto
    hr w vi herror ε hε
  filter_upwards [hsemi, hlp] with i hi hj
  exact ⟨hi, hj⟩

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
