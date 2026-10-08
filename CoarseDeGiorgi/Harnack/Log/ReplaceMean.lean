import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

namespace CoarseDeGiorgi.Harnack.Log

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Replace a fixed constant center by the actual average.  The explicit `hmean`
is the Holder estimate for the constant difference; the preceding global
oscillation step supplies it in the source argument.
-/
theorem replace_center_by_average {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ} (r : ℝ≥0∞) (hr : 1 ≤ r)
    (c hc : ℝ) (hcentered : ℝ≥0∞)
    (hLocal : eLpNorm (fun x => w x - hc) r μ ≤ hcentered)
    (hmean : eLpNorm (fun _ : α => hc - c) r μ ≤ hcentered) :
    eLpNorm (fun x => w x - c) r μ ≤ 2 * hcentered := by
  have hEq : (fun x => w x - c) =ᵐ[μ]
      (fun x => (w x - hc) + (hc - c)) := by
    filter_upwards with x
    ring
  calc
    eLpNorm (fun x => w x - c) r μ =
        eLpNorm (fun x => (w x - hc) + (hc - c)) r μ :=
      eLpNorm_congr_ae hEq
    _ ≤ eLpNorm (fun x => w x - hc) r μ +
        eLpNorm (fun _ : α => hc - c) r μ := eLpNorm_add_le hr
    _ ≤ hcentered + hcentered := add_le_add hLocal hmean
    _ = 2 * hcentered := by ring

end

end CoarseDeGiorgi.Harnack.Log
