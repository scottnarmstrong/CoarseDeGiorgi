import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def faceCoordinateMeasures {d : ℕ} (τ : ℝ) (i : Fin d)
    (positive : Bool) : Fin d → Measure ℝ := fun j =>
  if j = i then Measure.dirac (if positive then τ / 2 else -τ / 2)
  else volume.restrict (Set.Ioo (-τ / 2) (τ / 2))

end

end CoarseDeGiorgi
