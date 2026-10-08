import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
import CoarseDeGiorgi.Statements.SurfaceMeasure
import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def surfaceFracNorm {d : ℕ} (τ α r : ℝ) (f : Vec d → ℝ) : ℝ≥0∞ :=
  ((ENNReal.rpow (eLpNorm f (ENNReal.ofReal r) (surfaceMeasure τ)) r) +
    ENNReal.rpow (surfaceFracSeminorm τ α r f) r).rpow (1 / r)

end

end CoarseDeGiorgi
