module

public import CoarseDeGiorgi.Statements.FracSeminorm
public import Homogenization.Ambient.CoefficientField
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def fracNorm {d : ℕ} (V : Set (Vec d)) (α r : ℝ) (w : Vec d → ℝ) : ℝ≥0∞ :=
  ((ENNReal.rpow (eLpNorm w (ENNReal.ofReal r) (volume.restrict V)) r) +
    ENNReal.rpow (fracSeminorm V α r w) r).rpow (1 / r)

end

end CoarseDeGiorgi
