module

public import CoarseDeGiorgi.Statements.AuxDescendantCube
public import Homogenization.Ambient.CoefficientField
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def auxDescendantAverage {d : ℕ} (m k : ℤ) (z n : Fin d → ℤ)
    (f : Vec d → Vec d) : Vec d := fun i =>
  (((3 : ℝ) ^ (1 - k)) ^ d)⁻¹ *
    ∫ x in auxDescendantCube m k z n, f x i ∂volume

end

end CoarseDeGiorgi
