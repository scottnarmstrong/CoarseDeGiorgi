import CoarseDeGiorgi.Statements.AuxDescendantCube
import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Integral.Bochner.Set

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
