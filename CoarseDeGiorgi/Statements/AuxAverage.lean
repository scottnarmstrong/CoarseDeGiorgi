module

public import CoarseDeGiorgi.Statements.AuxDescendantAverage
public import CoarseDeGiorgi.Statements.AuxDescendantCube
public import CoarseDeGiorgi.Statements.AuxDescendantIndices
public import Homogenization.Ambient.CoefficientField

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def auxAverage {d : ℕ} (m k : ℤ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) : Vec d → Vec d := by
  classical
  exact fun x => (auxDescendantIndices m k).sum fun n =>
      if x ∈ auxDescendantCube m k z n then auxDescendantAverage m k z n f else 0

end

end CoarseDeGiorgi
