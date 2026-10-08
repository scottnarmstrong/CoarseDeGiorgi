module

public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import Homogenization.Ambient.CoefficientField

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def Csub {d : ℕ} (a : CoeffField d) (V : Set (Vec d)) :
    Set (Vec d → ℝ) :=
  {u | ∃ G : Vec d → Vec d, IsWeightedSubsolution a V u G}

end CoarseDeGiorgi
