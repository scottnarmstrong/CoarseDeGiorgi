import CoarseDeGiorgi.Statements.IsWeightedSubsolution
import Homogenization.Ambient.CoefficientField

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def Csub {d : ℕ} (a : CoeffField d) (V : Set (Vec d)) :
    Set (Vec d → ℝ) :=
  {u | ∃ G : Vec d → Vec d, IsWeightedSubsolution a V u G}

end CoarseDeGiorgi
