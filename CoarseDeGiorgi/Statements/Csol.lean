import CoarseDeGiorgi.Statements.IsWeightedSolution
import Homogenization.Ambient.CoefficientField

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def Csol {d : ℕ} (a : CoeffField d) (V : Set (Vec d)) :
    Set (Vec d → ℝ) :=
  {u | ∃ G : Vec d → Vec d, IsWeightedSolution a V u G}

end CoarseDeGiorgi
