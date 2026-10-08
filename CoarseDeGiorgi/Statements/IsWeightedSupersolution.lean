import CoarseDeGiorgi.Statements.IsWeightedSubsolution

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def IsWeightedSupersolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  IsWeightedSubsolution a V (fun x => -u x) (fun x => -G x)

end CoarseDeGiorgi
