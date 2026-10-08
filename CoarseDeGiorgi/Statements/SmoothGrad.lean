import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def smoothGrad {d : ℕ} (φ : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => fderiv ℝ φ x (basisVec i)

end CoarseDeGiorgi
