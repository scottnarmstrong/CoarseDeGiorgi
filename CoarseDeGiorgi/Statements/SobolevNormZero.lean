import CoarseDeGiorgi.Statements.SobolevNorm

import CoarseDeGiorgi.NegSobolev.SobolevNormFacts
open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi

/-- `W^{0,ξ}(U) = L^ξ(U)`: on an open `U`, the Sobolev norm of order zero is the `L^ξ(U)` norm. -/
theorem sobolevNorm_zero {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {ξ : ℝ} (hξ : 1 ≤ ξ)
    (w : Vec d → ℝ) :
    sobolevNorm U hU 0 ξ le_rfl hξ w = eLpNorm w (ENNReal.ofReal ξ) (volume.restrict U)
:=
  by exact CoarseDeGiorgi.NegSobolev.sobolevNorm_zero hU hξ w

end CoarseDeGiorgi
