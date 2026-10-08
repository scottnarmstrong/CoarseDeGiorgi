module

public import Homogenization.Ambient.CoefficientField
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

/-- Appendix `a.besov`: for `t > 0`, the Gaussian
`G_t(x) = (4πt)^{-d/2} exp(-|x|² / (4t))`, `x ∈ ℝ^d`, with `|x|² = vecNormSq x`. -/
noncomputable def gaussianKernel {d : ℕ} (t : ℝ) (_ht : 0 < t) (x : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) * Real.exp (-(vecNormSq x) / (4 * t))

end CoarseDeGiorgi
