module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace CoarseDeGiorgi

/-- `σ_* := t + (d-1)/(2q)` (`e.intro.parameters`). -/
noncomputable def sigmaLower (d : ℕ) (q t : ℝ) : ℝ :=
  t + ((d : ℝ) - 1) / (2 * q)

end CoarseDeGiorgi
