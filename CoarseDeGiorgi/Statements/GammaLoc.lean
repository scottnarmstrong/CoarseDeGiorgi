import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CoarseDeGiorgi

/-- `γ₁ := 2 - t + 1/(2p) + 1/(2q)` (`e.localization.exponents`). -/
noncomputable def gammaLoc (p q t : ℝ) : ℝ :=
  2 - t + 1 / (2 * p) + 1 / (2 * q)

end CoarseDeGiorgi
