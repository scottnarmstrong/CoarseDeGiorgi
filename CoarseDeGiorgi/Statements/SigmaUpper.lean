import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CoarseDeGiorgi

/-- `σ := s + (d-1)/(2p)` (`e.intro.parameters`). -/
noncomputable def sigmaUpper (d : ℕ) (p s : ℝ) : ℝ :=
  s + ((d : ℝ) - 1) / (2 * p)

end CoarseDeGiorgi
