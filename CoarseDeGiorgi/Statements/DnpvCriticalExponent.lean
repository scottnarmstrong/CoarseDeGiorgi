module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace CoarseDeGiorgi

noncomputable section

def dnpvCriticalExponent (n : ℕ) (s p : ℝ) : ℝ :=
  (n : ℝ) * p / ((n : ℝ) - s * p)

end

end CoarseDeGiorgi
