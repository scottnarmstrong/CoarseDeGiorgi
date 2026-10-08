module

public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace CoarseDeGiorgi

noncomputable def powerFactor (m : ℝ) : ℝ := |m| / (1 - 2 * m)

end CoarseDeGiorgi
