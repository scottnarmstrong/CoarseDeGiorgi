module

public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace CoarseDeGiorgi

def selectionInterval (ρ R : ℝ) : Set ℝ :=
  Set.Ioo (ρ + (R - ρ) / 4) (ρ + (R - ρ) / 2)

end CoarseDeGiorgi
