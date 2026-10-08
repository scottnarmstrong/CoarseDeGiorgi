module

public import CoarseDeGiorgi.Statements.FracSeminorm
public import Homogenization.Ambient.CoefficientField
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def MemDnpvSobolev {n : ℕ} (V : Set (Vec n)) (s p : ℝ)
    (f : Vec n → ℝ) : Prop :=
  MemLp f (ENNReal.ofReal p) (volume.restrict V) ∧ fracSeminorm V s p f < ⊤

end

end CoarseDeGiorgi
