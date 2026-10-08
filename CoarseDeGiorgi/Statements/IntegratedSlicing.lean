module

public import Homogenization.Ambient.CoefficientField
public import CoarseDeGiorgi.Statements.SurfaceFracNorm
public import CoarseDeGiorgi.Statements.FracNorm

public import CoarseDeGiorgi.Foundations.Slicing.Integrated

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

/-- Lemma `l.fractional.slicing`, estimate `e.boundary.slicing`: the constant is `C 2^ξ` with `C` depending
only on `d`; it is chosen before `α` and `ξ`. -/
theorem integrated_slicing {d : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α ξ : ℝ}, 0 < α → α < 1 → 1 < ξ →
      ∀ F : Vec d → ℝ, Measurable F →
        ∀ I : Set ℝ, MeasurableSet I → I ⊆ Set.Ioo (1 / 2 : ℝ) 1 →
          ∫⁻ τ in I, ENNReal.rpow (surfaceFracNorm τ α ξ F) ξ ∂volume ≤
            ENNReal.ofReal (C * (2 : ℝ) ^ ξ) * ENNReal.rpow (fracNorm Set.univ α ξ F) ξ
:=
  CoarseDeGiorgi.Foundations.Slicing.integrated_slicing_proved

end CoarseDeGiorgi
