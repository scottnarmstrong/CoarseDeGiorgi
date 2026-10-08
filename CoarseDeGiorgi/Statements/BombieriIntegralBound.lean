import CoarseDeGiorgi.Statements.OriginCube
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CoarseDeGiorgi.Harnack.Scalar.Bombieri

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi

theorem bombieri_integral_bound (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (A₁ A₂ : ℝ), 1 ≤ A₁ → 1 ≤ A₂ →
        ∀ v : Vec d → ℝ,
          Measurable (fun x : originCube (d := d) (7 / 8) => v x) →
          (∀ᵐ x ∂(volume.restrict (originCube (7 / 8))), 0 < v x) →
          IntegrableOn v (originCube (7 / 8)) →
          eLpNorm (fun x => Real.log (v x)) 1
            (volume.restrict (originCube (7 / 8))) ≤ ENNReal.ofReal A₁ →
          (∀ b : ℝ, 0 < b → b < 1 →
            ∀ ρ R : ℝ, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
              eLpNorm v 1 (volume.restrict (originCube ρ)) ≤
                (ENNReal.ofReal (A₂ * (R - ρ) ^ (-ξ))) ^ (1 / b) *
                  eLpNorm v (ENNReal.ofReal b) (volume.restrict (originCube R))) →
          eLpNorm v 1 (volume.restrict (originCube (3 / 4))) ≤
            ENNReal.ofReal (Real.exp (C * A₁ * A₂ ^ 6)) :=
  CoarseDeGiorgi.bombieri_integral_bound_proved ξ hξ

end CoarseDeGiorgi
