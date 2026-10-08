import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Foundations.FractionalSobolev.UnitCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

theorem dnpv_theorem_6_7_unitCube :
    ∀ n : ℕ, ∀ s p : ℝ, 0 < s → s < 1 → 1 ≤ p → s * p < (n : ℝ) →
      ∃ C : ℝ, 0 < C ∧
        ∀ f : Vec n → ℝ, MemDnpvSobolev (dnpvUnitCube n) s p f →
          eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent n s p)) (volume.restrict (dnpvUnitCube n)) ≤
              ENNReal.ofReal C * fracNorm (dnpvUnitCube n) s p f :=
  by exact @CoarseDeGiorgi.Foundations.FractionalSobolev.dnpv_theorem_6_7_unitCube_proved

end CoarseDeGiorgi
