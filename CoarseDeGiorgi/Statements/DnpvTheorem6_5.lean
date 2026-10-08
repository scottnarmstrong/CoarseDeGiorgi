import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Prod
import CoarseDeGiorgi.Foundations.FractionalSobolev.Sobolev

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

theorem dnpv_theorem_6_5 :
    ∀ n : ℕ, ∀ s p : ℝ, 0 < s → s < 1 → 1 ≤ p → s * p < (n : ℝ) →
      ∃ C : ℝ, 0 < C ∧
        ∀ f : Vec n → ℝ, Measurable f → HasCompactSupport f →
          (eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent n s p)) volume).rpow p ≤
            ENNReal.ofReal C *
              ∫⁻ xy : Vec n × Vec n, fracKernel s p f xy ∂(volume.prod volume) :=
  by exact @CoarseDeGiorgi.Foundations.FractionalSobolev.dnpv_theorem_6_5_proved

end CoarseDeGiorgi
