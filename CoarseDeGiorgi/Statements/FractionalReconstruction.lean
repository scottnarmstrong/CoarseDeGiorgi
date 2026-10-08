import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import CoarseDeGiorgi.Foundations.Reconstruction.Final

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

theorem fractional_reconstruction {d : ℕ} {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (Dw : Vec d → Vec d),
        HasWeakGradientOn (auxCube m z) w Dw →
        IntegrableOn w (auxCube m z) volume →
        IntegrableOn Dw (auxCube m z) volume →
        MemLp w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) →
        fracSeminorm (auxCube m z) α r w ≤
          ENNReal.ofReal C *
            ∑' k : {k : ℤ // m ≤ k},
              ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * (1 - α))) *
                eLpNorm (fun x => euclidNorm (auxAverage m k.1 z Dw x))
                  (ENNReal.ofReal r) (volume.restrict (auxCube m z)) :=
  CoarseDeGiorgi.fractional_reconstruction_proved hα0 hα1 hr

end CoarseDeGiorgi
