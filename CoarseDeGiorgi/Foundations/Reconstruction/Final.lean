module

public import CoarseDeGiorgi.Foundations.Reconstruction.Assembly
public import CoarseDeGiorgi.Foundations.Reconstruction.TailBounds
public import CoarseDeGiorgi.Foundations.Reconstruction.Smoothing

/-! # The all-dimensional fractional reconstruction theorem -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

theorem fractional_reconstruction_proved {d : ℕ} {α r : ℝ}
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
                  (ENNReal.ofReal r) (volume.restrict (auxCube m z)) := by
  exact Foundations.Reconstruction.fractional_reconstruction_of_tail_bounds_smoothing
    hα0 hα1 hr (Foundations.Reconstruction.assemblyTailBounds hr)
    (Foundations.Reconstruction.assemblySmoothingConvergence hr)

end
end CoarseDeGiorgi
