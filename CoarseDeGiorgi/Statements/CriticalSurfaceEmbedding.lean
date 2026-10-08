import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Foundations.FractionalSobolev.SurfaceEmbedding

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

theorem critical_surface_embedding {d : ℕ} {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r)
    (hcritical : α * r < (d : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧
        ∀ τ : ℝ, (1 / 2 : ℝ) ≤ τ → τ ≤ 1 →
        ∀ g : Vec d → ℝ, Measurable g →
          eLpNorm g
              (ENNReal.ofReal (((d : ℝ) - 1) * r /
                ((d : ℝ) - 1 - α * r))) (surfaceMeasure τ) ≤
            ENNReal.ofReal C * surfaceFracNorm τ α r g ∧
          (2 ≤ ((d : ℝ) - 1) * r / ((d : ℝ) - 1 - α * r) →
            eLpNorm g 2 (surfaceMeasure τ) ≤
              ENNReal.ofReal C * surfaceFracNorm τ α r g) :=
  CoarseDeGiorgi.Foundations.FractionalSobolev.critical_surface_embedding_proved hα0 hα1 hr hcritical

end CoarseDeGiorgi
