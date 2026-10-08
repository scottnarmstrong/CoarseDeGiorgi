module

public import Homogenization.Ambient.CoefficientField
public import CoarseDeGiorgi.Foundations.FracGeometry.SlicingRepresentative

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

theorem fractional_slicing_ae_representative {d : ℕ}
    {F F' : Vec d → ℝ} (hF : Measurable F) (hF' : Measurable F')
    (hEq : F =ᵐ[volume] F') :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo (1 / 2 : ℝ) 1)),
      F =ᵐ[surfaceMeasure τ] F' :=
  CoarseDeGiorgi.Foundations.FracGeometry.fractional_slicing_ae_representative_proved hF hF' hEq

end CoarseDeGiorgi
