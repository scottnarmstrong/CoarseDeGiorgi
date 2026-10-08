module

public import Homogenization.Ambient.CoefficientField
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

def IsWeightedCoeffOn {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) : Prop :=
  AEStronglyMeasurable a (volume.restrict V) ∧
    (∀ᵐ x ∂(volume.restrict V), (a x).PosDef) ∧
    IntegrableOn (fun x => (a x).trace) V ∧
    IntegrableOn (fun x => ((a x)⁻¹).trace) V

end CoarseDeGiorgi
