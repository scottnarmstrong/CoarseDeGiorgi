import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

def IsWeightedCoeffOn {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) : Prop :=
  AEStronglyMeasurable a (volume.restrict V) ∧
    (∀ᵐ x ∂(volume.restrict V), (a x).PosDef) ∧
    IntegrableOn (fun x => (a x).trace) V ∧
    IntegrableOn (fun x => ((a x)⁻¹).trace) V

end CoarseDeGiorgi
