module

public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.SmoothGrad
public import Homogenization.Ambient.CoefficientField
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def IsWeightedSubsolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) →
      IntegrableOn
        (fun x => vecDot (smoothGrad φ x) (matVecMul (a x) (G x))) V ∧
      ∫ x in V,
        vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) ∂volume ≤ 0

end CoarseDeGiorgi
