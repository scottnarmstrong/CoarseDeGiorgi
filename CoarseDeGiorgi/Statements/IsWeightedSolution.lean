import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.Statements.SmoothGrad
import Homogenization.Ambient.CoefficientField
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable def IsWeightedSolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      IntegrableOn
        (fun x => vecDot (smoothGrad φ x) (matVecMul (a x) (G x))) V ∧
      ∫ x in V,
        vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) ∂volume = 0

end CoarseDeGiorgi
