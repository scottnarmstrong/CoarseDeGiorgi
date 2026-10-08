module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.IsFractionalCover
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.CubeSurface
public import CoarseDeGiorgi.Statements.FracNorm
public import CoarseDeGiorgi.Statements.H1aWeightedNorm
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.SelectionInterval
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.WeightedEnergy

public import CoarseDeGiorgi.Localization.SummedFinal

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem fractional_localization :
    ∀ d : ℕ, 3 ≤ d →
      ∃ (S : ℝ → ℝ → Finset (ℤ × (Fin d → ℤ)))
        (φ : ℝ → ℝ → ℤ × (Fin d → ℤ) → Vec d → ℝ)
        (S' : ℝ → ℝ → Finset (ℤ × (Fin d → ℤ)))
        (φ' : ℝ → ℝ → ℤ × (Fin d → ℤ) → Vec d → ℝ),
      (∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        IsFractionalCover ρ₂ (S ρ₁ ρ₂) (φ ρ₁ ρ₂) ∧
        IsFractionalCover ρ₂ (S' ρ₁ ρ₂) (φ' ρ₁ ρ₂)) ∧
      ∀ p q s t : ℝ, (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
        0 < paramTheta d p q s t →
        ∃ C : ℝ≥0∞, C < ⊤ ∧
          ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
            spatialMomentRange a ha p q s t →
            ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
              (∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
                MemH1a a (originCube 1) v G →
                (∀ τ ∈ selectionInterval ρ₁ ρ₂,
                  ∃ U : Set (Vec d), IsOpen U ∧ cubeSurface τ ⊆ U ∧
                    ∀ᵐ x ∂(volume.restrict U),
                      ∑ i ∈ S ρ₁ ρ₂, φ ρ₁ ρ₂ i x * v x = v x) ∧
                fracNorm Set.univ (alphaParam t) (paramR q)
                    (fun x => ∑ i ∈ S ρ₁ ρ₂, φ ρ₁ ρ₂ i x * v x) ≤
                  C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-alphaParam t) *
                    ((lowerMoment a ha t q ht (le_of_lt hq)).rpow (-(1 / 2)) *
                        (weightedEnergy a (originCube ρ₂) G).rpow (1 / 2) +
                      eLpNorm v (ENNReal.ofReal (paramR q))
                        (volume.restrict (originCube ρ₂))) ∧
                ∀ (vⱼ : ℕ → Vec d → ℝ) (Gⱼ : ℕ → Vec d → Vec d),
                  (∀ j, MemH1a a (originCube 1) (vⱼ j) (Gⱼ j)) →
                  Filter.Tendsto
                    (fun j => h1aWeightedNorm a (originCube 1)
                      (fun x => vⱼ j x - v x) (fun x => Gⱼ j x - G x))
                    Filter.atTop (nhds 0) →
                  Filter.Tendsto
                    (fun j => fracNorm Set.univ (alphaParam t) (paramR q)
                      (fun x => (∑ i ∈ S ρ₁ ρ₂, φ ρ₁ ρ₂ i x * vⱼ j x) -
                        ∑ i ∈ S ρ₁ ρ₂, φ ρ₁ ρ₂ i x * v x))
                    Filter.atTop (nhds 0)) ∧
              (∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
                MemH1a a (originCube 1) v G →
                (∃ U : Set (Vec d), IsOpen U ∧ closure (originCube ρ₁) ⊆ U ∧
                  ∀ᵐ x ∂(volume.restrict U),
                    ∑ i ∈ S' ρ₁ ρ₂, φ' ρ₁ ρ₂ i x * v x = v x) ∧
                fracNorm Set.univ (alphaParam t) (paramR q)
                    (fun x => ∑ i ∈ S' ρ₁ ρ₂, φ' ρ₁ ρ₂ i x * v x) ≤
                  C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-alphaParam t) *
                    ((lowerMoment a ha t q ht (le_of_lt hq)).rpow (-(1 / 2)) *
                        (weightedEnergy a (originCube ρ₂) G).rpow (1 / 2) +
                      eLpNorm v (ENNReal.ofReal (paramR q))
                        (volume.restrict (originCube ρ₂))) ∧
                ∀ (vⱼ : ℕ → Vec d → ℝ) (Gⱼ : ℕ → Vec d → Vec d),
                  (∀ j, MemH1a a (originCube 1) (vⱼ j) (Gⱼ j)) →
                  Filter.Tendsto
                    (fun j => h1aWeightedNorm a (originCube 1)
                      (fun x => vⱼ j x - v x) (fun x => Gⱼ j x - G x))
                    Filter.atTop (nhds 0) →
                  Filter.Tendsto
                    (fun j => fracNorm Set.univ (alphaParam t) (paramR q)
                      (fun x => (∑ i ∈ S' ρ₁ ρ₂, φ' ρ₁ ρ₂ i x * vⱼ j x) -
                        ∑ i ∈ S' ρ₁ ρ₂, φ' ρ₁ ρ₂ i x * v x))
                    Filter.atTop (nhds 0))
:=
  CoarseDeGiorgi.Localization.fractional_localization_proved

end CoarseDeGiorgi
