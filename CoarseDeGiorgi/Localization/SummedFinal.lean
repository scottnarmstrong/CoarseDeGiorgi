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
public import CoarseDeGiorgi.Localization.SummedChosen

/-! Proposition `p.fractional.localization`: the localization bound, assembled from the summed
local bounds. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Localization

open CoarseDeGiorgi

theorem fractional_localization_proved :
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
:= by
  intro d hd
  have hKann : ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      ∃ m, GoodLevel (localizationAnnulus (d := d) ρ₁ ρ₂) ρ₁ ρ₂ m :=
    fun ρ₁ ρ₂ h1 h12 h2 => exists_goodLevel_annulus h1 h12 h2
  have hKinn : ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      ∃ m, GoodLevel {x : Vec d | ∀ i, |x i| ≤ ρ₁ / 2} ρ₁ ρ₂ m :=
    fun ρ₁ ρ₂ h1 h12 h2 => exists_goodLevel_inner h1 h12 h2
  let annK : ℝ → ℝ → Set (Vec d) := fun ρ₁ ρ₂ => localizationAnnulus ρ₁ ρ₂
  let innK : ℝ → ℝ → Set (Vec d) := fun ρ₁ _ => {x | ∀ i, |x i| ≤ ρ₁ / 2}
  refine ⟨chosenS annK, chosenPhi annK, chosenS innK, chosenPhi innK, ?_, ?_⟩
  · intro ρ₁ ρ₂ h1 h12 h2
    exact ⟨chosen_isFractionalCover (hKann ρ₁ ρ₂ h1 h12 h2),
      chosen_isFractionalCover (hKinn ρ₁ ρ₂ h1 h12 h2)⟩
  · intro p q s t hp hq hs ht hθ
    obtain ⟨C₁, hC₁, hF₁⟩ := chosen_family hd hp hq hs ht hθ annK hKann
    obtain ⟨C₂, hC₂, hF₂⟩ := chosen_family hd hp hq hs ht hθ innK hKinn
    refine ⟨C₁ + C₂, ENNReal.add_lt_top.mpr ⟨hC₁, hC₂⟩, ?_⟩
    intro a ha hrange ρ₁ ρ₂ h1 h12 h2
    refine ⟨?_, ?_⟩
    · intro v G hv
      obtain ⟨hbd, hconv⟩ := hF₁ a ha hrange ρ₁ ρ₂ h1 h12 h2 v G hv
      refine ⟨?_, hbd.trans (by gcongr; exact le_self_add), hconv⟩
      intro τ hτ
      obtain ⟨⟨hlo, hhi, hcover, b, hb, hbm⟩, hZ⟩ := chosen_spec (Kf := annK) (hKann ρ₁ ρ₂ h1 h12 h2)
      obtain ⟨U, hU, hKU, heq⟩ := localizedFunction_eq_on_neighborhood hcover v
      have hsurf : cubeSurface (d := d) τ ⊆ localizationAnnulus ρ₁ ρ₂ := fun x hx =>
        mem_localizationAnnulus_of_radius h12 hτ.1 hτ.2 (by
          have : ‖x‖ = τ / 2 := hx
          linarith)
      refine ⟨U, hU, hsurf.trans hKU, ?_⟩
      refine ae_restrict_of_forall_mem hU.measurableSet fun x hx => ?_
      rw [sum_chosenS, hZ]
      exact heq hx
    · intro v G hv
      obtain ⟨hbd, hconv⟩ := hF₂ a ha hrange ρ₁ ρ₂ h1 h12 h2 v G hv
      refine ⟨?_, hbd.trans (by gcongr; exact le_add_self), hconv⟩
      obtain ⟨⟨hlo, hhi, hcover, b, hb, hbm⟩, hZ⟩ := chosen_spec (Kf := innK) (hKinn ρ₁ ρ₂ h1 h12 h2)
      obtain ⟨U, hU, hKU, heq⟩ := localizedFunction_eq_on_neighborhood hcover v
      have hcl : closure (originCube (d := d) ρ₁) ⊆ {x : Vec d | ∀ i, |x i| ≤ ρ₁ / 2} := by
        refine closure_minimal (fun x hx i => abs_le.mpr ⟨(hx i).1.le, (hx i).2.le⟩) ?_
        have : {x : Vec d | ∀ i, |x i| ≤ ρ₁ / 2} = ⋂ i, {x : Vec d | |x i| ≤ ρ₁ / 2} := by
          ext x; simp
        rw [this]
        exact isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const
      refine ⟨U, hU, hcl.trans hKU, ?_⟩
      refine ae_restrict_of_forall_mem hU.measurableSet fun x hx => ?_
      rw [sum_chosenS, hZ]
      exact heq hx

end CoarseDeGiorgi.Localization
