module

public import CoarseDeGiorgi.ExteriorIntegral.CoreWide
public import CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension
public import CoarseDeGiorgi.Statements.IsTriadicWidth
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.SimplexIndex
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.ClosedReferenceCube
public import CoarseDeGiorgi.Statements.CubeFaceMeasure
public import CoarseDeGiorgi.Statements.CubeSurface
public import CoarseDeGiorgi.Statements.EuclidLipConst
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.SampledResponseSeries
public import CoarseDeGiorgi.Statements.SampledUpperResponse
public import CoarseDeGiorgi.Statements.SelectionInterval
public import CoarseDeGiorgi.Statements.SigmaLower
public import CoarseDeGiorgi.Statements.SigmaUpper
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import CoarseDeGiorgi.Statements.SurfaceMeasure
public import CoarseDeGiorgi.Statements.UpperResponseOnCell
public import CoarseDeGiorgi.Statements.WeightedEnergy
public import CoarseDeGiorgi.Statements.WhitneyAffineExtensionDef
public import CoarseDeGiorgi.Statements.WhitneySimplicesNearSize
public import CoarseDeGiorgi.Weighted.Energy
public import Homogenization.Ambient.CoefficientField
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # The exterior integral from the two extension propositions

`exterior_integral_bound_of_extension` proves Lemma `l.exterior.integral` from the statements of
Propositions `p.affine.extension` and `p.whitney.extension`, which are taken verbatim as
hypotheses. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.ExteriorIntegral.WideWidth

open CoarseDeGiorgi ExteriorIntegral

noncomputable section

open scoped Classical in
theorem exterior_integral_bound_of_extension
    (h61 : ∀ (d : ℕ) (_hd : 3 ≤ d) (α ξ : ℝ)
    (_hα0 : 0 < α) (_hα1 : α < 1) (_hξ1 : 1 ≤ ξ) (_hξ2 : ξ ≤ 2),
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ρ₁ ρ₂ : ℝ, (hρ₁ : 1 / 2 ≤ ρ₁) → (hρ₁₂ : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        ∀ τ : ℝ, (hJ : τ ∈ selectionInterval ρ₁ ρ₂) →
          let hτ0 : (1 / 2 : ℝ) ≤ τ := by
            have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
            linarith
          let hτ1 : τ < 1 := by
            have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
            linarith
          ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - τ) / (100 * (d : ℝ)) →
            -- linearity in `f`
            (∀ f₁ f₂ : Vec d → ℝ,
              (∃ K : ℝ≥0, LipschitzOnWith K f₁ (cubeSurface τ)) →
              (∃ K : ℝ≥0, LipschitzOnWith K f₂ (cubeSurface τ)) →
              ∀ c₁ c₂ : ℝ, ∀ x ∈ (closedReferenceCube (d := d) τ)ᶜ,
                whitneyAffineExtension τ h (fun y => c₁ * f₁ y + c₂ * f₂ y) hτ0 hτ1 x =
                  c₁ * whitneyAffineExtension τ h f₁ hτ0 hτ1 x +
                    c₂ * whitneyAffineExtension τ h f₂ hτ0 hτ1 x) ∧
            ∀ f : Vec d → ℝ, (∃ K : ℝ≥0, LipschitzOnWith K f (cubeSurface τ)) →
              -- nonnegativity
              ((∀ y ∈ cubeSurface (d := d) τ, 0 ≤ f y) →
                ∀ x ∈ (closedReferenceCube (d := d) τ)ᶜ,
                  0 ≤ whitneyAffineExtension τ h f hτ0 hτ1 x) ∧
              -- a Lipschitz extension of `f` to `ℝ^d ∖ τ□₀`
              (∃ F : Vec d → ℝ,
                (∀ x ∈ (closedReferenceCube (d := d) τ)ᶜ,
                  F x = whitneyAffineExtension τ h f hτ0 hτ1 x) ∧
                (∀ y ∈ cubeSurface (d := d) τ, F y = f y) ∧
                euclidLipConst (originCube (d := d) τ)ᶜ F < ⊤) ∧
              -- values between `min {0, min f}` and `max {0, max f}`
              (∀ m M : ℝ, m ≤ 0 → 0 ≤ M →
                (∀ y ∈ cubeSurface (d := d) τ, m ≤ f y ∧ f y ≤ M) →
                ∀ x ∈ (closedReferenceCube (d := d) τ)ᶜ,
                  m ≤ whitneyAffineExtension τ h f hτ0 hτ1 x ∧
                    whitneyAffineExtension τ h f hτ0 hτ1 x ≤ M) ∧
              -- vanishing off `𝒲_h`
              (∀ cell : ExteriorCell d τ, cell ∉ whitneySimplicesNear τ h →
                ∀ x ∈ exteriorCellSet cell, whitneyAffineExtension τ h f hτ0 hτ1 x = 0) ∧
              -- support: closures in `(τ + 3h)□̄₀ ⋐ ρ₂□₀`
              ((∀ cell : ExteriorCell d τ, cell ∈ whitneySimplicesNear τ h →
                  closure (exteriorCellSet cell) ⊆ closedReferenceCube (d := d) (τ + 3 * h)) ∧
                closure {x | x ∈ (closedReferenceCube (d := d) τ)ᶜ ∧
                    whitneyAffineExtension τ h f hτ0 hτ1 x ≠ 0} ⊆
                  closedReferenceCube (d := d) (τ + 3 * h) ∧
                closedReferenceCube (d := d) (τ + 3 * h) ⊆ originCube (d := d) ρ₂) ∧
              -- `e.extension.scale`
              (∀ (j : ℕ) (b : ℝ), (b = 2 ∨ b = ξ) →
                ∑' cell : whitneySimplicesNearSize (d := d) τ h j,
                  ∫⁻ x in exteriorCellSet cell.1,
                    ENNReal.ofReal (vecNormSq
                      (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)) ≤
                  C * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
                    (ENNReal.ofReal ((3 : ℝ) ^ (j : ℤ) *
                        (3 : ℝ) ^ (-((j : ℝ) *
                          (α - ((d : ℝ) - 1) * (1 / ξ - 1 / 2))))) *
                      surfaceFracSeminorm τ α ξ f) ^ 2 +
                  C * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
                    (ENNReal.ofReal (h⁻¹ * (3 : ℝ) ^ ((j : ℝ) *
                        (((d : ℝ) - 1) * (1 / b - 1 / 2)))) *
                      eLpNorm f (ENNReal.ofReal b) (surfaceMeasure τ)) ^ 2))
    (h62 : ∀ (d : ℕ) (_hd : 3 ≤ d) (α ξ : ℝ)
    (_hα0 : 0 < α) (_hα1 : α < 1) (_hξ1 : 1 ≤ ξ) (_hξ2 : ξ ≤ 2),
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
      ∀ ρ₁ ρ₂ : ℝ, (hρ₁ : 1 / 2 ≤ ρ₁) → (hρ₁₂ : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        ∀ τ : ℝ, (hJ : τ ∈ selectionInterval ρ₁ ρ₂) →
          let hτ0 : (1 / 2 : ℝ) ≤ τ := by
            have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
            linarith
          let hτ1 : τ < 1 := by
            have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
            linarith
          ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - τ) / (100 * (d : ℝ)) →
            -- linearity in `f`
            (∀ f₁ f₂ : Vec d → ℝ,
              (∃ K : ℝ≥0, LipschitzOnWith K f₁ (cubeSurface τ)) →
              (∃ K : ℝ≥0, LipschitzOnWith K f₂ (cubeSurface τ)) →
              ∀ c₁ c₂ : ℝ,
              ∀ (H₁ H₂ H : Vec d → ℝ) (GH₁ GH₂ GH : Vec d → Vec d),
                IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f₁ H₁ GH₁ →
                IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f₂ H₂ GH₂ →
                IsPiecewiseHarmonicExtension a τ h hτ0 hτ1
                  (fun y => c₁ * f₁ y + c₂ * f₂ y) H GH →
                ∀ᵐ x ∂(volume.restrict (closedReferenceCube (d := d) τ)ᶜ),
                  H x = c₁ * H₁ x + c₂ * H₂ x ∧ GH x = c₁ • GH₁ x + c₂ • GH₂ x) ∧
            ∀ f : Vec d → ℝ, (∃ K : ℝ≥0, LipschitzOnWith K f (cubeSurface τ)) →
            ∀ (H : Vec d → ℝ) (GH : Vec d → Vec d),
              IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH →
              -- nonnegativity
              ((∀ y ∈ cubeSurface (d := d) τ, 0 ≤ f y) →
                ∀ᵐ x ∂(volume.restrict (closedReferenceCube (d := d) τ)ᶜ), 0 ≤ H x) ∧
              -- the range bound of `L_h f`
              (∀ m M : ℝ, m ≤ 0 → 0 ≤ M →
                (∀ y ∈ cubeSurface (d := d) τ, m ≤ f y ∧ f y ≤ M) →
                ∀ᵐ x ∂(volume.restrict (closedReferenceCube (d := d) τ)ᶜ),
                  m ≤ H x ∧ H x ≤ M) ∧
              -- ordinary trace `f` on `∂(τ□₀)`
              (∀ (i : Fin d) (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ originCube (d := d) 1 →
                ∫ x in originCube (d := d) 1 \ closedReferenceCube (d := d) τ,
                    (H x * fderiv ℝ φ x (basisVec i) + GH x i * φ x) =
                  (∫ x, f x * φ x ∂(cubeFaceMeasure τ i false)) -
                    ∫ x, f x * φ x ∂(cubeFaceMeasure τ i true)) ∧
              -- `H_h f ∈ W^{1,1}(□₀ ∖ τ□̄₀)` with finite energy
              (Integrable H (volume.restrict
                  (originCube (d := d) 1 \ closedReferenceCube (d := d) τ)) ∧
                Integrable GH (volume.restrict
                  (originCube (d := d) 1 \ closedReferenceCube (d := d) τ)) ∧
                HasWeakGradientOn
                  (originCube (d := d) 1 \ closedReferenceCube (d := d) τ) H GH ∧
                weightedEnergy a
                  (originCube (d := d) 1 \ closedReferenceCube (d := d) τ) GH < ⊤) ∧
              -- vanishes outside `(τ + 3h)□̄₀`
              (∀ᵐ x ∂(volume.restrict (closedReferenceCube (d := d) (τ + 3 * h))ᶜ),
                H x = 0) ∧
              -- `e.harmonic.energy`
              (∀ (j : ℕ) (cell : ExteriorCell d τ),
                cell ∈ whitneySimplicesNearSize (d := d) τ h j →
                ∃ η : SimplexIndex d j, exteriorCellSet cell = simplexCell j η ∧
                  ∀ x ∈ exteriorCellSet cell,
                    weightedEnergy a (exteriorCellSet cell) GH =
                      volume (exteriorCellSet cell) *
                        ENNReal.ofReal
                          (vecDot (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)
                            (matVecMul (upperResponseOnCell j a ha η)
                              (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x))) ∧
                    volume (exteriorCellSet cell) *
                        ENNReal.ofReal
                          (vecDot (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)
                            (matVecMul (upperResponseOnCell j a ha η)
                              (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x))) ≤
                      sampledUpperResponse a ha j τ *
                        (volume (exteriorCellSet cell) *
                          ENNReal.ofReal (vecNormSq
                            (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)))) ∧
              -- the estimate `e.extension.scale` with the extra factor `A_j(τ)`
              (∀ (j : ℕ) (b : ℝ), (b = 2 ∨ b = ξ) →
                ∑' cell : whitneySimplicesNearSize (d := d) τ h j,
                  weightedEnergy a (exteriorCellSet cell.1) GH ≤
                  sampledUpperResponse a ha j τ *
                    (C * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
                      (ENNReal.ofReal ((3 : ℝ) ^ (j : ℤ) *
                          (3 : ℝ) ^ (-((j : ℝ) *
                            (α - ((d : ℝ) - 1) * (1 / ξ - 1 / 2))))) *
                        surfaceFracSeminorm τ α ξ f) ^ 2 +
                    C * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
                      (ENNReal.ofReal (h⁻¹ * (3 : ℝ) ^ ((j : ℝ) *
                          (((d : ℝ) - 1) * (1 / b - 1 / 2)))) *
                        eLpNorm f (ENNReal.ofReal b) (surfaceMeasure τ)) ^ 2)) ∧
              -- gluing with a Lipschitz `w` on `τ□̄₀`
              (∀ w : Vec d → ℝ,
                (∃ K : ℝ≥0, LipschitzOnWith K w (closedReferenceCube (d := d) τ)) →
                (∀ y ∈ cubeSurface (d := d) τ, w y = f y) →
                ∃ G : Vec d → Vec d,
                  MemH1a0 a (originCube (d := d) 1)
                    (fun x => if x ∈ closedReferenceCube (d := d) τ then w x else H x) G ∧
                  (∃ K : Set (Vec d), IsCompact K ∧ K ⊆ originCube (d := d) ρ₂ ∧
                    ∀ᵐ x ∂volume, x ∉ K →
                      (if x ∈ closedReferenceCube (d := d) τ then w x else H x) = 0) ∧
                  ((∀ x ∈ closedReferenceCube (d := d) τ, 0 ≤ w x) →
                    ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)),
                      0 ≤ (if x ∈ closedReferenceCube (d := d) τ then w x else H x)))) :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ ρ₁ ρ₂ : ℝ, (hρ₁ : 1 / 2 ≤ ρ₁) → (hρ₁₂ : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
            ∀ τ : ℝ, (hJ : τ ∈ selectionInterval ρ₁ ρ₂) →
              let hτ0 : (1 / 2 : ℝ) ≤ τ := by
                have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
                linarith
              let hτ1 : τ < 1 := by
                have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
                linarith
              ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - ρ₁) / (200 * (d : ℝ)) →
                ∀ (g : Vec d → ℝ),
                  (∃ K : ℝ≥0, LipschitzOnWith K g (cubeSurface τ)) →
                    ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
                      MemH1a a (originCube 1) v G →
                      ∀ (H : Vec d → ℝ) (GH : Vec d → Vec d),
                        IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 g H GH →
                        Integrable (fun x => vecDot (GH x) (matVecMul (a x) (G x)))
                          (volume.restrict (originCube 1 \ closedReferenceCube (d := d) τ)) ∧
                        ENNReal.ofReal |∫ x in originCube 1 \ closedReferenceCube (d := d) τ,
                          vecDot (GH x) (matVecMul (a x) (G x))| ≤
                          C * sampledResponseSeries a ha s p τ *
                            (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                            ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                              surfaceFracSeminorm τ (alphaParam t) (paramR q) g +
                              (ENNReal.ofReal h).rpow (-(sigmaUpper d p s)) *
                                eLpNorm g 2 (surfaceMeasure τ)) ∧
                        ENNReal.ofReal |∫ x in originCube 1 \ closedReferenceCube (d := d) τ,
                          vecDot (GH x) (matVecMul (a x) (G x))| ≤
                          C * sampledResponseSeries a ha s p τ *
                            (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                            ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                              surfaceFracSeminorm τ (alphaParam t) (paramR q) g +
                              (ENNReal.ofReal h).rpow
                                (-(sigmaUpper d p s + sigmaLower d q t - t)) *
                                eLpNorm g (ENNReal.ofReal (paramR q)) (surfaceMeasure τ)) := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hNZ : NeZero (n + 1) := ⟨by omega⟩
  have hdr : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hd
  have hp0 : 0 < p := by linarith only [hp]
  have hq0 : 0 < q := by linarith only [hq]
  have hX : 0 < ((((n + 1 : ℕ) : ℝ) - 1) / 2) * (1 / p + 1 / q) := by
    have : 0 < (((n + 1 : ℕ) : ℝ) - 1) / 2 := by linarith only [hdr]
    positivity
  have hθ' : 0 < 1 - s - t - ((((n + 1 : ℕ) : ℝ) - 1) / 2) * (1 / p + 1 / q) := hθ
  have hα : 0 < alphaParam t := by unfold alphaParam; linarith only [hθ', hX, hs]
  have hα1 : alphaParam t < 1 := by unfold alphaParam; linarith only [ht]
  have hr1 : 1 ≤ paramR q := by
    unfold paramR
    rw [le_div_iff₀ (by linarith only [hq])]
    linarith only [hq]
  have hr2 : paramR q ≤ 2 := by
    unfold paramR
    rw [div_le_iff₀ (by linarith only [hq])]
    linarith only [hq]
  obtain ⟨C₂, hC₂, hmain⟩ := h62 (n + 1) hd (alphaParam t) (paramR q) hα hα1 hr1 hr2
  have _h61 := h61
  refine ⟨(54 * C₂) ^ (1 / 2 : ℝ), ?_, ?_⟩
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top (by simp) hC₂.ne)
  intro a ha hrange ρ₁ ρ₂ hρ₁ hρ₁₂ hρ₂ τ hJ
  have hm := hmain a ha ρ₁ ρ₂ hρ₁ hρ₁₂ hρ₂ τ hJ
  dsimp only at hm ⊢
  have hτ0 : (1 / 2 : ℝ) ≤ τ := by
    have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
    linarith
  have hτ1 : τ < 1 := by
    have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
    linarith
  intro h hhtri hhw g hg v G hv H GH hext
  have hhpos : 0 < h := by
    obtain ⟨m, rfl⟩ := hhtri
    positivity
  have hhw' : h ≤ (ρ₂ - τ) / (100 * (((n + 1 : ℕ) : ℝ))) := by
    have hτ2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
    have hden : 0 < 100 * (((n + 1 : ℕ) : ℝ)) := by positivity
    have h20 : 0 < 200 * (((n + 1 : ℕ) : ℝ)) := by positivity
    have := (le_div_iff₀ h20).mp hhw
    rw [le_div_iff₀ hden]
    nlinarith only [this, hτ2, hhpos, hdr, hρ₁₂]
  have hh1 : h ≤ 1 := by
    have h20 : 0 < 200 * (((n + 1 : ℕ) : ℝ)) := by positivity
    have := (le_div_iff₀ h20).mp hhw
    nlinarith only [this, hρ₂, hρ₁, hρ₁₂, hhpos, hdr]
  obtain ⟨-, hrest⟩ := hm h hhtri hhw'
  obtain ⟨-, -, -, hfin, -, -, h64, -⟩ := hrest g hg H GH hext
  obtain ⟨-, hGHint, -, hGHen⟩ := hfin
  -- the standing facts
  set Ω : Set (Vec (n + 1)) := originCube 1 \ closedReferenceCube (d := n + 1) τ with hΩ
  have hΩsub : Ω ⊆ originCube 1 := fun _ hx => hx.1
  have haΩ : IsWeightedCoeffOn Ω a := Whitney.lift_coeff_mono ha hΩsub
  have hGm : AEStronglyMeasurable G (volume.restrict Ω) :=
    hv.2.1.mono_measure (Measure.restrict_mono hΩsub le_rfl)
  have hEG : weightedEnergy a Ω G < ⊤ := by
    have hEw : weightedEnergy a (originCube 1) G < ⊤ :=
      Weighted.MemH1a.energy_lt_top
        (Whitney.source_cube_domain (d := n + 1) (by norm_num : (0 : ℝ) < 1)).isOpen ha hv
    exact (lintegral_mono_set hΩsub).trans_lt hEw
  refine ⟨(Weighted.pairing_integrable_and_bound haΩ hGHint.aestronglyMeasurable hGm
    hGHen hEG).1, ?_⟩
  have hvan : ∀ cell : ExteriorCell (n + 1) τ, cell ∉ whitneySimplicesNear τ h →
      ∀ᵐ x ∂(volume.restrict (exteriorCellSet cell)), GH x = 0 := fun cell hn =>
    ((hext cell).2 hn).mono fun x hx => hx.2
  -- parameters
  set σ : ℝ := sigmaUpper (n + 1) p s with hσdef
  have hσ' : σ = s + ((((n + 1 : ℕ) : ℝ)) - 1) / (2 * p) := rfl
  have hβ0 : ((((n + 1 : ℕ) : ℝ)) - 1) * (1 / paramR q - 1 / 2) =
      ((((n + 1 : ℕ) : ℝ)) - 1) / (2 * q) := by
    unfold paramR
    field_simp
    ring
  have hσL : sigmaLower (n + 1) q t = t + ((((n + 1 : ℕ) : ℝ)) - 1) / (2 * q) := rfl
  have hθeq : paramTheta (n + 1) p q s t =
      1 - σ - (t + ((((n + 1 : ℕ) : ℝ)) - 1) / (2 * q)) := by
    unfold paramTheta
    rw [hσ']
    field_simp
    ring
  have hqpos : 0 < ((((n + 1 : ℕ) : ℝ)) - 1) / (2 * q) := by
    apply div_pos (by linarith only [hdr]) (by linarith only [hq])
  have hγ : alphaParam t - ((((n + 1 : ℕ) : ℝ)) - 1) * (1 / paramR q - 1 / 2) =
      σ + paramTheta (n + 1) p q s t := by
    unfold alphaParam
    rw [hβ0, hθeq]
    ring
  have hS : (sampledResponseSeries a ha s p τ) =
      ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * σ))) *
        (sampledUpperResponse a ha k τ) ^ (1 / 2 : ℝ) := rfl
  have hβ2 : ((((n + 1 : ℕ) : ℝ)) - 1) * (1 / 2 - 1 / 2) = 0 := by norm_num
  constructor
  · have hcore := exterior_bound_core (n := n) ha hd hρ₁ hρ₂ hJ hτ0 hτ1 hhpos hh1 hhw hv
      hGHint.aestronglyMeasurable hvan (σ := σ) (θ := paramTheta (n + 1) p q s t)
      (γ := alphaParam t - ((((n + 1 : ℕ) : ℝ)) - 1) * (1 / paramR q - 1 / 2))
      (β := ((((n + 1 : ℕ) : ℝ)) - 1) * (1 / 2 - 1 / 2)) hθ hγ
      (by rw [hβ2]; linarith only [hθeq, hθ, hqpos, ht])
      C₂ (surfaceFracSeminorm τ (alphaParam t) (paramR q) g)
      (eLpNorm g (ENNReal.ofReal 2) (surfaceMeasure τ))
      (fun j => h64 j 2 (Or.inl rfl))
    have e1 : -(σ + ((((n + 1 : ℕ) : ℝ)) - 1) * (1 / 2 - 1 / 2)) = -σ := by
      rw [hβ2]; ring
    have e2 : ENNReal.ofReal 2 = 2 := by simp
    rw [e1, e2] at hcore
    rw [hS]
    exact hcore
  · have hcore := exterior_bound_core (n := n) ha hd hρ₁ hρ₂ hJ hτ0 hτ1 hhpos hh1 hhw hv
      hGHint.aestronglyMeasurable hvan (σ := σ) (θ := paramTheta (n + 1) p q s t)
      (γ := alphaParam t - ((((n + 1 : ℕ) : ℝ)) - 1) * (1 / paramR q - 1 / 2))
      (β := ((((n + 1 : ℕ) : ℝ)) - 1) * (1 / paramR q - 1 / 2)) hθ hγ
      (by rw [hβ0]; linarith only [hθeq, hθ, hqpos, ht])
      C₂ (surfaceFracSeminorm τ (alphaParam t) (paramR q) g)
      (eLpNorm g (ENNReal.ofReal (paramR q)) (surfaceMeasure τ))
      (fun j => h64 j (paramR q) (Or.inr rfl))
    have e1 : -(σ + ((((n + 1 : ℕ) : ℝ)) - 1) * (1 / paramR q - 1 / 2)) =
        -(sigmaUpper (n + 1) p s + sigmaLower (n + 1) q t - t) := by
      rw [hβ0, hσL, hσdef]; ring
    rw [e1] at hcore
    rw [hS]
    exact hcore

end

end CoarseDeGiorgi.ExteriorIntegral.WideWidth
