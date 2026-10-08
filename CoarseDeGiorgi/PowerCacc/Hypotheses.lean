module

public import CoarseDeGiorgi.Statements.WhitneyInterpolationDef
public import CoarseDeGiorgi.Statements.WhitneyAffineExtensionDef
public import CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension
public import CoarseDeGiorgi.Statements.IsTriadicWidth
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.ClosedReferenceCube
public import CoarseDeGiorgi.Statements.CubeSurface
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.SampledResponseSeries
public import CoarseDeGiorgi.Statements.SelectionInterval
public import CoarseDeGiorgi.Statements.SigmaLower
public import CoarseDeGiorgi.Statements.SigmaUpper
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import CoarseDeGiorgi.Statements.SurfaceMeasure
public import CoarseDeGiorgi.Statements.WhitneySimplicesNearSize
public import CoarseDeGiorgi.Statements.CubeFaceMeasure
public import CoarseDeGiorgi.Statements.SampledUpperResponse
public import CoarseDeGiorgi.Statements.UpperResponseOnCell
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Statements.SimplexIndex
public import CoarseDeGiorgi.Statements.WeightedEnergy

/-! # The three hypotheses of `power_caccioppoli_inequality_of_extension`

The definitions below give `l.exterior.integral`, `p.whitney.extension`
(with its binders turned into `∀`) and existence of a piecewise
harmonic extension, restricted to the narrower triadic widths used by this implementation. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi.PowerCacc

/-- `l.exterior.integral` restricted to widths at most δ/(20000 d). -/
def ExteriorIntegralHyp : Prop :=
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
              ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - ρ₁) / (20000 * (d : ℝ)) →
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
                                eLpNorm g (ENNReal.ofReal (paramR q)) (surfaceMeasure τ))

open scoped Classical in
/-- `p.whitney.extension` restricted to widths at most (ρ₂ − τ)/(10000 d). -/
def WhitneyHarmonicExtensionHyp : Prop :=
    ∀ (d : ℕ) (_hd : 3 ≤ d) (α ξ : ℝ)
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
          ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - τ) / (10000 * (d : ℝ)) →
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
                      0 ≤ (if x ∈ closedReferenceCube (d := d) τ then w x else H x)))

/-- Existence of a piecewise harmonic extension at widths at most (ρ₂ − τ)/(10000 d). -/
def PiecewiseHarmonicExtensionExistsHyp : Prop :=
    ∀ d : ℕ, 3 ≤ d → ∀ a : CoeffField d,
      IsWeightedCoeffOn (originCube 1) a →
      ∀ ρ₁ ρ₂ : ℝ, (hρ₁ : 1 / 2 ≤ ρ₁) → (hρ₁₂ : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        ∀ τ : ℝ, (hJ : τ ∈ selectionInterval ρ₁ ρ₂) →
          let hτ0 : (1 / 2 : ℝ) ≤ τ := by
            have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
            linarith
          let hτ1 : τ < 1 := by
            have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
            linarith
          ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - τ) / (10000 * (d : ℝ)) →
            ∀ f : Vec d → ℝ, (∃ K : ℝ≥0, LipschitzOnWith K f (cubeSurface τ)) →
              ∃ (H : Vec d → ℝ) (GH : Vec d → Vec d),
                IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH

end CoarseDeGiorgi.PowerCacc
