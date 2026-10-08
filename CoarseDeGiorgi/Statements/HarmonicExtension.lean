module

public import CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension
public import CoarseDeGiorgi.Statements.WhitneySimplicesNearSize
public import CoarseDeGiorgi.Statements.IsTriadicWidth
public import CoarseDeGiorgi.Statements.SelectionInterval
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import CoarseDeGiorgi.Statements.CubeFaceMeasure
public import CoarseDeGiorgi.Statements.SampledUpperResponse
public import CoarseDeGiorgi.Statements.UpperResponseOnCell
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Statements.SimplexIndex
public import CoarseDeGiorgi.Statements.WeightedEnergy

public import CoarseDeGiorgi.Statements.AffineExtension
public import CoarseDeGiorgi.Whitney.Harmonic.Prop62Wide

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

open scoped Classical in
/-- Proposition `p.whitney.extension`.  `(H, GH)` is the piecewise harmonic
extension `H_h f` with its gradient (`IsPiecewiseHarmonicExtension`).  The "ordinary trace `f` on
`∂(τ□₀)`" is the Gauss-Green identity for `W^{1,1}(□₀ ∖ τ□̄₀)`, tested with smooth fields
supported in `□₀`.  One constant `C = C(d, α, ξ) < ∞` serves the last estimate. -/
theorem harmonic_extension (d : ℕ) (_hd : 3 ≤ d) (α ξ : ℝ)
    (_hα0 : 0 < α) (_hα1 : α < 1) (_hξ1 : 1 ≤ ξ) (_hξ2 : ξ ≤ 2) :
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
                      0 ≤ (if x ∈ closedReferenceCube (d := d) τ then w x else H x)))
:=
  Whitney.Harmonic.Wide.harmonic_extension_of_affine CoarseDeGiorgi.affine_extension d _hd α ξ _hα0 _hα1 _hξ1 _hξ2

end CoarseDeGiorgi
