import CoarseDeGiorgi.Statements.WhitneyAffineExtensionDef
import CoarseDeGiorgi.Statements.WhitneySimplicesNearSize
import CoarseDeGiorgi.Statements.EuclidLipConst
import CoarseDeGiorgi.Statements.IsTriadicWidth
import CoarseDeGiorgi.Statements.SelectionInterval
import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
import CoarseDeGiorgi.Statements.OriginCube

import CoarseDeGiorgi.Whitney.Extension.WideAffine
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

/-- Proposition `p.affine.extension`: the piecewise affine extension `L_h f`.  It is linear in `f`,
nonnegative when `f ≥ 0`, a Lipschitz extension of `f` to `ℝ^d ∖ τ□₀`, has values between `min {0, min f}` and
`max {0, max f}`, vanishes off `𝒲_h`, has the simplices of `𝒲_h` and its support in `(τ+3h)□̄₀ ⋐ ρ₂□₀`, and obeys
`e.extension.scale`.  The width is `0 < h ≤ (ρ₂-τ)/(100 d)` (`e.extension.width`).  One constant `C = C(d, α, ξ) < ∞`
serves the scale estimate. -/
theorem affine_extension (d : ℕ) (_hd : 3 ≤ d) (α ξ : ℝ)
    (_hα0 : 0 < α) (_hα1 : α < 1) (_hξ1 : 1 ≤ ξ) (_hξ2 : ξ ≤ 2) :
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
                      eLpNorm f (ENNReal.ofReal b) (surfaceMeasure τ)) ^ 2)
:=
  by exact CoarseDeGiorgi.WhitneyExt.affine_extension_wide d _hd α ξ _hα0 _hα1 _hξ1 _hξ2

end CoarseDeGiorgi
