module

public import CoarseDeGiorgi.Whitney.Extension.WideLipschitz
public import CoarseDeGiorgi.Whitney.Extension.EnergyFinal
public import CoarseDeGiorgi.Statements.IsTriadicWidth
public import CoarseDeGiorgi.Statements.SelectionInterval

/-! # The affine extension at widths bounded by `(ρ₂ - τ)/(100 d)`

All interpolation, patch, overlap and gradient estimates are supplied by the
width-independent implementation. The wider cap enters only in the strict
containment of the support cube. The Lipschitz clause uses a finite real bound.
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

/-- The wider width cap still leaves the support cube strictly inside `ρ₂ □₀`. -/
theorem radius_add_three_width_lt {d : ℕ} {τ ρ₂ h : ℝ} (hd : 1 ≤ d)
    (hh : 0 < h) (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ))) :
    τ + 3 * h < ρ₂ := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 100 * (d : ℝ) := by positivity
  have hcap := (le_div_iff₀ hden).mp hwidth
  nlinarith only [hcap, hh, hdr]

/-- `p.affine.extension`: the piecewise affine extension `L_h f`.  It is linear in `f`,
nonnegative when `f ≥ 0`, a Lipschitz extension of `f` to `ℝ^d ∖ τ□₀`, has values between `min {0, min f}` and
`max {0, max f}`, vanishes off `𝒲_h`, has the simplices of `𝒲_h` and its support in `(τ+3h)□̄₀ ⋐ ρ₂□₀`, and obeys
`e.extension.scale`.  The width is `0 < h ≤ (ρ₂-τ)/(100 d)` as in `e.extension.width`.  One constant `C = C(d, α, ξ) < ∞`
serves the scale estimate. -/
theorem affine_extension_wide (d : ℕ) (_hd : 3 ≤ d) (α ξ : ℝ)
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
  by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Cr, _, hCr⟩ := CoarseDeGiorgi.WhitneyExt.energy_final hd1 _hα0 _hξ1 _hξ2
  refine ⟨ENNReal.ofReal Cr,
    ENNReal.ofReal_lt_top, ?_⟩
  intro ρ₁ ρ₂ hρ₁ hρ₁₂ hρ₂ τ hJ hτ0 hτ1 h hw hh2
  obtain ⟨n, hn⟩ := hw
  have hh0 : 0 < h := by rw [hn]; positivity
  have hh1 : h ≤ 1 := by
    rw [hn]; exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hlt : τ + 3 * h < ρ₂ := radius_add_three_width_lt hd1 hh0 hh2
  have hnear_sub : ∀ D : TriadicCube d, D ∈ whitneyCubes (d := d) τ →
      infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ) < h →
      closedTriadicCube D ⊆ closedReferenceCube (d := d) (τ + 3 * h) := fun D hD hnear =>
    CoarseDeGiorgi.WhitneyExt.cube_subset_closedRef_of_near hτ0 hτ1 hD hnear
  refine ⟨?_, ?_⟩
  · intro f₁ f₂ hf₁ hf₂ c₁ c₂ x hx
    obtain ⟨K₁, hK₁⟩ := hf₁
    obtain ⟨K₂, hK₂⟩ := hf₂
    exact CoarseDeGiorgi.WhitneyExt.ext_linear hτ0 hτ1 hK₁.continuousOn hK₂.continuousOn c₁ c₂ hx
  · intro f hf
    obtain ⟨K, hK⟩ := hf
    have hfc : ContinuousOn f (cubeSurface (d := d) τ) := hK.continuousOn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hf0 x hx
      exact CoarseDeGiorgi.WhitneyExt.ext_nonneg hτ0 hτ1 hf0 hx
    · exact exists_extension_lipConst_lt_top hd1 hτ0 hτ1 hh0 hh1 hK
    · intro m M hm hM hf2 x hx
      exact CoarseDeGiorgi.WhitneyExt.ext_mem_Icc hτ0 hτ1 hm hM hf2 hx
    · intro cell hcell x hx
      exact CoarseDeGiorgi.WhitneyExt.ext_eq_zero_of_far hτ0 hτ1 hh0 f cell.1.2
        (not_lt.mp hcell) (CoarseDeGiorgi.WhitneyInterp.closure_cell_subset_cube cell
          (subset_closure hx))
    · refine ⟨?_, ?_, ?_⟩
      · intro cell hcell
        have hD : cell.1.val ∈ whitneyCubes (d := d) τ := cell.1.2
        exact (CoarseDeGiorgi.WhitneyInterp.closure_cell_subset_cube cell).trans
          (hnear_sub _ hD hcell)
      · apply closure_minimal _ (CoarseDeGiorgi.WhitneyExt.closedRef_isClosed _)
        intro x hx
        obtain ⟨D, hD, hxD⟩ := (CoarseDeGiorgi.whitney_cubes hτ0 hτ1).2.1 x hx.1
        by_cases hnear : infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ) < h
        · exact hnear_sub D hD hnear hxD
        · exact absurd (CoarseDeGiorgi.WhitneyExt.ext_eq_zero_of_far hτ0 hτ1 hh0 f hD
            (not_lt.mp hnear) hxD) hx.2
      · exact CoarseDeGiorgi.WhitneyExt.closedRef_subset_originCube hlt
    · intro j b hb
      exact hCr hτ0 hτ1 hh0 hh1 hfc j b hb

end CoarseDeGiorgi.WhitneyExt
