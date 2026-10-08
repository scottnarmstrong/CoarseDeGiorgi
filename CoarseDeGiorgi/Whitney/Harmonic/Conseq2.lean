module

public import CoarseDeGiorgi.Whitney.Harmonic.GlueData
public import CoarseDeGiorgi.Whitney.Harmonic.Cellwise
public import CoarseDeGiorgi.Statements.WhitneyInterpolationSpec
public import CoarseDeGiorgi.Whitney.Harmonic.GaussGreen
public import CoarseDeGiorgi.Weighted.Identification
public import CoarseDeGiorgi.Foundations.Reconstruction.Representatives
public import CoarseDeGiorgi.Statements.CubeFaceMeasure

/-! The `W^{1,1}` and trace assertions of Proposition `p.whitney.extension`. -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

/-- An extension `w₀` of the boundary datum, Lipschitz on the whole space. -/
theorem exists_lipschitz_extension {τ : ℝ} {f : Vec d → ℝ}
    (hf : ∃ K : ℝ≥0, LipschitzOnWith K f (CoarseDeGiorgi.cubeSurface (d := d) τ)) :
    ∃ (w : Vec d → ℝ) (K : ℝ≥0), LipschitzWith K w ∧
      ∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, w y = f y := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨g, hg, hfg⟩ := hK.extend_real
  exact ⟨g, K, hg, fun y hy => (hfg hy).symm⟩

end CoarseDeGiorgi.Whitney.Harmonic
