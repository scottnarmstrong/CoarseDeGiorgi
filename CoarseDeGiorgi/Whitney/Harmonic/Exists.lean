module

public import CoarseDeGiorgi.Whitney.Harmonic.Geometry
public import CoarseDeGiorgi.Whitney.Harmonic.Linear
public import CoarseDeGiorgi.Statements.WhitneyInterpolationSpec
public import CoarseDeGiorgi.Statements.WhitneyAffineExtensionDef
public import CoarseDeGiorgi.Statements.SelectionInterval
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Weighted.HarmonicProperties
public import CoarseDeGiorgi.Weighted.Lipschitz

@[expose] public section

open Homogenization MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace CoarseDeGiorgi.Whitney.Harmonic

noncomputable section

variable {d : ℕ}

open CoarseDeGiorgi.Harnack.Replacement

/-- `L_h f` is affine on every cell, hence Lipschitz there. -/
theorem affineExtension_lipschitzOn_cell {τ : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (h : ℝ) (f : Vec d → ℝ) (cell : CoarseDeGiorgi.ExteriorCell d τ) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1)
      (CoarseDeGiorgi.exteriorCellSet cell) := by
  obtain ⟨e, c, hec⟩ :=
    ((CoarseDeGiorgi.whitneyInterpolation_spec hτ0 hτ1
      (CoarseDeGiorgi.whitneyFreeValue τ h f)).1).2.2.1 cell
  refine ⟨⟨∑ i, |e i|, Finset.sum_nonneg (fun i _ => abs_nonneg _)⟩, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx' := hec x hx
  have hy' := hec y hy
  change CoarseDeGiorgi.whitneyInterpolation hτ0 hτ1 (CoarseDeGiorgi.whitneyFreeValue τ h f) x = _
    at hx'
  change CoarseDeGiorgi.whitneyInterpolation hτ0 hτ1 (CoarseDeGiorgi.whitneyFreeValue τ h f) y = _
    at hy'
  show dist (CoarseDeGiorgi.whitneyInterpolation hτ0 hτ1 (CoarseDeGiorgi.whitneyFreeValue τ h f) x)
    (CoarseDeGiorgi.whitneyInterpolation hτ0 hτ1 (CoarseDeGiorgi.whitneyFreeValue τ h f) y) ≤ _
  rw [hx', hy', Real.dist_eq]
  have : vecDot e x + c - (vecDot e y + c) = ∑ i, e i * (x i - y i) := by
    simp only [vecDot, mul_sub, Finset.sum_sub_distrib]; ring
  rw [this]
  calc |∑ i, e i * (x i - y i)| ≤ ∑ i, |e i * (x i - y i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |e i| * dist x y := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have := dist_le_pi_dist x y i
        rwa [Real.dist_eq] at this
    _ = _ := by rw [← Finset.sum_mul]; rfl

end
end CoarseDeGiorgi.Whitney.Harmonic

namespace CoarseDeGiorgi.Whitney.Harmonic

end CoarseDeGiorgi.Whitney.Harmonic
