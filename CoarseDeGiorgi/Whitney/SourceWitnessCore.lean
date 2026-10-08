module

public import CoarseDeGiorgi.Weighted.UpperResponseAffine
public import CoarseDeGiorgi.Whitney.LiftZeroExtension
public import CoarseDeGiorgi.Selection.CommonRadius
public import CoarseDeGiorgi.Selection.SourceResponses
public import CoarseDeGiorgi.Whitney.LiftCell
public import CoarseDeGiorgi.Whitney.SeedCellAffine
public import CoarseDeGiorgi.Whitney.LiftSurfaceLayer
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! # Source witness pieces for fixed-surface smooth data -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ} {V W : Set (Vec d)} {a : CoeffField d}

/-- The source width permitted by the caller remains admissible for the splice
at every radius in the selection interval. -/
theorem source_width_at_selected_radius {ρ R τ h : ℝ} (hd : 3 ≤ d)
    (hρ : 1 / 2 ≤ ρ) (hρR : ρ < R) (hR : R ≤ 1)
    (hτ : τ ∈ Selection.selectionInterval ρ R) (hh : 0 < h)
    (hwidth : h ≤ (R - ρ) / (20000 * (d : ℝ))) :
    1 / 2 ≤ τ ∧ τ < R ∧ h ≤ (R - τ) / (10000 * (d : ℝ)) ∧ h ≤ 1 / 10 := by
  change ρ + (R - ρ) / 4 < τ ∧ τ < ρ + (R - ρ) / 2 at hτ
  have hgap : 0 < R - ρ := by linarith only [hρR]
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
  have hbig : 20000 * (d : ℝ) * h ≤ R - ρ := by
    have hb := (le_div_iff₀ (by positivity : 0 < 20000 * (d : ℝ))).mp hwidth
    nlinarith only [hb]
  have hsmallgap : 10000 * (d : ℝ) * h ≤ (R - ρ) / 2 := by linarith only [hbig]
  have htarget : 10000 * (d : ℝ) * h ≤ R - τ := by linarith only [hsmallgap, hτ.2]
  have hsmall : 40000 * (d : ℝ) * h ≤ 1 := by
    have hgaple : R - ρ ≤ 1 / 2 := by linarith only [hR, hρ]
    nlinarith only [hbig, hgaple]
  refine ⟨by linarith only [hρ, hτ.1, hgap], by linarith only [hτ.2, hρR], ?_, ?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < 10000 * (d : ℝ))).mpr
    nlinarith only [htarget]
  · have hdh : h ≤ (d : ℝ) * h := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hdreal) hh.le]
    nlinarith only [hsmall, hdh]

end

end CoarseDeGiorgi.Whitney
