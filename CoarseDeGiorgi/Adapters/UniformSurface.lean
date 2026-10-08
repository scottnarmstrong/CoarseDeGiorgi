module

public import CoarseDeGiorgi.Localization.SourceCover
public import CoarseDeGiorgi.Selection.TraceTransport
public import CoarseDeGiorgi.Selection.SourceRadius
public import CoarseDeGiorgi.Selection.TraceBounds
public import CoarseDeGiorgi.Selection.SamplingMoment
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import CoarseDeGiorgi.Statements.CriticalSurfaceEmbedding
public import CoarseDeGiorgi.Statements.IntegratedSlicing

/-! # Uniform trace and simultaneous selection from surface agreement

The slicing constant of `integrated_slicing` is chosen before radii and all concrete data.
Agreement is needed only on almost every surface in the original interval.
-/

@[expose] public section

namespace CoarseDeGiorgi.Adapters
open Homogenization MeasureTheory Set CoarseDeGiorgi.Localization CoarseDeGiorgi.Selection
open scoped ENNReal BigOperators
noncomputable section

/-- The slicing theorem `integrated_slicing` gives one constant for every admissible pair
of radii. -/
theorem exists_uniform_trace_constant {n : ℕ} {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ R : ℝ,
      (1 / 2 : ℝ) ≤ ρ → R ≤ 1 → ρ < R →
      ∀ (F w : Vec (n + 1) → ℝ) (L : ℝ≥0∞), Measurable F →
        (∀ᵐ τ ∂volume.restrict (selectionInterval ρ R),
          F =ᵐ[CoarseDeGiorgi.surfaceMeasure τ] w) →
        fracNorm univ α r F ≤ L →
        (∫⁻ τ in selectionInterval ρ R, surfaceFracNorm τ α r w ^ r) ≤
          ENNReal.ofReal C * L ^ r := by
  obtain ⟨C₀, hC₀, hslicing₀⟩ := CoarseDeGiorgi.integrated_slicing (d := n + 1)
  let C := C₀ * (2 : ℝ) ^ r
  have hC : 0 < C := mul_pos hC₀ (Real.rpow_pos_of_pos (by norm_num) _)
  have hslicing := hslicing₀ hα0 hα1 hr
  refine ⟨C, hC, ?_⟩
  intro ρ R hρ hR hgap F w L hF hagree hbound
  have hJ : selectionInterval ρ R ⊆ Ioo (1 / 2 : ℝ) 1 := by
    intro τ hτ
    have h := selectionInterval_subset hgap hτ
    exact ⟨lt_of_le_of_lt hρ h.1, lt_of_lt_of_le h.2 hR⟩
  have heq : (fun τ => surfaceFracNorm τ α r F ^ r) =ᵐ[
      volume.restrict (selectionInterval ρ R)] (fun τ => surfaceFracNorm τ α r w ^ r) :=
    hagree.mono fun τ hτ =>
    congrArg (fun z : ℝ≥0∞ => z ^ r) (surfaceFracNorm_congr_ae hτ)
  rw [← lintegral_congr_ae heq]
  exact (hslicing F hF _ measurableSet_Ioo hJ).trans
    (mul_le_mul_right (ENNReal.rpow_le_rpow hbound (zero_lt_one.trans hr).le) _)

end
end CoarseDeGiorgi.Adapters
