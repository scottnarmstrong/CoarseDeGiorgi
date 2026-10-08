import CoarseDeGiorgi.Foundations.Reconstruction.AssemblyLimit
import CoarseDeGiorgi.Foundations.Reconstruction.ZeroDimension

/-! # Exact all-dimensional fractional reconstruction, conditional on the two explicit inputs

The conclusion is the type of `fractional_reconstruction`, with its hypotheses and
quantifier order. Only the inputs `AssemblyTailBounds` and `AssemblySmoothingConvergence`
precede it.
-/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The full reconstruction conclusion, conditional on exactly `AssemblyTailBounds` and
`AssemblySmoothingConvergence`.
The zero-dimensional branch is unconditional and uses constant `1`. -/
theorem fractional_reconstruction_of_tail_bounds_smoothing {d : ℕ} {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r)
    (htail : AssemblyTailBounds d α r) (hsmoothing : AssemblySmoothingConvergence d r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (Dw : Vec d → Vec d),
        HasWeakGradientOn (CoarseDeGiorgi.auxCube m z) w Dw →
        IntegrableOn w (CoarseDeGiorgi.auxCube m z) volume →
        IntegrableOn Dw (CoarseDeGiorgi.auxCube m z) volume →
        MemLp w (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z)) →
        CoarseDeGiorgi.fracSeminorm (CoarseDeGiorgi.auxCube m z) α r w ≤
          ENNReal.ofReal C *
            ∑' k : {k : ℤ // m ≤ k},
              ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * (1 - α))) *
                eLpNorm (fun x => CoarseDeGiorgi.euclidNorm (CoarseDeGiorgi.auxAverage m k.1 z Dw x))
                  (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z)) := by
  cases d with
  | zero => exact fractional_reconstruction_zero_dim hα0 hα1 hr
  | succ d =>
    obtain ⟨C₁, _, htail⟩ := htail
    let K := assemblyConstantENN (d + 1) α r C₁
    have hK : K ≠ ∞ := assemblyConstantENN_ne_top hα0 (zero_lt_one.trans hr)
    let C : ℝ := K.toReal + 1
    have hC : 0 < C := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one
    have hKC : K ≤ ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_toReal hK]
      exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)
    refine ⟨C, hC, ?_⟩
    intro m z w Dw hweak hw hDw hmem
    change CoarseDeGiorgi.fracSeminorm (CoarseDeGiorgi.auxCube m z) α r w ≤
      ENNReal.ofReal C * assemblySourceSeries m z Dw α r
    by_cases hinf : assemblySourceSeries m z Dw α r = ∞
    · exact le_of_sourceSeries_eq_top hC hinf
    have hfinite : assemblySourceSeries m z Dw α r < ∞ := lt_top_iff_ne_top.mpr hinf
    let w' := hw.aestronglyMeasurable.mk w
    have hmeas : Measurable w' := hw.aestronglyMeasurable.measurable_mk
    have heq : w =ᵐ[volume.restrict (CoarseDeGiorgi.auxCube m z)] w' :=
      hw.aestronglyMeasurable.ae_eq_mk
    have hw' : IntegrableOn w' (CoarseDeGiorgi.auxCube m z) volume := hw.congr heq
    have hmem' : MemLp w' (ENNReal.ofReal r)
        (volume.restrict (CoarseDeGiorgi.auxCube m z)) := by
      rw [MemLp, ← eLpNorm_congr_ae heq]
      exact hmem
    have hweak' := hasWeakGradientOn_congr_ae heq (Filter.Eventually.of_forall fun _ => rfl) hweak
    have hblocks := htail m z w' Dw hweak' hw' hDw hmem' hfinite
    have h := assembly_reconstruction_le_of_block_bounds hα0 hα1 hr m z hmeas Dw C₁
      (fun j => (hblocks j).2) (hsmoothing m z w' hw' hmem')
    have hsem : CoarseDeGiorgi.fracSeminorm (CoarseDeGiorgi.auxCube m z) α r w =
        CoarseDeGiorgi.fracSeminorm (CoarseDeGiorgi.auxCube m z) α r w' := by
      rw [← fracSeminorm_eq_statement, ← fracSeminorm_eq_statement]
      exact fracSeminorm_congr_ae heq
    rw [hsem]
    exact h.trans (mul_le_mul_left hKC _)

end
end CoarseDeGiorgi.Foundations.Reconstruction
