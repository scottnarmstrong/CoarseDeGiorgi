module

public import CoarseDeGiorgi.Whitney.Extension.CellLipschitz

/-!
# The energy of `L_h f` on one Whitney simplex
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

theorem volume_closedTriadicCube (D : TriadicCube d) :
    volume (closedTriadicCube D) = ENNReal.ofReal (cubeScaleFactor D ^ d) := by
  have hp := cubeScaleFactor_pos D
  have he : closedTriadicCube D = Metric.closedBall (triadicCenter D) (cubeScaleFactor D / 2) := by
    ext x
    simp only [closedTriadicCube, mem_ofPred_eq, Metric.mem_closedBall, dist_pi_le_iff
      (by linarith only [hp] : 0 ≤ cubeScaleFactor D / 2), Real.dist_eq]
  rw [he, Real.volume_pi_closedBall _ (by linarith only [hp])]
  simp only [Fintype.card_fin]
  congr 1
  ring

theorem volume_exteriorCellSet_le {τ : ℝ} (cell : ExteriorCell d τ) :
    volume (exteriorCellSet cell) ≤ ENNReal.ofReal (cubeScaleFactor cell.1.val ^ d) := by
  rw [← volume_closedTriadicCube]
  exact measure_mono (subset_closure.trans (WhitneyInterp.closure_cell_subset_cube cell))

/-- The energy of one cell is at most `ℓ^d (C ℓ⁻¹ M)²` when all free-vertex differences in the
cube are at most `M`. -/
theorem cell_lintegral_le (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (f : Vec d → ℝ)
    {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ) {M : ℝ}
    (hM : ∀ z z' : {z : Vec d // IsFreeVertex τ z}, z.1 ∈ closedTriadicCube D →
      z'.1 ∈ closedTriadicCube D → |whitneyFreeValue τ h f z - whitneyFreeValue τ h f z'| ≤ M)
    {cell : ExteriorCell d τ} (hc : cell.1.val = D) :
    ∫⁻ x in exteriorCellSet cell,
        ENNReal.ofReal (vecNormSq (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)) ≤
      ENNReal.ofReal (cubeScaleFactor D ^ d * (C32 d / cubeScaleFactor D * M) ^ 2) := by
  have hp := cubeScaleFactor_pos D
  have hI := interp_spec (h := h) hτ0 hτ1 f
  have hM' : ∀ z z' : {z : Vec d // IsFreeVertex τ z}, z.1 ∈ closedTriadicCube D →
      z'.1 ∈ closedTriadicCube D → |whitneyAffineExtension τ h f hτ0 hτ1 z.1 -
        whitneyAffineExtension τ h f hτ0 hτ1 z'.1| ≤ M := by
    intro z z' hz hz'
    rw [hI.2.2.2 z, hI.2.2.2 z']
    exact hM z z' hz hz'
  have hgrad := ((C32_spec hτ0 hτ1 hI).2 D hD).2 M hM' cell hc
  have hpt : ∀ x ∈ exteriorCellSet cell,
      ENNReal.ofReal (vecNormSq (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)) ≤
        ENNReal.ofReal ((C32 d / cubeScaleFactor D * M) ^ 2) := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    have h1 := hgrad x hx
    have h2 : vecNormSq (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x) =
        euclidNorm (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x) ^ 2 := by
      unfold euclidNorm
      rw [Real.sq_sqrt (vecNormSq_nonneg _)]
    rw [h2]
    have h3 : 0 ≤ euclidNorm (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x) :=
      Real.sqrt_nonneg _
    exact pow_le_pow_left₀ h3 h1 2
  calc ∫⁻ x in exteriorCellSet cell, _ ≤ ∫⁻ _x in exteriorCellSet cell,
        ENNReal.ofReal ((C32 d / cubeScaleFactor D * M) ^ 2) :=
        setLIntegral_mono' (WhitneyInterp.isOpen_exteriorCellSet cell).measurableSet hpt
    _ = ENNReal.ofReal ((C32 d / cubeScaleFactor D * M) ^ 2) * volume (exteriorCellSet cell) := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal ((C32 d / cubeScaleFactor D * M) ^ 2) *
          ENNReal.ofReal (cubeScaleFactor D ^ d) := by
        gcongr
        have := volume_exteriorCellSet_le cell
        rw [hc] at this
        exact this
    _ = _ := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]

end

end CoarseDeGiorgi.WhitneyExt
