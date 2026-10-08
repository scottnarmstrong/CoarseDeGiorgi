module

public import CoarseDeGiorgi.Statements.LowerDirectionalResponse
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! The lower response in dimension zero, and a zero solution in every dimension. -/

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-- The zero value-gradient pair is a weighted solution. -/
theorem lower_zero_solution {d : ℕ} (a : CoeffField d) (V : Set (Vec d)) :
    IsWeightedSolution a V 0 0 := by
  have hc : IsSmoothCore a V (0 : Vec d → ℝ) := by
    refine ⟨contDiffOn_const, integrableOn_zero, ?_⟩
    simp [weightedEnergy, smoothGrad, vecDot, matVecMul]
  refine ⟨⟨aestronglyMeasurable_zero, aestronglyMeasurable_zero,
    fun _ => 0, fun _ => hc, ?_, ?_, ?_⟩, ?_⟩
  · intro ε hε
    refine ⟨0, fun _ _ _ _ => ?_⟩
    simpa [weightedEnergy, smoothGrad, vecDot, matVecMul, volumeAverage] using
      ENNReal.ofReal_pos.mpr hε
  · intro K _ _
    simpa only [Pi.zero_apply, sub_self, enorm_zero, lintegral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  · simp [weightedEnergy, smoothGrad, vecDot, matVecMul]
  · intro φ _ _ _
    simp [vecDot, matVecMul]

/-- All directional lower responses vanish in dimension zero. -/
theorem lowerDirectionalResponse_dim_zero (a : CoeffField 0) (V : Set (Vec 0))
    (e : Vec 0) : lowerDirectionalResponse a V e = 0 := by
  apply le_antisymm
  · unfold lowerDirectionalResponse
    refine iSup_le fun w => iSup_le fun G => iSup_le fun _ => ?_
    simp [vecDot, volumeAverage]
  · unfold lowerDirectionalResponse
    have hz : ((volumeAverage V (fun x =>
        -vecDot ((0 : Vec 0 → Vec 0) x)
          (matVecMul (a x) ((0 : Vec 0 → Vec 0) x)) +
        2 * vecDot e ((0 : Vec 0 → Vec 0) x)) : ℝ) : EReal) = 0 := by
      simp [vecDot, volumeAverage]
    rw [← hz]
    exact le_iSup_of_le (0 : Vec 0 → ℝ) (le_iSup_of_le (0 : Vec 0 → Vec 0)
      (le_iSup_of_le (lower_zero_solution a V) (le_refl _)))

/-- Existence and uniqueness of the lower-response matrix in dimension zero. -/
theorem lowerResponse_existsUnique_dim_zero (a : CoeffField 0) (V : Set (Vec 0)) :
    ∃! A : Mat 0, A.PosDef ∧ ∀ e : Vec 0,
      ((vecDot e (matVecMul A e) : ℝ) : EReal) = lowerDirectionalResponse a V e := by
  refine ⟨0, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨by simp [Matrix.IsHermitian], fun x hx => ?_⟩
    exact (hx (Subsingleton.elim x 0)).elim
  · intro e
    rw [lowerDirectionalResponse_dim_zero]
    simp [vecDot]
  · intro A _
    exact Subsingleton.elim A 0


end CoarseDeGiorgi.Weighted
