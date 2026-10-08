import CoarseDeGiorgi.Foundations.Reconstruction.FoldedTests

/-! # The weak-gradient identity for compactly cut off folded tests -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The folded test translated back to the original auxiliary cube. -/
def translatedFoldedTest (m : ℤ) (z : Fin d → ℤ) (i : Fin d)
    (φ : Vec d → ℝ) (x : Vec d) : ℝ := foldedTest i φ (x - auxLower m z)

theorem contDiff_translatedFoldedTest (m : ℤ) (z : Fin d → ℤ) (i : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (translatedFoldedTest m z i φ) :=
  (contDiff_foldedTest i hφ).comp (contDiff_id.sub contDiff_const)

theorem fderiv_translatedFoldedTest_basisVec (m : ℤ) (z : Fin d → ℤ) (i : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    (fderiv ℝ (translatedFoldedTest m z i φ) x) (basisVec i) =
      ∑ s : Fin d → Bool,
        (fderiv ℝ φ (signLinear s (x - auxLower m z))) (basisVec i) := by
  have hf := ((contDiff_foldedTest i hφ).differentiable (by norm_num)
    (x - auxLower m z)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const (auxLower m z))
  dsimp only [Function.comp_def, id_eq] at hf
  change (fderiv ℝ (fun y => foldedTest i φ (y - auxLower m z)) x) (basisVec i) = _
  rw [hf.fderiv, ContinuousLinearMap.comp_id]
  exact fderiv_foldedTest_basisVec i hφ (x - auxLower m z)

end

end CoarseDeGiorgi.Foundations.Reconstruction
