module

public import CoarseDeGiorgi.Weighted.Defs
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization


/-- A positive symmetric bilinear form determines a unique positive definite matrix.
This supplies the matrix representation step in both response constructions. -/
theorem existsUnique_posDef_matrix_of_bilin {d : ℕ}
    (B : LinearMap.BilinForm ℝ (Vec d)) (hs : B.IsSymm)
    (hp : ∀ e : Vec d, e ≠ 0 → 0 < B e e) :
    ∃! A : Mat d, A.PosDef ∧ ∀ e : Vec d, vecDot e (matVecMul A e) = B e e := by
  let A : Mat d := B.toMatrix'
  have hA : A.IsSymm := B.isSymm_toMatrix'_iff_isSymm.mpr hs
  have he (e : Vec d) : vecDot e (matVecMul A e) = B e e := by
    change dotProduct e (Matrix.mulVec A e) = B e e
    rw [← Matrix.toBilin'_apply', Matrix.toBilin'_toMatrix']
  refine ⟨A, ⟨?_, he⟩, ?_⟩
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · simpa only [Matrix.isHermitian_iff_isSymm] using hA
    · intro e hne
      have hpos : 0 < vecDot e (matVecMul A e) := (he e).symm ▸ hp e hne
      simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using hpos
  · intro M hM
    have hsM : M.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr
      (by simpa only [Matrix.isHermitian_iff_isSymm] using hM.1.isHermitian)
    have hMB : M.toBilin' = B := by
      apply LinearMap.BilinForm.ext_of_isSymm hsM hs
      intro e
      simpa [Matrix.toBilin'_apply', vecDot, matVecMul, dotProduct, Matrix.mulVec] using hM.2 e
    exact Matrix.toBilin'.injective (hMB.trans (Matrix.toBilin'_toMatrix' B).symm)

end CoarseDeGiorgi.Weighted
