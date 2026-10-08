module

public import CoarseDeGiorgi.Endpoint.Rescaling.AffineInverse
public import CoarseDeGiorgi.Statements.UpperResponseSpec
public import CoarseDeGiorgi.Statements.LowerResponseInvSpec

/-! Affine covariance of the weighted response matrices. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Endpoint.Rescaling

private theorem solution_supremum_affine {d : ℕ} [NeZero d]
    (y : Vec d) {r : ℝ} (hr : 0 < r) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hneU : U.Nonempty)
    (hV : IsOpenBoundedConvexDomain (affineImage y r U))
    (hneV : (affineImage y r U).Nonempty) {a : CoeffField d}
    (ha : IsWeightedCoeffOn (affineImage y r U) a) (F : Mat d → Vec d → ℝ) :
    (⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
      (_ : IsWeightedSolution (a ∘ affineMap y r) U w G),
      ((volumeAverage U (fun x => F ((a ∘ affineMap y r) x) (G x)) : ℝ) : EReal)) =
    (⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
      (_ : IsWeightedSolution a (affineImage y r U) w G),
      ((volumeAverage (affineImage y r U) (fun x => F (a x) (G x)) : ℝ) : EReal)) := by
  apply le_antisymm
  · apply iSup_le
    intro w
    apply iSup_le
    intro G
    apply iSup_le
    intro hw
    have hback := solution_affine_reverse y hr hU hneU hV ha hw
    have havg : volumeAverage U (fun x => F ((a ∘ affineMap y r) x) (G x)) =
        volumeAverage (affineImage y r U)
          (fun x => F (a x) (G (affineMap (-(r⁻¹ • y)) r⁻¹ x))) := by
      rw [← volumeAverage_affine y hr U
        (fun x => F (a x) (G (affineMap (-(r⁻¹ • y)) r⁻¹ x)))]
      congr 1
      funext x
      simp only [Function.comp_apply, affineMap_inverse_left y hr]
    rw [havg]
    exact le_iSup_of_le _ (le_iSup_of_le _ (le_iSup_of_le hback le_rfl))
  · apply iSup_le
    intro w
    apply iSup_le
    intro G
    apply iSup_le
    intro hw
    have hforward := solution_affine_normalized y hr hU hV hneV ha hw
    have havg : volumeAverage U
        (fun x => F ((a ∘ affineMap y r) x) ((G ∘ affineMap y r) x)) =
        volumeAverage (affineImage y r U) (fun x => F (a x) (G x)) :=
      volumeAverage_affine y hr U (fun x => F (a x) (G x))
    rw [← havg]
    exact le_iSup_of_le _ (le_iSup_of_le _ (le_iSup_of_le hforward le_rfl))

/-- The upper response is unchanged when both domain and coefficients are transported. -/
theorem upperResponse_affine {d : ℕ} [NeZero d] (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hneU : U.Nonempty)
    (hV : IsOpenBoundedConvexDomain (affineImage y r U))
    (hneV : (affineImage y r U).Nonempty) {a : CoeffField d}
    (ha : IsWeightedCoeffOn (affineImage y r U) a) :
    upperResponse (a ∘ affineMap y r) U hU hneU (weightedCoeffOn_affine y hr ha) =
      upperResponse a (affineImage y r U) hV hneV ha := by
  have hs := upperResponse_spec hV hneV ha
  have ht := upperResponse_spec hU hneU (weightedCoeffOn_affine y hr ha)
  apply Eq.symm
  apply ht.2.1 _ hs.1
  intro e
  have he : upperDirectionalResponseSol (a ∘ affineMap y r) U e =
      upperDirectionalResponseSol a (affineImage y r U) e :=
    solution_supremum_affine y hr hU hneU hV hneV ha
      (fun A G => -vecDot G (matVecMul A G) + 2 * vecDot e (matVecMul A G))
  exact (hs.2.2.1 e).trans he.symm

/-- The inverse lower response has the same affine covariance. -/
theorem lowerResponseInv_affine {d : ℕ} [NeZero d] (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hneU : U.Nonempty)
    (hV : IsOpenBoundedConvexDomain (affineImage y r U))
    (hneV : (affineImage y r U).Nonempty) {a : CoeffField d}
    (ha : IsWeightedCoeffOn (affineImage y r U) a) :
    lowerResponseInv (a ∘ affineMap y r) U hU hneU (weightedCoeffOn_affine y hr ha) =
      lowerResponseInv a (affineImage y r U) hV hneV ha := by
  have hs := lowerResponseInv_spec hV hneV ha
  have ht := lowerResponseInv_spec hU hneU (weightedCoeffOn_affine y hr ha)
  apply Eq.symm
  apply ht.2.1 _ hs.1
  intro e
  have he : lowerDirectionalResponse (a ∘ affineMap y r) U e =
      lowerDirectionalResponse a (affineImage y r U) e :=
    solution_supremum_affine y hr hU hneU hV hneV ha
      (fun A G => -vecDot G (matVecMul A G) + 2 * vecDot e G)
  exact (hs.2.2.1 e).trans he.symm

end CoarseDeGiorgi.Endpoint.Rescaling
