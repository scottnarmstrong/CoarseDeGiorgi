module

public import CoarseDeGiorgi.Endpoint.Rescaling.WeightedEquation
public import CoarseDeGiorgi.Weighted.LowerSpecMean

/-! Inverse changes of variables and gradient-preserving solution transport. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace CoarseDeGiorgi.Endpoint.Rescaling

theorem affineMap_inverse_left {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    affineMap (-(r⁻¹ • y)) r⁻¹ (affineMap y r x) = x := by
  simp only [affineMap, smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  abel

theorem affineMap_inverse_right {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    affineMap y r (affineMap (-(r⁻¹ • y)) r⁻¹ x) = x := by
  simp only [affineMap, smul_add, smul_neg, smul_smul,
    mul_inv_cancel₀ hr.ne', one_smul]
  abel

theorem affineImage_inverse {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) :
    affineImage (-(r⁻¹ • y)) r⁻¹ (affineImage y r U) = U := by
  rw [← affineMap_image, ← affineMap_image, Set.image_image]
  have he : affineMap (-(r⁻¹ • y)) r⁻¹ ∘ affineMap y r = id := by
    funext x
    exact affineMap_inverse_left y hr x
  change (affineMap (-(r⁻¹ • y)) r⁻¹ ∘ affineMap y r) '' U = U
  rw [he, Set.image_id]

theorem solution_const_smul {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) {a : CoeffField d}
    (ha : IsWeightedCoeffOn U a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSolution a U u G) (c : ℝ) :
    IsWeightedSolution a U (c • u) (c • G) := by
  refine ⟨Weighted.LowerResponseImpl.lower_memH1a_smul hU hne ha hu.1 c, ?_⟩
  intro φ hφ hc hs
  obtain ⟨hi, he⟩ := hu.2 φ hφ hc hs
  have heq : (fun x => vecDot (smoothGrad φ x) (matVecMul (a x) ((c • G) x))) =
      fun x => c * vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) := by
    funext x
    simp only [Pi.smul_apply, matVecMul_smul, vecDot_smul_right]
  rw [heq]
  exact ⟨hi.const_mul c, by rw [integral_const_mul, he, mul_zero]⟩

/-- Normalizing the value by `r⁻¹` transports the gradient without a scalar factor. -/
theorem solution_affine_normalized {d : ℕ} [NeZero d] (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain (affineImage y r U))
    (hne : (affineImage y r U).Nonempty) {a : CoeffField d}
    (ha : IsWeightedCoeffOn (affineImage y r U) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSolution a (affineImage y r U) u G) :
    IsWeightedSolution (a ∘ affineMap y r) U (r⁻¹ • (u ∘ affineMap y r))
      (G ∘ affineMap y r) := by
  have h := solution_affine y hr hU hV hne ha (solution_const_smul hV hne ha hu r⁻¹)
  have hv : (r⁻¹ • u) ∘ affineMap y r = r⁻¹ • (u ∘ affineMap y r) := rfl
  have hg : r • ((r⁻¹ • G) ∘ affineMap y r) = G ∘ affineMap y r := by
    funext x
    exact smul_smul r r⁻¹ (G (affineMap y r x)) |>.trans
      (by rw [mul_inv_cancel₀ hr.ne', one_smul]; rfl)
  rwa [hv, hg] at h

/-- A solution for the pulled-back coefficient can be pushed to the original domain. -/
theorem solution_affine_reverse {d : ℕ} [NeZero d] (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hneU : U.Nonempty)
    (hV : IsOpenBoundedConvexDomain (affineImage y r U)) {a : CoeffField d}
    (ha : IsWeightedCoeffOn (affineImage y r U) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSolution (a ∘ affineMap y r) U u G) :
    IsWeightedSolution a (affineImage y r U)
      ((r⁻¹)⁻¹ • (u ∘ affineMap (-(r⁻¹ • y)) r⁻¹))
      (G ∘ affineMap (-(r⁻¹ • y)) r⁻¹) := by
  have hdom : IsOpenBoundedConvexDomain
      (affineImage (-(r⁻¹ • y)) r⁻¹ (affineImage y r U)) :=
    (affineImage_inverse y hr U).symm ▸ hU
  have hne : (affineImage (-(r⁻¹ • y)) r⁻¹ (affineImage y r U)).Nonempty :=
    (affineImage_inverse y hr U).symm ▸ hneU
  have hcoeff : IsWeightedCoeffOn
      (affineImage (-(r⁻¹ • y)) r⁻¹ (affineImage y r U)) (a ∘ affineMap y r) :=
    (affineImage_inverse y hr U).symm ▸ weightedCoeffOn_affine y hr ha
  have hsol : IsWeightedSolution (a ∘ affineMap y r)
      (affineImage (-(r⁻¹ • y)) r⁻¹ (affineImage y r U)) u G :=
    (affineImage_inverse y hr U).symm ▸ hu
  have h := solution_affine_normalized (-(r⁻¹ • y)) (inv_pos.mpr hr)
    hV hdom hne hcoeff hsol
  have he : (a ∘ affineMap y r) ∘ affineMap (-(r⁻¹ • y)) r⁻¹ = a := by
    funext x
    exact congrArg a (affineMap_inverse_right y hr x)
  rwa [he] at h

end CoarseDeGiorgi.Endpoint.Rescaling
