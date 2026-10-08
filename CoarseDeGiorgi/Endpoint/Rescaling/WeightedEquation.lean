import CoarseDeGiorgi.Endpoint.Rescaling.WeightedCompletion
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.IsWeightedSupersolution

/-! Affine transport of the literal weighted solution and supersolution classes. -/

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace CoarseDeGiorgi.Endpoint.Rescaling

theorem affineHomeomorph_symm_contDiff {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (affineHomeomorph y hr).symm := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => r⁻¹ • (x - y))
  exact (contDiff_id.sub contDiff_const).const_smul r⁻¹

theorem test_affine_inverse {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (affineHomeomorph y hr).symm) ∧
      HasCompactSupport (φ ∘ (affineHomeomorph y hr).symm) ∧
      tsupport (φ ∘ (affineHomeomorph y hr).symm) ⊆ affineImage y r U := by
  refine ⟨hφ.comp (affineHomeomorph_symm_contDiff y hr),
    hc.comp_homeomorph (affineHomeomorph y hr).symm, ?_⟩
  rw [tsupport_comp_eq_preimage]
  intro x hx
  rw [← affineMap_image]
  exact ⟨(affineHomeomorph y hr).symm x, hs hx,
    (affineHomeomorph y hr).apply_symm_apply x⟩

theorem smoothGrad_test_inverse {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d) :
    smoothGrad φ x = r • smoothGrad (φ ∘ (affineHomeomorph y hr).symm)
      (affineMap y r x) := by
  have hψ := hφ.comp (affineHomeomorph_symm_contDiff y hr)
  have hcomp : (φ ∘ (affineHomeomorph y hr).symm) ∘ affineMap y r = φ := by
    funext z
    exact congrArg φ ((affineHomeomorph y hr).symm_apply_apply z)
  have h := smoothGrad_affine y r
    ((hψ.differentiable (by simp)).differentiableAt (x := affineMap y r x))
  rwa [hcomp] at h

private theorem affine_test_pairing {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (a : CoeffField d) (G : Vec d → Vec d) :
    (fun x => vecDot (smoothGrad φ x)
      (matVecMul ((a ∘ affineMap y r) x) ((r • (G ∘ affineMap y r)) x))) =
      fun x => r ^ 2 * vecDot
        (smoothGrad (φ ∘ (affineHomeomorph y hr).symm) (affineMap y r x))
        (matVecMul (a (affineMap y r x)) (G (affineMap y r x))) := by
  funext x
  rw [smoothGrad_test_inverse y hr hφ x]
  simp only [Pi.smul_apply, Function.comp_apply, matVecMul_smul,
    vecDot_smul_left, vecDot_smul_right]
  ring

/-- The equation and its explicit gradient transport under the affine map. -/
theorem solution_affine {d : ℕ} [NeZero d] (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain (affineImage y r U))
    (hne : (affineImage y r U).Nonempty) {a : CoeffField d}
    (ha : IsWeightedCoeffOn (affineImage y r U) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSolution a (affineImage y r U) u G) :
    IsWeightedSolution (a ∘ affineMap y r) U (u ∘ affineMap y r)
      (r • (G ∘ affineMap y r)) := by
  refine ⟨memH1a_affine y hr hU hV hne ha hu.1, ?_⟩
  intro φ hφ hc hs
  obtain ⟨hψ, hcψ, hsψ⟩ := test_affine_inverse y hr hφ hc hs
  obtain ⟨hi, he⟩ := hu.2 _ hψ hcψ hsψ
  rw [affine_test_pairing y hr hφ]
  refine ⟨(integrable_affine y hr hi).const_mul (r ^ 2), ?_⟩
  rw [integral_const_mul, integral_affine y hr U
    (fun x => vecDot (smoothGrad (φ ∘ (affineHomeomorph y hr).symm) x)
      (matVecMul (a x) (G x))), he, mul_zero, mul_zero]

/-- The sign of the weak equation is preserved by positive affine scaling. -/
theorem subsolution_affine {d : ℕ} [NeZero d] (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain (affineImage y r U))
    (hne : (affineImage y r U).Nonempty) {a : CoeffField d}
    (ha : IsWeightedCoeffOn (affineImage y r U) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSubsolution a (affineImage y r U) u G) :
    IsWeightedSubsolution (a ∘ affineMap y r) U (u ∘ affineMap y r)
      (r • (G ∘ affineMap y r)) := by
  refine ⟨memH1a_affine y hr hU hV hne ha hu.1, ?_⟩
  intro φ hφ hc hs hn
  obtain ⟨hψ, hcψ, hsψ⟩ := test_affine_inverse y hr hφ hc hs
  obtain ⟨hi, he⟩ := hu.2 _ hψ hcψ hsψ (fun x => hn _)
  rw [affine_test_pairing y hr hφ]
  refine ⟨(integrable_affine y hr hi).const_mul (r ^ 2), ?_⟩
  rw [integral_const_mul, integral_affine y hr U
    (fun x => vecDot (smoothGrad (φ ∘ (affineHomeomorph y hr).symm) x)
      (matVecMul (a x) (G x)))]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg r)
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) he)

/-- Supersolutions transport with the same rule as solutions. -/
theorem supersolution_affine {d : ℕ} [NeZero d] (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain (affineImage y r U))
    (hne : (affineImage y r U).Nonempty) {a : CoeffField d}
    (ha : IsWeightedCoeffOn (affineImage y r U) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSupersolution a (affineImage y r U) u G) :
    IsWeightedSupersolution (a ∘ affineMap y r) U (u ∘ affineMap y r)
      (r • (G ∘ affineMap y r)) := by
  have h := subsolution_affine y hr hU hV hne ha hu
  have he : r • ((fun x => -G x) ∘ affineMap y r) =
      (fun x => -(r • (G ∘ affineMap y r)) x) := by
    funext x
    exact smul_neg r _
  rw [he] at h
  exact h

end CoarseDeGiorgi.Endpoint.Rescaling
