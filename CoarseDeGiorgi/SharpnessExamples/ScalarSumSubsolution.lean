import CoarseDeGiorgi.SharpnessExamples.ScalarCylinderSubsolution

/-! # The cylinder series is a weighted subsolution -/

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem pairing_finset_sum {d : ℕ} (s : Finset ℕ) (a : Mat d) (g : Vec d)
    (F : ℕ → Vec d) :
    vecDot g (matVecMul a (∑ j ∈ s, F j)) = ∑ j ∈ s, vecDot g (matVecMul a (F j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, matVecMul_zero, vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  | @insert n s hn ih =>
    rw [Finset.sum_insert hn, Finset.sum_insert hn, matVecMul_add, vecDot_add_right, ih]

/-- Finite cylinder sums satisfy the subsolution test inequality. -/
theorem scalarCylinder_partial_test_nonpos {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (k : ℕ)
    {φ : Vec (m + 1) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ originCube 1) (hn : ∀ x, 0 ≤ φ x) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x)
      (matVecMul (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1)) x)
        (∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x))) (originCube 1) ∧
    (∫ x in originCube 1, vecDot (smoothGrad φ x)
      (matVecMul (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1)) x)
        (∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x)) ∂volume) ≤ 0 := by
  classical
  let μ := volume.restrict (originCube (d := m + 1) 1)
  let J := fun j (x : Vec (m + 1)) => vecDot (smoothGrad φ x)
    (matVecMul (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1)) x)
      (scalarCylinderGradient j ζ x))
  have hj : ∀ j, Integrable (J j) μ ∧ (∫ x, J j x ∂μ) ≤ 0 := fun j =>
    (scalarCylinderSubsolution_isWeightedSubsolution hm hζ0 hζ2 j).2 φ hφ hc hs hn
  have heq : (fun x => vecDot (smoothGrad φ x)
      (matVecMul (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1)) x)
        (∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x))) = fun x => ∑ j ∈ Finset.range k, J j x := by
    funext x
    exact pairing_finset_sum _ _ _ _
  rw [heq]
  refine ⟨integrable_finsetSum _ (fun j _ => (hj j).1), ?_⟩
  rw [integral_finsetSum _ (fun j _ => (hj j).1)]
  exact Finset.sum_nonpos (fun j _ => (hj j).2)

/-- The literal pointwise cylinder sum is a subsolution. Dominated convergence
passes every smooth test inequality to the limit, so no distribution is added
on the line where the cylinders accumulate. -/
theorem scalarSubsolutionSum_isWeightedSubsolution {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    IsWeightedSubsolution (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1)))
      (originCube 1) (scalarSubsolutionSum (d := m + 1) ζ) (scalarSubsolutionGradientSum ζ) := by
  classical
  have hu := scalarSubsolutionSum_memH1a hm hζ0 hζ2
  have hV := Whitney.source_cube_domain (d := m + 1) (by norm_num : (0 : ℝ) < 1)
  have ha := scalarSharpnessCoefficient_isWeightedCoeffOn (d := m + 1) (by omega) hζ0 hζ2
    (cylinderRadialConstant_pos (d := m + 1) (by omega))
  refine ⟨hu, ?_⟩
  intro φ hφ hc hs hn
  let μ := volume.restrict (originCube (d := m + 1) 1)
  let a := scalarSharpnessCoefficient (d := m + 1) ζ (cylinderRadialConstant (m + 1))
  let G := scalarSubsolutionGradientSum (d := m + 1) ζ
  let F := fun k (x : Vec (m + 1)) => ∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x
  let J := fun x : Vec (m + 1) => vecDot (smoothGrad φ x) (matVecMul (a x) (G x))
  let P := fun k (x : Vec (m + 1)) => vecDot (smoothGrad φ x) (matVecMul (a x) (F k x))
  have hcore := Weighted.isSmoothCore_of_supported ha hφ hc
  have hiJ : Integrable J μ := (Weighted.pairing_integrable_and_bound ha
    (Weighted.smoothGrad_aestronglyMeasurable hV.isOpen hφ.contDiffOn) hu.2.1
    hcore.2.2 (Weighted.MemH1a.energy_lt_top hV.isOpen ha hu)).1
  have hiP : ∀ k, Integrable (P k) μ ∧ (∫ x, P k x ∂μ) ≤ 0 := fun k =>
    scalarCylinder_partial_test_nonpos hm hζ0 hζ2 k hφ hc hs hn
  have hbound : ∀ k, ∀ᵐ x ∂μ, ‖P k x‖ ≤ |J x| := by
    intro k
    apply Eventually.of_forall
    intro x
    rcases scalarCylinder_partial_gradient_cases (by omega) hζ0 hζ2 x k with hz | heq
    · dsimp only [P, F]
      rw [hz, matVecMul_zero]
      simp only [vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, norm_zero]
      exact abs_nonneg _
    · change ‖vecDot (smoothGrad φ x) (matVecMul (a x) (F k x))‖ ≤ |J x|
      rw [show F k x = G x from heq]
      exact le_of_eq (Real.norm_eq_abs _)
  have ht := tendsto_integral_of_dominated_convergence (f := J) (fun x => |J x|)
    (fun k => (hiP k).1.1) hiJ.abs hbound (Eventually.of_forall (fun x => ?_))
  · exact ⟨hiJ, le_of_tendsto ht (Eventually.of_forall (fun k => (hiP k).2))⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [scalarCylinder_partials_eventually_eq (by omega) hζ0 hζ2 x] with k hk
    simp only [P, F, J, G, hk.2]

end

end CoarseDeGiorgi.SharpnessExamples
