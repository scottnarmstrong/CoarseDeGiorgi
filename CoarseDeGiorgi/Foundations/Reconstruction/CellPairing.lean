import CoarseDeGiorgi.Foundations.Reconstruction.ReflectedCenters
import CoarseDeGiorgi.Foundations.Reconstruction.KernelApproximation
import CoarseDeGiorgi.Foundations.Reconstruction.CancellationJets
import CoarseDeGiorgi.Foundations.Reconstruction.SchurLp

/-! # Exact removal of parent-center contributions from the gradient increments -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Reflected finite average fields are globally measurable for arbitrary input data. -/
theorem measurable_reflectedAverage (m : ℤ) (j : ℕ) (z : Fin d → ℤ) (f : Vec d → Vec d) :
    Measurable (reflectedAverage m j z f) := by
  apply measurable_pi_iff.mpr
  intro i
  have hs : Measurable (fun x : Vec d => reflectionSign (decide (0 < x i))) := by
    have heq : (fun x : Vec d => reflectionSign (decide (0 < x i))) =
        fun x => if 0 < x i then (1 : ℝ) else -1 := by
      funext x
      by_cases h : 0 < x i <;> simp only [h, decide_true, decide_false, reflectionSign, Bool.false_eq_true, ite_true, ite_false]
    rw [heq]
    exact Measurable.ite ((isOpen_lt continuous_const (continuous_apply i)).measurableSet)
      measurable_const measurable_const
  exact hs.mul (((measurable_pi_apply i).comp (measurable_auxAverage m (m + j) z f)).comp
    (measurable_const.add (measurable_pi_iff.mpr fun a => (continuous_apply a).abs.measurable)))

/-- Each reflected orthant is contained in the full integration box. -/
theorem reflectionOrthant_subset_reflectionBox (m : ℤ) (s : Fin d → Bool) :
    reflectionOrthant m s ⊆ reflectionBox m := by
  intro x hx
  exact ((mem_iUnion_reflectionOrthant m x).mp (Set.mem_iUnion.mpr ⟨s, hx⟩)).1

/-- The reflected cell partition permits ordinary finite integration on each orthant. -/
theorem setIntegral_reflectedCells {m : ℤ} {z : Fin d → ℤ} (j : ℕ)
    {F : Vec d → ℝ} (hF : IntegrableOn F (reflectionBox m) volume) :
    ∫ y in reflectionBox m, F y =
      ∑ s : Fin d → Bool, ∑ R ∈ descendantsAtDepth (originCube d (1 - m)) j,
        ∫ y in reflectedCell m z s R, F y := by
  rw [setIntegral_congr_set (reflectionBox_ae_eq_iUnion_orthant m),
    integral_iUnion_fintype (measurableSet_reflectionOrthant m)
      (pairwise_disjoint_reflectionOrthant m) ((integrableOn_reflectionBox_iff m F).mp hF)]
  apply Finset.sum_congr rfl
  intro s _
  have horth : IntegrableOn F (reflectionOrthant m s) volume :=
    hF.mono_set (reflectionOrthant_subset_reflectionBox m s)
  rw [setIntegral_congr_set (reflectionOrthant_ae_eq_iUnion_reflectedCell m z s j)]
  apply integral_biUnion_finset
  · intro R _
    exact (isOpen_openCubeSet R).measurableSet.preimage (reflectionChart m z s).measurable
  · intro R hR S hS hRS
    exact disjoint_reflectedCell_of_mem_descendantsAtDepth m z s hR hS hRS
  · intro R hR
    rw [← reflectedCell_root_eq_orthant m z s] at horth
    exact horth.mono_set (reflectedCell_subset_of_mem_descendantsAtDepth m z s hR)

/-- Constant vectors pair to zero with an increment on every parent cell. -/
theorem integral_vecDot_reflected_increment_eq_zero {m : ℤ} {z : Fin d → ℤ}
    (s : Fin d → Bool) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube d (1 - m)) j)
    (f : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume) (v : Vec d) :
    ∫ y in reflectedCell m z s R,
      vecDot v (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y) = 0 := by
  have hi (k : ℕ) : IntegrableOn (reflectedAverage m k z f) (reflectedCell m z s R) volume :=
    (integrableOn_reflectedGradient
      (memLp_one_iff_integrable.mp (memLp_auxAverage m (m + k) z f 1))).mono_set
        ((reflectedCell_subset_of_mem_descendantsAtDepth m z s hR).trans
          (by rw [reflectedCell_root_eq_orthant]; exact reflectionOrthant_subset_reflectionBox m s))
  simp only [vecDot, Pi.sub_apply]
  have hcoord (i : Fin d) : IntegrableOn (fun y =>
      v i * (reflectedAverage m (j + 1) z f y i - reflectedAverage m j z f y i))
      (reflectedCell m z s R) volume :=
    (((hi (j + 1)).eval i).sub ((hi j).eval i)).const_mul (v i)
  rw [integral_finsetSum _ (fun i _ => hcoord i)]
  simp only [integral_const_mul, integral_reflectedAverage_increment_coordinate_eq_zero m z s hR f hf,
    mul_zero, Finset.sum_const_zero]

/-- The parent-center contribution vanishes exactly, before any Lʳ estimate. -/
theorem integral_parentCenter_pairing_eq_zero {m : ℤ} {z : Fin d → ℤ} (j : ℕ)
    (f : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume)
    (K : Vec d → Vec d) (x : Vec d)
    (hi : IntegrableOn (fun y => vecDot (K (x - reflectedParentCenter m z j y))
      (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y)) (reflectionBox m) volume) :
    ∫ y in reflectionBox m, vecDot (K (x - reflectedParentCenter m z j y))
      (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y) = 0 := by
  rw [setIntegral_reflectedCells (z := z) j hi]
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro R hR
  have hcenter : ∀ y ∈ reflectedCell m z s R,
      reflectedParentCenter m z j y = reflectedCenter m z s R := fun y hy =>
    reflectedParentCenter_eq_of_mem (m := m) (z := z) (j := j) (p := (s, R))
      (Finset.mem_product.mpr ⟨Finset.mem_univ s, hR⟩) hy
  have heq : (∫ y in reflectedCell m z s R,
      vecDot (K (x - reflectedParentCenter m z j y))
        (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y)) =
      ∫ y in reflectedCell m z s R, vecDot (K (x - reflectedCenter m z s R))
        (reflectedAverage m (j + 1) z f y - reflectedAverage m j z f y) := by
    apply setIntegral_congr_fun ((isOpen_openCubeSet R).measurableSet.preimage
      (reflectionChart m z s).measurable)
    intro y hy
    dsimp only
    rw [hcenter y hy]
  rw [heq]
  exact integral_vecDot_reflected_increment_eq_zero s hR f hf _

end

end CoarseDeGiorgi.Foundations.Reconstruction
