module

public import CoarseDeGiorgi.SharpnessExamples.ScalarLargeSets
public import CoarseDeGiorgi.SharpnessExamples.ScalarGradientBounds

/-! # Pointwise finite support of the value and gradient series -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem vecNormSq_zero {d : ℕ} : vecNormSq (0 : Vec d) = 0 := by
  simp only [vecNormSq, vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- The explicit gradient series of the source's cylinder sum. -/
def scalarSubsolutionGradientSum {d : ℕ} [NeZero d] (ζ : ℝ) (x : Vec d) : Vec d :=
  ∑' n : ℕ, scalarCylinderGradient n ζ x

theorem scalarCylinder_pair_zero_of_not_outer {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) {n : ℕ} {x : Vec d}
    (hx : x ∉ outerCylinder n ζ (cylinderRadialConstant d)) :
    scalarCylinderSubsolution n ζ x = 0 ∧ scalarCylinderGradient n ζ x = 0 := by
  have hr : 2 * cylinderRadius d n ζ (cylinderRadialConstant d) ≤
      transverseNorm (x - cylinderCenter (cylinderB n)) :=
    (not_le.mp hx).le
  refine ⟨?_, scalarCylinderGradient_eq_zero_outer hd hζ0 hζ2 hr⟩
  simp only [scalarCylinderSubsolution, scalarRadialProfile_eq_zero hd hζ0 hζ2 hr, mul_zero]

/-- At each point there is either no nonzero pair or a unique possible index. -/
theorem scalarCylinder_pair_pointwise {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (x : Vec d) :
    (∀ n, scalarCylinderSubsolution n ζ x = 0 ∧ scalarCylinderGradient n ζ x = 0) ∨
    ∃ n, ∀ j, j ≠ n →
      scalarCylinderSubsolution j ζ x = 0 ∧ scalarCylinderGradient j ζ x = 0 := by
  classical
  by_cases hex : ∃ n, x ∈ outerCylinder n ζ (cylinderRadialConstant d)
  · obtain ⟨n, hn⟩ := hex
    right
    refine ⟨n, fun j hj => scalarCylinder_pair_zero_of_not_outer hd hζ0 hζ2 ?_⟩
    intro hjx
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · exact (Set.disjoint_left.mp (outerCylinder_pairwise_disjoint hd hζ0 hζ2
        (cylinderRadialConstant_pos hd) hlt)) hjx hn
    · exact (Set.disjoint_left.mp (outerCylinder_pairwise_disjoint hd hζ0 hζ2
        (cylinderRadialConstant_pos hd) hgt)) hn hjx
  · left
    exact fun n => scalarCylinder_pair_zero_of_not_outer hd hζ0 hζ2
      (fun hn => hex ⟨n, hn⟩)

private theorem partial_single {E : Type*} [AddCommMonoid E] {f : ℕ → E}
    {n : ℕ} (hn : ∀ j, j ≠ n → f j = 0) (k : ℕ) :
    (∑ j ∈ Finset.range k, f j) = if n < k then f n else 0 := by
  classical
  by_cases hnk : n < k
  · rw [ite_eq_left hnk]
    exact Finset.sum_eq_single n (fun j _ hj => hn j hj)
      (fun h => (h (Finset.mem_range.mpr hnk)).elim)
  · rw [ite_eq_right hnk]
    apply Finset.sum_eq_zero
    intro j hj
    exact hn j (fun h => hnk (h ▸ Finset.mem_range.mp hj))

/-- At every point both finite sums eventually equal their literal series. -/
theorem scalarCylinder_partials_eventually_eq {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (x : Vec d) :
    ∀ᶠ k in atTop,
      (∑ j ∈ Finset.range k, scalarCylinderSubsolution j ζ x) = scalarSubsolutionSum ζ x ∧
      (∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x) = scalarSubsolutionGradientSum ζ x := by
  classical
  rcases scalarCylinder_pair_pointwise hd hζ0 hζ2 x with hzero | ⟨n, hn⟩
  · apply Eventually.of_forall
    intro k
    simp only [scalarSubsolutionSum, scalarSubsolutionGradientSum,
      funext (fun j => (hzero j).1), funext (fun j => (hzero j).2),
      Finset.sum_const_zero, tsum_zero, and_self]
  · have hu : scalarSubsolutionSum ζ x = scalarCylinderSubsolution n ζ x :=
      tsum_eq_single n (fun j hj => (hn j hj).1)
    have hG : scalarSubsolutionGradientSum ζ x = scalarCylinderGradient n ζ x :=
      tsum_eq_single n (fun j hj => (hn j hj).2)
    filter_upwards [eventually_gt_atTop n] with k hk
    rw [partial_single (fun j hj => (hn j hj).1),
      partial_single (fun j hj => (hn j hj).2), ite_eq_left hk, ite_eq_left hk, hu, hG]
    exact ⟨rfl, rfl⟩

/-- The density series is the density of the summed pair, without cross terms. -/
theorem scalarCylinder_density_tsum {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (x : Vec d) (w : ℝ) :
    (∑' n : ℕ, w * (scalarCylinderSubsolution n ζ x ^ 2 +
      vecNormSq (scalarCylinderGradient n ζ x))) =
    w * (scalarSubsolutionSum ζ x ^ 2 + vecNormSq (scalarSubsolutionGradientSum ζ x)) := by
  rcases scalarCylinder_pair_pointwise hd hζ0 hζ2 x with hzero | ⟨n, hn⟩
  · simp only [scalarSubsolutionSum, scalarSubsolutionGradientSum]
    simp_rw [show ∀ j, scalarCylinderSubsolution j ζ x = 0 from fun j => (hzero j).1,
      show ∀ j, scalarCylinderGradient j ζ x = 0 from fun j => (hzero j).2]
    simp only [tsum_zero, zero_pow (by norm_num : 2 ≠ 0), vecNormSq_zero, add_zero, mul_zero]
  · have hu : scalarSubsolutionSum ζ x = scalarCylinderSubsolution n ζ x :=
      tsum_eq_single n (fun j hj => (hn j hj).1)
    have hG : scalarSubsolutionGradientSum ζ x = scalarCylinderGradient n ζ x :=
      tsum_eq_single n (fun j hj => (hn j hj).2)
    rw [hu, hG]
    apply tsum_eq_single n
    intro j hj
    rw [(hn j hj).1, (hn j hj).2]
    simp only [zero_pow (by norm_num : 2 ≠ 0), vecNormSq_zero, add_zero, mul_zero]

/-- Finite-sum errors are bounded by the squared size of the total pair. -/
theorem scalarCylinder_partial_error_bounds {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (x : Vec d) (k : ℕ) :
    |(∑ j ∈ Finset.range k, scalarCylinderSubsolution j ζ x) - scalarSubsolutionSum ζ x| ≤
      |scalarSubsolutionSum ζ x| ∧
    vecNormSq ((∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x) -
      scalarSubsolutionGradientSum ζ x) ≤ vecNormSq (scalarSubsolutionGradientSum ζ x) := by
  classical
  rcases scalarCylinder_pair_pointwise hd hζ0 hζ2 x with hzero | ⟨n, hn⟩
  · simp only [scalarSubsolutionSum, scalarSubsolutionGradientSum,
      funext (fun j => (hzero j).1), funext (fun j => (hzero j).2),
      Finset.sum_const_zero, tsum_zero, sub_self, abs_zero, le_refl, and_self]
  · have hu : scalarSubsolutionSum ζ x = scalarCylinderSubsolution n ζ x :=
      tsum_eq_single n (fun j hj => (hn j hj).1)
    have hG : scalarSubsolutionGradientSum ζ x = scalarCylinderGradient n ζ x :=
      tsum_eq_single n (fun j hj => (hn j hj).2)
    rw [partial_single (fun j hj => (hn j hj).1),
      partial_single (fun j hj => (hn j hj).2), hu, hG]
    by_cases hnk : n < k
    · simp only [ite_eq_left hnk, sub_self, abs_zero, vecNormSq_zero]
      exact ⟨abs_nonneg _, vecNormSq_nonneg _⟩
    · simp only [ite_eq_right hnk, zero_sub, abs_neg, vecNormSq, vecDot,
        Pi.neg_apply, neg_mul_neg, le_refl, and_self]

/-- A partial gradient is either zero or the full pointwise gradient. -/
theorem scalarCylinder_partial_gradient_cases {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (x : Vec d) (k : ℕ) :
    (∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x) = 0 ∨
    (∑ j ∈ Finset.range k, scalarCylinderGradient j ζ x) = scalarSubsolutionGradientSum ζ x := by
  classical
  rcases scalarCylinder_pair_pointwise hd hζ0 hζ2 x with hzero | ⟨n, hn⟩
  · left
    exact Finset.sum_eq_zero (fun j _ => (hzero j).2)
  · have hG : scalarSubsolutionGradientSum ζ x = scalarCylinderGradient n ζ x :=
      tsum_eq_single n (fun j hj => (hn j hj).2)
    rw [partial_single (fun j hj => (hn j hj).2)]
    by_cases hnk : n < k
    · exact Or.inr (by rw [ite_eq_left hnk, hG])
    · exact Or.inl (ite_eq_right hnk)

end

end CoarseDeGiorgi.SharpnessExamples
