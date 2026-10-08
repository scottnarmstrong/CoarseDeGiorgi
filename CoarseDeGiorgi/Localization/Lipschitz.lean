import CoarseDeGiorgi.Localization.Bumps
import CoarseDeGiorgi.Foundations.FracGeometry.ChartLipschitz

/-! # Uniform partition bounds independent of the cover cardinality -/
namespace CoarseDeGiorgi.Localization
open Homogenization Set Metric CoarseDeGiorgi.Foundations
open scoped BigOperators Topology ContDiff NNReal
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

/-- The scalar smooth switch has a finite global Lipschitz constant. -/
theorem exists_smoothTransition_lipschitz : ∃ L : ℝ≥0, LipschitzWith L Real.smoothTransition := by
  obtain ⟨L, hL⟩ := (Real.smoothTransition.contDiff (n := ⊤)).contDiffOn.exists_lipschitzOnWith
    (by norm_num : (∞ : ℕ∞ω) ≠ 0) (convex_Icc (0 : ℝ) 1) isCompact_Icc
  refine ⟨L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hh := hL.dist_le_mul (projIcc 0 1 zero_le_one x) (projIcc 0 1 zero_le_one x).property
    (projIcc 0 1 zero_le_one y) (projIcc 0 1 zero_le_one y).property
  simp only [Real.smoothTransition.projIcc] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (by simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using ((LipschitzWith.projIcc zero_le_one).dist_le_mul x y)) (NNReal.coe_nonneg L))

/-- Nonzero bumps belong to the closed auxiliary cubes counted in Geometry. -/
theorem support_bump_subset_closedAuxCube (m : ℤ) (z : Fin d → ℤ) :
    Function.support (localizationBump m z) ⊆ closedAuxCube m z := by
  rw [support_localizationBump]
  intro x hx i
  have hi : |x i - gridCenter m z i| ≤ ‖x - gridCenter m z‖ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x - gridCenter m z) i
  have hn := mem_ball_iff_norm.mp hx
  linarith only [hi, hn, gridSpacing_pos m]

theorem card_filter_bump_ne_zero_le (m : ℤ) (Z : Finset (Fin d → ℤ)) (x : Vec d) :
    (Z.filter fun z => localizationBump m z x ≠ 0).card ≤ 4 ^ d := by
  apply le_trans _ (card_filter_closedAuxCube_le m Z x)
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzZ, hzB⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hzZ, support_bump_subset_closedAuxCube m z hzB⟩

/-- A sum difference involves supports at both endpoints; at most twice the overlap. -/
theorem bumpSum_difference_le {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ (m : ℤ) (z : Fin d → ℤ) (x y : Vec d),
      |localizationBump m z x - localizationBump m z y| ≤ (L / gridSpacing m) * dist x y)
    (m : ℤ) (Z : Finset (Fin d → ℤ)) (x y : Vec d) :
    |bumpSum m Z x - bumpSum m Z y| ≤
      (2 * (4 : ℝ) ^ d * L / gridSpacing m) * dist x y := by
  let A := (Z.filter fun z => localizationBump m z x ≠ 0) ∪
    (Z.filter fun z => localizationBump m z y ≠ 0)
  have hAZ : A ⊆ Z := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hc : A.card ≤ 2 * 4 ^ d :=
    (Finset.card_union_le _ _).trans (by
      have hx := card_filter_bump_ne_zero_le m Z x
      have hy := card_filter_bump_ne_zero_le m Z y
      omega)
  have he : (∑ z ∈ Z, (localizationBump m z x - localizationBump m z y)) =
      ∑ z ∈ A, (localizationBump m z x - localizationBump m z y) := by
    apply (Finset.sum_subset hAZ ?_).symm
    intro z hz hn
    have hx : localizationBump m z x = 0 := by
      by_contra h
      exact hn (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, h⟩))
    have hy : localizationBump m z y = 0 := by
      by_contra h
      exact hn (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz, h⟩))
    rw [hx, hy, sub_self]
  unfold bumpSum
  rw [← Finset.sum_sub_distrib, he]
  calc
    _ ≤ ∑ z ∈ A, |localizationBump m z x - localizationBump m z y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ A, (L / gridSpacing m) * dist x y := Finset.sum_le_sum fun z _ => hLip m z x y
    _ = (A.card : ℝ) * ((L / gridSpacing m) * dist x y) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (4 : ℝ) ^ d) * ((L / gridSpacing m) * dist x y) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (div_nonneg hL (gridSpacing_pos m).le) dist_nonneg)
      exact_mod_cast hc
    _ = _ := by ring

/-- A regularized denominator computes precisely the literal quotient everywhere. -/
theorem localizationFactor_eq_regularized (t : ℝ) :
    localizationFactor t = localizationSwitch t / max (1 / 2) t := by
  by_cases ht : t ≤ 1 / 2
  · simp only [localizationFactor, localizationSwitch_eq_zero ht, zero_div]
  · rw [localizationFactor, max_eq_right (not_le.mp ht).le]

/-- A uniform bound for the quotient factor on the nonnegative half-line. -/
theorem localizationFactor_bound (t : ℝ) : |localizationFactor t| ≤ 2 := by
  rw [localizationFactor_eq_regularized, abs_div, abs_of_nonneg (localizationSwitch_nonneg _),
    abs_of_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_left _ _))]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_left _ _))).mpr
  have h := localizationSwitch_le_one t
  have hm : 1 / 2 ≤ max (1 / 2) t := le_max_left _ _
  linarith only [h, hm]

/-- Smooth quotient factor is Lipschitz with a fixed constant. -/
theorem localizationFactor_difference_le {L : ℝ≥0} (hL : LipschitzWith L Real.smoothTransition)
    (a b : ℝ) : |localizationFactor a - localizationFactor b| ≤
      (8 * (L : ℝ) + 4) * |a - b| := by
  let A := max (1 / 2 : ℝ) a
  let B := max (1 / 2 : ℝ) b
  have hA : 1 ≤ 2 * A := by dsimp [A]; linarith only [le_max_left (1 / 2 : ℝ) a]
  have hB : 1 ≤ 2 * B := by dsimp [B]; linarith only [le_max_left (1 / 2 : ℝ) b]
  have hnum : |localizationSwitch b| ≤ 2 * B := by
    rw [abs_of_nonneg (localizationSwitch_nonneg _)]
    exact (localizationSwitch_le_one _).trans hB
  have hh := FracGeometry.abs_div_sub_div_le_normalized (a := localizationSwitch a) hA hB hnum
  have hη := hL.dist_le_mul (4 * a - 2) (4 * b - 2)
  have hη' : |localizationSwitch a - localizationSwitch b| ≤ 4 * (L : ℝ) * |a - b| := by
    rw [Real.dist_eq, Real.dist_eq, show 4 * a - 2 - (4 * b - 2) = 4 * (a - b) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hη
    simpa only [localizationSwitch, mul_assoc, mul_comm, mul_left_comm] using hη
  have hden : |A - B| ≤ |a - b| := by
    simpa only [A, B, Real.dist_eq, NNReal.coe_one, one_mul, id_eq] using
      (LipschitzWith.id.const_max (1 / 2 : ℝ)).dist_le_mul a b
  have hAe : A ≠ 0 := by dsimp [A]; positivity
  have hBe : B ≠ 0 := by dsimp [B]; positivity
  have he (t : ℝ) (M : ℝ) (hM : M ≠ 0) : t / M = 2 * (t / (2 * M)) := by field_simp
  rw [localizationFactor_eq_regularized, localizationFactor_eq_regularized]
  change |localizationSwitch a / A - localizationSwitch b / B| ≤ _
  rw [he _ A hAe, he _ B hBe, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  linarith only [hh, hη', hden]

/-- Uniform Lipschitz constant for every member of the source partition.
It is fixed before the scale and finite selected cover. -/
theorem exists_localizationPartition_difference_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℤ) (Z : Finset (Fin d → ℤ)) (z : Fin d → ℤ) (x y : Vec d),
      |localizationPartition m Z z x - localizationPartition m Z z y| ≤
        (C / gridSpacing m) * Euclid.eDist2 x y := by
  obtain ⟨L, hL, hb⟩ := exists_localizationBump_difference_bound (d := d)
  obtain ⟨T, hT⟩ := exists_smoothTransition_lipschitz
  let C : ℝ := 2 * L + (8 * (T : ℝ) + 4) * (2 * 4 ^ d * L)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m Z z x y
  have hs := bumpSum_difference_le hL.le hb m Z x y
  have hfac := localizationFactor_difference_le hT (bumpSum m Z x) (bumpSum m Z y)
  have hf := localizationFactor_bound (bumpSum m Z x)
  have hy := localizationBump_le_one m z y
  have hn := localizationBump_nonneg m z y
  have hh : |localizationPartition m Z z x - localizationPartition m Z z y| ≤
      2 * |localizationBump m z x - localizationBump m z y| +
        |localizationFactor (bumpSum m Z x) - localizationFactor (bumpSum m Z y)| := by
    unfold localizationPartition
    have he : localizationBump m z x * localizationFactor (bumpSum m Z x) -
        localizationBump m z y * localizationFactor (bumpSum m Z y) =
        (localizationBump m z x - localizationBump m z y) * localizationFactor (bumpSum m Z x) +
        localizationBump m z y * (localizationFactor (bumpSum m Z x) - localizationFactor (bumpSum m Z y)) := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hn]
    exact add_le_add (by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hf (abs_nonneg (localizationBump m z x - localizationBump m z y)))
      (mul_le_of_le_one_left (abs_nonneg _) hy)
  have hsup : |localizationPartition m Z z x - localizationPartition m Z z y| ≤
      (C / gridSpacing m) * dist x y := by
    have hbase := hb m z x y
    have hcombine : 0 ≤ 8 * (T : ℝ) + 4 := by positivity
    have hfac' := hfac.trans (mul_le_mul_of_nonneg_left hs hcombine)
    dsimp only [C]
    calc
      _ ≤ 2 * ((L / gridSpacing m) * dist x y) +
          (8 * (T : ℝ) + 4) * ((2 * (4 : ℝ) ^ d * L / gridSpacing m) * dist x y) :=
        hh.trans (add_le_add (mul_le_mul_of_nonneg_left hbase (by norm_num)) hfac')
      _ = _ := by ring
  exact hsup.trans (mul_le_mul_of_nonneg_left (Euclid.dist_le_eDist2 x y)
    (div_nonneg hC.le (gridSpacing_pos m).le))

end
end CoarseDeGiorgi.Localization

