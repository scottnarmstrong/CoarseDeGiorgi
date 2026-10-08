module

public import CoarseDeGiorgi.SharpnessExamples.ScalarIntegrability
public import CoarseDeGiorgi.SharpnessExamples.ScalarSeries

/-! # Positive majorants for the scalar cylinder field and its inverse -/

@[expose] public section

open Homogenization MeasureTheory
open CoarseDeGiorgi.Sharpness CoarseDeGiorgi.Foundations.FracGeometry
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem scalarRadius_pos (d n : ℕ) (ζ κ : ℝ) :
    0 < cylinderRadius d n ζ κ := by
  have hb := cylinderB_pos n
  have ht : 0 < cylinderTail d n κ := by
    unfold cylinderTail
    exact div_pos (mul_pos (by positivity) hb)
      (mul_pos (by positivity) (Real.exp_pos _))
  unfold cylinderRadius
  apply lt_min
  · exact div_pos hb (by positivity)
  · apply lt_min (Real.rpow_pos_of_pos hb _)
    exact lt_min (Real.rpow_pos_of_pos hb _) (Real.rpow_pos_of_pos ht _)

/-- The positive majorant summand on a cylinder of radius `L ε_n`. -/
def scalarMajorantTerm (m n : ℕ) (ζ κ α L : ℝ) (x : Vec (m + 1)) : ℝ :=
  cylinderB n * Real.rpow (cylinderRadius (m + 1) n ζ κ) (-α) *
    {x : Vec (m + 1) | transverseNorm
      (flatJoin 0 (scalarTailCenter m n) - x) <
        L * cylinderRadius (m + 1) n ζ κ}.indicator (fun _ => (1 : ℝ)) x

theorem scalarMajorantTerm_nonneg (m n : ℕ) (ζ κ α L : ℝ)
    (x : Vec (m + 1)) : 0 ≤ scalarMajorantTerm m n ζ κ α L x := by
  unfold scalarMajorantTerm
  apply mul_nonneg
  · exact mul_nonneg (cylinderB_pos n).le
      (Real.rpow_nonneg (scalarRadius_pos _ _ _ _).le _)
  · exact Set.indicator_nonneg (fun _ _ => by norm_num) x

theorem scalarMajorantTerm_integrable (m n : ℕ) (ζ κ α L : ℝ) :
    IntegrableOn (scalarMajorantTerm m n ζ κ α L) (originCube 1) volume := by
  have hcube : volume (originCube (d := m + 1) 1) ≠ ⊤ := by
    rw [Assembly.ClassicalMomentsImpl.originCube_volume_one]
    simp
  exact ((integrableOn_const hcube : IntegrableOn (fun _ : Vec (m + 1) => (1 : ℝ))
    (originCube 1) volume).indicator
      (cylinderTube_measurable (L * cylinderRadius (m + 1) n ζ κ) (scalarTailCenter m n))).const_mul _

theorem scalarMajorantTerm_pointwise_summable {m : ℕ} (hm : 2 ≤ m)
    {ζ κ α L : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ)
    (hL : L ≤ 2) (x : Vec (m + 1)) :
    Summable (fun n => scalarMajorantTerm m n ζ κ α L x) := by
  classical
  have hsupport {n : ℕ} (hn : scalarMajorantTerm m n ζ κ α L x ≠ 0) :
      x ∈ outerCylinder n ζ κ := by
    have hmem : transverseNorm (flatJoin 0 (scalarTailCenter m n) - x) <
        L * cylinderRadius (m + 1) n ζ κ := by
      by_contra h
      simp [scalarMajorantTerm, h] at hn
    change transverseNorm (x - cylinderCenter (cylinderB n)) ≤ _
    rw [scalarShiftedTransverseNorm_eq]
    exact hmem.le.trans (mul_le_mul_of_nonneg_right hL
      (cylinderRadius_data (d := m + 1) (n := n) (by omega) hζ0 hζ2 hκ).1.le)
  have hunique {i j : ℕ}
      (hi : scalarMajorantTerm m i ζ κ α L x ≠ 0)
      (hj : scalarMajorantTerm m j ζ κ α L x ≠ 0) : i = j := by
    by_contra hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact Set.disjoint_left.mp
        (outerCylinder_pairwise_disjoint (by omega) hζ0 hζ2 hκ hlt) (hsupport hi) (hsupport hj)
    · exact Set.disjoint_left.mp
        (outerCylinder_pairwise_disjoint (by omega) hζ0 hζ2 hκ hlt) (hsupport hj) (hsupport hi)
  by_cases hex : ∃ n, scalarMajorantTerm m n ζ κ α L x ≠ 0
  · obtain ⟨n, hn⟩ := hex
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton n).subset
    intro j hj
    exact Set.mem_singleton_iff.mpr (hunique hj hn)
  · have hz : ∀ n, scalarMajorantTerm m n ζ κ α L x = 0 := by
      intro n
      by_contra h
      exact hex ⟨n, h⟩
    simp only [hz]
    exact summable_zero

private theorem scalarMajorant_integral_bound {m : ℕ} (hm : 2 ≤ m)
    {ζ κ α L : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ)
    (hα : α ≤ (m : ℝ)) (hL0 : 0 < L) (hL2 : L ≤ 2) (n : ℕ) :
    (∫ x in originCube 1, ‖scalarMajorantTerm m n ζ κ α L x‖ ∂volume) ≤
      (4 : ℝ) ^ m * cylinderB n := by
  let ε := cylinderRadius (m + 1) n ζ κ
  let A := cylinderB n * Real.rpow ε (-α)
  let E := {x : Vec (m + 1) | transverseNorm (flatJoin 0 (scalarTailCenter m n) - x) < L * ε}
  have hrad := scalarRadius_small (m := m) (k := n) (by omega) hζ0 hζ2 hκ
  have hε : 0 < ε := hrad.1
  have hLrad : L * ε < 1 / 4 :=
    (mul_le_mul_of_nonneg_right hL2 hε.le).trans_lt hrad.2
  have hA : 0 ≤ A := mul_nonneg (cylinderB_pos n).le (Real.rpow_nonneg hε.le _)
  have hnorm : (fun x => ‖scalarMajorantTerm m n ζ κ α L x‖) =
      fun x => A * E.indicator (fun _ => (1 : ℝ)) x := by
    funext x
    rw [Real.norm_of_nonneg (scalarMajorantTerm_nonneg _ _ _ _ _ _ x)]
    rfl
  rw [hnorm, integral_const_mul]
  have hint : (∫ x in originCube 1, E.indicator (fun _ => (1 : ℝ)) x ∂volume) =
      (volume (averagesCylinder (L * ε) (scalarTailCenter m n))).toReal := by
    rw [integral_indicator (cylinderTube_measurable (L * ε) (scalarTailCenter m n))]
    simp only [integral_const, measureReal_def, smul_eq_mul, mul_one,
      Measure.restrict_apply_univ, Measure.restrict_apply
        (cylinderTube_measurable (L * ε) (scalarTailCenter m n))]
    rw [Set.inter_comm]
    rfl
  rw [hint]
  have hvol := (averagesCylinder_volume_bounds (L * ε) (scalarTailCenter m n)
    (mul_pos hL0 hε) hLrad scalarTailCenter_coord_bound).2
  have hpow : Real.rpow ε ((m : ℝ) - α) ≤ 1 :=
    Real.rpow_le_one hε.le (by linarith [hrad.2]) (sub_nonneg.mpr hα)
  have hfactor : A * (4 * ε) ^ m =
      (4 : ℝ) ^ m * (cylinderB n * Real.rpow ε ((m : ℝ) - α)) := by
    dsimp [A]
    rw [mul_pow, ← Real.rpow_natCast ε m]
    have hcomb : Real.rpow ε (-α) * Real.rpow ε (m : ℝ) =
        Real.rpow ε ((m : ℝ) - α) := by
      calc
        _ = Real.rpow ε (-α + (m : ℝ)) := (Real.rpow_add hε _ _).symm
        _ = _ := by congr 1; ring
    change cylinderB n * Real.rpow ε (-α) *
      ((4 : ℝ) ^ m * Real.rpow ε (m : ℝ)) = _
    rw [show cylinderB n * Real.rpow ε (-α) *
      ((4 : ℝ) ^ m * Real.rpow ε (m : ℝ)) =
      (4 : ℝ) ^ m * (cylinderB n * (Real.rpow ε (-α) * Real.rpow ε (m : ℝ))) by ring,
      hcomb]
    simp only [Real.rpow_eq_pow]
  calc
    _ ≤ A * (2 * (L * ε)) ^ m := mul_le_mul_of_nonneg_left hvol hA
    _ ≤ A * (4 * ε) ^ m := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by nlinarith) _) hA
    _ = (4 : ℝ) ^ m * (cylinderB n * Real.rpow ε ((m : ℝ) - α)) := hfactor
    _ ≤ (4 : ℝ) ^ m * cylinderB n := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (cylinderB_pos n).le)
        (by positivity)

theorem scalarMajorant_integral_summable {m : ℕ} (hm : 2 ≤ m)
    {ζ κ α L : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ)
    (hα : α ≤ (m : ℝ)) (hL0 : 0 < L) (hL2 : L ≤ 2) :
    Summable (fun n => ∫ x in originCube 1, ‖scalarMajorantTerm m n ζ κ α L x‖ ∂volume) := by
  have hb : Summable cylinderB := by
    change Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 3))
    simpa only [pow_add] using summable_geometric_two.mul_right ((1 / 2 : ℝ) ^ 3)
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
    (scalarMajorant_integral_bound hm hζ0 hζ2 hκ hα hL0 hL2) (hb.mul_left ((4 : ℝ) ^ m))

theorem scalarSharpnessWeight_majorant {m : ℕ} (hm : 2 ≤ m)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (x : Vec (m + 1)) :
    scalarSharpnessWeight ζ κ x ≤ 1 + ∑' n, scalarMajorantTerm m n ζ κ ζ 1 x := by
  classical
  by_cases hex : ∃ n, x ∈ scalarCoreBand n ζ κ
  · obtain ⟨n, hn⟩ := hex
    rw [scalarSharpnessWeight_eq_core (by omega) hζ0 hζ2 hκ hn]
    have hterm : scalarMajorantTerm m n ζ κ ζ 1 x = scalarCoreValue (m + 1) n ζ κ := by
      have hmem : transverseNorm (flatJoin 0 (scalarTailCenter m n) - x) <
          cylinderRadius (m + 1) n ζ κ := by
        simpa only [scalarCoreBand, Set.mem_ofPred_eq, scalarShiftedTransverseNorm_eq] using hn
      simp [scalarMajorantTerm, scalarCoreValue, hmem]
    have hle := (scalarMajorantTerm_pointwise_summable (α := ζ) hm hζ0 hζ2 hκ
      (by norm_num : (1 : ℝ) ≤ 2) x).le_tsum n
      (fun j _ => scalarMajorantTerm_nonneg _ _ _ _ _ _ x)
    rw [hterm] at hle
    linarith
  · have hnonpos : ∀ n, scalarCylinderContribution n ζ κ x ≤ 0 := by
      intro n
      have hn : x ∉ scalarCoreBand n ζ κ := fun h => hex ⟨n, h⟩
      unfold scalarCylinderContribution
      rw [ite_eq_right hn]
      split_ifs
      · have hle := (cylinderRadius_data (by omega) hζ0 hζ2 hκ
          (d := m + 1) (n := n)).2.2.2.1
        change scalarAnnulusValue (m + 1) n ζ κ ≤ 1 at hle
        linarith
      · exact le_rfl
    have hweight : scalarSharpnessWeight ζ κ x ≤ 1 := by
      unfold scalarSharpnessWeight
      have ht : (∑' n : ℕ, scalarCylinderContribution n ζ κ x) ≤ 0 := tsum_nonpos hnonpos
      linarith only [ht]
    exact hweight.trans (le_add_of_nonneg_right (tsum_nonneg
      (fun n => scalarMajorantTerm_nonneg _ _ _ _ _ _ x)))

theorem scalarInvSharpnessWeight_majorant {m : ℕ} (hm : 2 ≤ m)
    {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (x : Vec (m + 1)) :
    (scalarSharpnessWeight ζ κ x)⁻¹ ≤
      1 + ∑' n, scalarMajorantTerm m n ζ κ (2 - ζ) 2 x := by
  classical
  by_cases hex : ∃ n, x ∈ scalarAnnulusBand n ζ κ
  · obtain ⟨n, hn⟩ := hex
    rw [scalarSharpnessWeight_eq_annulus (by omega) hζ0 hζ2 hκ hn]
    have hmem : transverseNorm (flatJoin 0 (scalarTailCenter m n) - x) <
        2 * cylinderRadius (m + 1) n ζ κ := by
      simpa only [scalarShiftedTransverseNorm_eq] using hn.2
    have hterm : scalarMajorantTerm m n ζ κ (2 - ζ) 2 x =
        (scalarAnnulusValue (m + 1) n ζ κ)⁻¹ := by
      unfold scalarMajorantTerm
      rw [Set.indicator_of_mem (show x ∈ {x : Vec (m + 1) | transverseNorm
        (flatJoin 0 (scalarTailCenter m n) - x) < 2 * cylinderRadius (m + 1) n ζ κ} from hmem)]
      simp only [mul_one, scalarAnnulusValue]
      simp only [Real.rpow_eq_pow, mul_inv, inv_inv,
        ← Real.rpow_neg (cylinderRadius_data (d := m + 1) (n := n) (by omega) hζ0 hζ2 hκ).1.le]
    have hle := (scalarMajorantTerm_pointwise_summable (α := 2 - ζ) hm hζ0 hζ2 hκ le_rfl x).le_tsum n
      (fun j _ => scalarMajorantTerm_nonneg _ _ _ _ _ _ x)
    rw [hterm] at hle
    linarith
  · have hweight : 1 ≤ scalarSharpnessWeight ζ κ x := by
      unfold scalarSharpnessWeight
      apply le_add_of_nonneg_right
      apply tsum_nonneg
      intro n
      have hn : x ∉ scalarAnnulusBand n ζ κ := fun h => hex ⟨n, h⟩
      unfold scalarCylinderContribution
      rw [ite_eq_right hn]
      split_ifs
      · have hle := (cylinderRadius_data (by omega) hζ0 hζ2 hκ
          (d := m + 1) (n := n)).2.2.1
        change 1 ≤ scalarCoreValue (m + 1) n ζ κ at hle
        linarith
      · exact le_rfl
    have hinv : (scalarSharpnessWeight ζ κ x)⁻¹ ≤ 1 :=
      (inv_le_one₀ (scalarSharpnessWeight_pos (by omega) hζ0 hζ2 hκ x)).2 hweight
    exact hinv.trans (le_add_of_nonneg_right (tsum_nonneg
      (fun n => scalarMajorantTerm_nonneg _ _ _ _ _ _ x)))

end

end CoarseDeGiorgi.SharpnessExamples
