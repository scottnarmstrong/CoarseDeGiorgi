import CoarseDeGiorgi.Whitney.SeedNodal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Partition identity for Kuhn nodal hats

A hat is the length of the interval of common rounding thresholds producing
its vertex. These intervals partition `[0,1)`, including on simplex faces.
This proves the nodal partition without choosing a simplex at a boundary.
-/

namespace CoarseDeGiorgi.Whitney

open Homogenization MeasureTheory Set

noncomputable section

variable {d : ℕ}

theorem positivePeak_le_iff {x : Vec d} {r : ℝ} (hr : 0 ≤ r) :
    positivePeak x ≤ r ↔ ∀ i, x i ≤ r := by
  constructor
  · intro h i
    exact (coordinate_le_positivePeak x i).trans h
  · intro h
    apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    exact max_le (h i) hr

theorem positivePeak_lt_iff {x : Vec d} {r : ℝ} (hr : 0 < r) :
    positivePeak x < r ↔ ∀ i, x i < r := by
  constructor
  · intro h i
    exact (coordinate_le_positivePeak x i).trans_lt h
  · intro h
    apply (pi_norm_lt_iff hr).mpr
    intro i
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    exact max_lt (h i) hr

/-- Thresholds for which simultaneous integer rounding produces vertex `m`. -/
def nodalRoundingCell (k : ℕ) (m : Fin d → ℤ) (x : Vec d) : Set ℝ :=
  {t | t ∈ Ico 0 1 ∧ ∀ i, (m i : ℝ) ≤ x i / seedScale k - 1 / 2 + t ∧
    x i / seedScale k - 1 / 2 + t < (m i : ℝ) + 1}

private theorem rounding_lower {s : ℝ} (hs : 0 < s) (a t : ℝ) (m : ℤ) :
    (m : ℝ) ≤ a / s - 1 / 2 + t ↔ s * ((m : ℝ) + 1 / 2) - a ≤ s * t := by
  have heq : s * (a / s - 1 / 2 + t) = a - s / 2 + s * t := by
    rw [mul_add, mul_sub, mul_div_cancel₀ _ hs.ne']
    ring
  rw [← mul_le_mul_iff_right₀ hs]
  rw [heq]
  constructor <;> intro h <;> nlinarith only [h]

private theorem rounding_upper {s : ℝ} (hs : 0 < s) (a t : ℝ) (m : ℤ) :
    a / s - 1 / 2 + t < (m : ℝ) + 1 ↔ a - s * ((m : ℝ) + 1 / 2) < s * (1 - t) := by
  have heq : s * (a / s - 1 / 2 + t) = a - s / 2 + s * t := by
    rw [mul_add, mul_sub, mul_div_cancel₀ _ hs.ne']
    ring
  rw [← mul_lt_mul_iff_right₀ hs]
  rw [heq]
  constructor <;> intro h <;> nlinarith only [h]

theorem nodalRoundingCell_eq_Ico (k : ℕ) (m : Fin d → ℤ) (x : Vec d) :
    nodalRoundingCell k m x =
      Ico (positivePeak (seedNode k m - x) / seedScale k)
        (1 - positivePeak (x - seedNode k m) / seedScale k) := by
  have hs := seedScale_pos k
  ext t
  constructor
  · rintro ⟨ht, hcoord⟩
    have hlo : positivePeak (seedNode k m - x) ≤ t * seedScale k := by
      apply (positivePeak_le_iff (mul_nonneg ht.1 hs.le)).mpr
      intro i
      simpa only [seedNode, Pi.sub_apply, mul_comm t] using
        (rounding_lower hs (x i) t (m i)).mp (hcoord i).1
    have hhi : positivePeak (x - seedNode k m) < (1 - t) * seedScale k := by
      apply (positivePeak_lt_iff (mul_pos (sub_pos.mpr ht.2) hs)).mpr
      intro i
      simpa only [seedNode, Pi.sub_apply, mul_comm (1 - t)] using
        (rounding_upper hs (x i) t (m i)).mp (hcoord i).2
    refine ⟨(div_le_iff₀ hs).mpr hlo, ?_⟩
    have hd := (div_lt_iff₀ hs).mpr hhi
    linarith only [hd]
  · intro ht
    have hlo0 : 0 ≤ positivePeak (seedNode k m - x) / seedScale k :=
      div_nonneg (positivePeak_nonneg _) hs.le
    have hhi0 : 0 ≤ positivePeak (x - seedNode k m) / seedScale k :=
      div_nonneg (positivePeak_nonneg _) hs.le
    have ht0 : 0 ≤ t := hlo0.trans ht.1
    have ht1 : t < 1 := by linarith only [ht.2, hhi0]
    have hlo := (positivePeak_le_iff (mul_nonneg ht0 hs.le)).mp
      ((div_le_iff₀ hs).mp ht.1)
    have hd : positivePeak (x - seedNode k m) / seedScale k < 1 - t := by
      linarith only [ht.2]
    have hhi := (positivePeak_lt_iff (mul_pos (sub_pos.mpr ht1) hs)).mp
      ((div_lt_iff₀ hs).mp hd)
    refine ⟨⟨ht0, ht1⟩, fun i => ⟨?_, ?_⟩⟩
    · apply (rounding_lower hs (x i) t (m i)).mpr
      simpa only [seedNode, Pi.sub_apply, mul_comm t] using hlo i
    · apply (rounding_upper hs (x i) t (m i)).mpr
      simpa only [seedNode, Pi.sub_apply, mul_comm (1 - t)] using hhi i

theorem measurableSet_nodalRoundingCell (k : ℕ) (m : Fin d → ℤ) (x : Vec d) :
    MeasurableSet (nodalRoundingCell k m x) := by
  rw [nodalRoundingCell_eq_Ico]
  exact measurableSet_Ico

theorem seedHat_eq_rounding_volume (k : ℕ) (m : Fin d → ℤ) (x : Vec d) :
    seedHat k m x = (volume (nodalRoundingCell k m x)).toReal := by
  rw [nodalRoundingCell_eq_Ico, Real.volume_Ico]
  have heq : 1 - positivePeak (x - seedNode k m) / seedScale k -
      positivePeak (seedNode k m - x) / seedScale k =
      1 - (positivePeak (x - seedNode k m) + positivePeak (seedNode k m - x)) /
        seedScale k := by ring
  rw [heq]
  simp only [seedHat, nodalHat, ENNReal.toReal_ofReal', max_comm]

theorem pairwise_disjoint_nodalRoundingCell (k : ℕ) (x : Vec d) :
    Pairwise (fun m n : Fin d → ℤ =>
      Disjoint (nodalRoundingCell k m x) (nodalRoundingCell k n x)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro t hm hn
  apply hmn
  funext i
  have hm' : ⌊x i / seedScale k - 1 / 2 + t⌋ = m i :=
    Int.floor_eq_iff.mpr (hm.2 i)
  have hn' : ⌊x i / seedScale k - 1 / 2 + t⌋ = n i :=
    Int.floor_eq_iff.mpr (hn.2 i)
  exact hm'.symm.trans hn'

theorem iUnion_nodalRoundingCell (k : ℕ) (x : Vec d) :
    (⋃ m : Fin d → ℤ, nodalRoundingCell k m x) = Ico 0 1 := by
  ext t
  constructor
  · intro ht
    obtain ⟨m, hm⟩ := mem_iUnion.mp ht
    exact hm.1
  · intro ht
    apply mem_iUnion.mpr
    refine ⟨fun i => ⌊x i / seedScale k - 1 / 2 + t⌋, ht, fun i => ?_⟩
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

theorem tsum_seedHat (k : ℕ) (x : Vec d) :
    ∑' m : Fin d → ℤ, seedHat k m x = 1 := by
  have hv : ∑' m : Fin d → ℤ, volume (nodalRoundingCell k m x) = 1 := by
    rw [← measure_iUnion (pairwise_disjoint_nodalRoundingCell k x)
      (fun m => measurableSet_nodalRoundingCell k m x), iUnion_nodalRoundingCell]
    simp only [Real.volume_Ico, sub_zero, ENNReal.ofReal_one]
  have hfinite (m : Fin d → ℤ) : volume (nodalRoundingCell k m x) ≠ ⊤ := by
    rw [nodalRoundingCell_eq_Ico, Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  calc
    ∑' m : Fin d → ℤ, seedHat k m x =
        ∑' m : Fin d → ℤ, (volume (nodalRoundingCell k m x)).toReal :=
      tsum_congr fun m => seedHat_eq_rounding_volume k m x
    _ = (∑' m : Fin d → ℤ, volume (nodalRoundingCell k m x)).toReal :=
      (ENNReal.tsum_toReal_eq hfinite).symm
    _ = 1 := by rw [hv, ENNReal.toReal_one]

end

end CoarseDeGiorgi.Whitney

