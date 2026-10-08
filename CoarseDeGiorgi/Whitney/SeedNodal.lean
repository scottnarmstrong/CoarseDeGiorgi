module

public import CoarseDeGiorgi.Foundations.Simplex.Nested
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Nodal hats for the Whitney seed

The vertex grid of a centered cube of side `s` is the half-shifted grid
`s * (ℤ + 1/2)^d`. The formula below is the continuous Kuhn nodal hat:
one minus the span of the normalized coordinates and zero, truncated at zero.
-/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization

noncomputable section

variable {d : ℕ}

/-- Side length of the level-`k` triangulation. -/
def seedScale (k : ℕ) : ℝ := (3 : ℝ) ^ (-(k : ℤ))

theorem seedScale_pos (k : ℕ) : 0 < seedScale k := zpow_pos (by norm_num) _

theorem three_mul_seedScale_succ (k : ℕ) : 3 * seedScale (k + 1) = seedScale k := by
  have he : -((k + 1 : ℕ) : ℤ) = -(k : ℤ) - 1 := by omega
  simp only [seedScale, he, zpow_sub_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  ring

/-- Vertices, rather than centers, of the centered triadic cubes. -/
def seedNode (k : ℕ) (m : Fin d → ℤ) : Vec d :=
  fun i => seedScale k * ((m i : ℝ) + 1 / 2)

/-- Largest positive coordinate, with zero included even in dimension zero. -/
def positivePeak (x : Vec d) : ℝ := ‖fun i => max (x i) 0‖

theorem positivePeak_nonneg (x : Vec d) : 0 ≤ positivePeak x := norm_nonneg _

@[simp] theorem positivePeak_zero : positivePeak (0 : Vec d) = 0 := by
  simp only [positivePeak, Pi.zero_apply, max_self]
  exact norm_zero

theorem coordinate_le_positivePeak (x : Vec d) (i : Fin d) :
    x i ≤ positivePeak x := by
  calc
    x i ≤ max (x i) 0 := le_max_left _ _
    _ = ‖max (x i) 0‖ := (Real.norm_of_nonneg (le_max_right _ _)).symm
    _ ≤ positivePeak x := norm_le_pi_norm (fun i => max (x i) 0) i

theorem norm_le_positivePeak_add (x : Vec d) :
    ‖x‖ ≤ positivePeak x + positivePeak (-x) := by
  apply (pi_norm_le_iff_of_nonneg (by
    exact add_nonneg (positivePeak_nonneg _) (positivePeak_nonneg _))).mpr
  intro i
  rw [Real.norm_eq_abs, abs_le]
  have hp := coordinate_le_positivePeak x i
  have hn := coordinate_le_positivePeak (-x) i
  simp only [Pi.neg_apply] at hn
  constructor <;> linarith only [hp, hn, positivePeak_nonneg x, positivePeak_nonneg (-x)]

theorem continuous_positivePeak : Continuous (positivePeak : Vec d → ℝ) := by
  exact (continuous_pi fun i => (continuous_apply i).max continuous_const).norm

/-- Continuous Kuhn nodal function at `z`, for a positive mesh size `s`. -/
def nodalHat (s : ℝ) (z x : Vec d) : ℝ :=
  max 0 (1 - (positivePeak (x - z) + positivePeak (z - x)) / s)

theorem nodalHat_nonneg (s : ℝ) (z x : Vec d) : 0 ≤ nodalHat s z x :=
  le_max_left _ _

@[simp] theorem nodalHat_self (s : ℝ) (z : Vec d) : nodalHat s z z = 1 := by
  simp only [nodalHat, sub_self, positivePeak_zero, add_zero, zero_div,
    sub_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

theorem continuous_nodalHat (s : ℝ) (z : Vec d) : Continuous (nodalHat s z) := by
  exact continuous_const.max (continuous_const.sub
    (((continuous_positivePeak.comp (continuous_id.sub continuous_const)).add
      (continuous_positivePeak.comp (continuous_const.sub continuous_id))).div_const s))

theorem norm_sub_lt_of_nodalHat_ne_zero {s : ℝ} (hs : 0 < s)
    {z x : Vec d} (h : nodalHat s z x ≠ 0) : ‖x - z‖ < s := by
  have hp : 0 < 1 - (positivePeak (x - z) + positivePeak (z - x)) / s := by
    by_contra hn
    exact h (max_eq_left (le_of_not_gt hn))
  have hdiv : (positivePeak (x - z) + positivePeak (z - x)) / s < 1 := by
    linarith only [hp]
  have hspan := (div_lt_iff₀ hs).mp hdiv
  have hnorm := norm_le_positivePeak_add (x - z)
  rw [neg_sub] at hnorm
  exact hnorm.trans_lt (by simpa only [one_mul] using hspan)

theorem nodalHat_eq_zero_of_le_norm_sub {s : ℝ} (hs : 0 < s)
    {z x : Vec d} (h : s ≤ ‖x - z‖) : nodalHat s z x = 0 := by
  by_contra hn
  exact (not_lt_of_ge h) (norm_sub_lt_of_nodalHat_ne_zero hs hn)

/-- The hat indexed by the integer coordinates of its vertex. -/
def seedHat (k : ℕ) (m : Fin d → ℤ) : Vec d → ℝ :=
  nodalHat (seedScale k) (seedNode k m)

theorem seedScale_le_node_dist {k : ℕ} {m n : Fin d → ℤ} (h : m ≠ n) :
    seedScale k ≤ ‖seedNode k m - seedNode k n‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have hint : (1 : ℤ) ≤ |m i - n i| := by
    have hne : m i - n i ≠ 0 := sub_ne_zero.mpr hi
    have hp := abs_pos.mpr hne
    omega
  have hr : (1 : ℝ) ≤ |(m i : ℝ) - n i| := by exact_mod_cast hint
  have hcoord : (seedNode k m - seedNode k n) i =
      seedScale k * ((m i : ℝ) - n i) := by
    simp only [seedNode, Pi.sub_apply]
    ring
  calc
    seedScale k = seedScale k * 1 := (mul_one _).symm
    _ ≤ seedScale k * |(m i : ℝ) - n i| := mul_le_mul_of_nonneg_left hr (seedScale_pos k).le
    _ = ‖(seedNode k m - seedNode k n) i‖ := by
      rw [hcoord, Real.norm_eq_abs, abs_mul, abs_of_pos (seedScale_pos k)]
    _ ≤ ‖seedNode k m - seedNode k n‖ := norm_le_pi_norm _ i

theorem seedHat_at_node (k : ℕ) (m n : Fin d → ℤ) :
    seedHat k m (seedNode k n) = if m = n then 1 else 0 := by
  classical
  by_cases h : m = n
  · subst n
    simp only [seedHat, nodalHat_self, ite_true]
  · rw [ite_eq_right h]
    exact nodalHat_eq_zero_of_le_norm_sub (seedScale_pos k)
      (seedScale_le_node_dist (Ne.symm h))

theorem finite_seedNodes_in_ball (k : ℕ) (R : ℝ) :
    {m : Fin d → ℤ | ‖seedNode k m‖ ≤ R}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt (R / seedScale k + 1)
  apply (Set.Finite.pi' fun _ : Fin d => Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
  intro m hm i
  have hc : |seedNode k m i| ≤ ‖seedNode k m‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (seedNode k m) i
  have hn : |seedNode k m i| ≤ R := by
    exact hc.trans hm
  rw [seedNode, abs_mul, abs_of_pos (seedScale_pos k)] at hn
  have hq : |(m i : ℝ) + 1 / 2| ≤ R / seedScale k := by
    exact (le_div_iff₀ (seedScale_pos k)).mpr (by simpa only [mul_comm] using hn)
  have htri := abs_sub_le ((m i : ℝ) + 1 / 2) 0 (1 / 2)
  simp only [add_sub_cancel_right, sub_zero, zero_sub, abs_neg,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at htri
  have hbound : |(m i : ℝ)| ≤ (N : ℝ) := by linarith only [htri, hq, hN]
  obtain ⟨hl, hu⟩ := abs_le.mp hbound
  constructor
  · exact_mod_cast hl
  · exact_mod_cast hu

theorem finite_seedHat_support (k : ℕ) (x : Vec d) :
    (Function.support (fun m : Fin d → ℤ => seedHat k m x)).Finite := by
  apply (finite_seedNodes_in_ball k (‖x‖ + seedScale k)).subset
  intro m hm
  have h := norm_sub_lt_of_nodalHat_ne_zero (seedScale_pos k) hm
  rw [norm_sub_rev] at h
  have hh := norm_add_le (seedNode k m - x) x
  rw [sub_add_cancel] at hh
  exact hh.trans (by simpa only [add_comm] using add_le_add_right h.le ‖x‖)

theorem summable_seedWeightedHat (k : ℕ) (x : Vec d) (c : (Fin d → ℤ) → ℝ) :
    Summable (fun m : Fin d → ℤ => c m * seedHat k m x) := by
  apply summable_of_hasFiniteSupport
  apply (finite_seedHat_support k x).subset
  intro m hm
  exact (mul_ne_zero_iff.mp hm).2

end

end CoarseDeGiorgi.Whitney

