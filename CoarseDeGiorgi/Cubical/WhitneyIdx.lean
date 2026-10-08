import CoarseDeGiorgi.Cubical.Box
import CoarseDeGiorgi.Cubical.BallShrink
import CoarseDeGiorgi.Cubical.KuhnBall

/-! # Maximal triadic cubes inside an open set (Whitney decomposition)

A cube `box j z` is *good* for `S` if the closed sup-ball of radius `3^{-j}` about its center
lies in `S` (this contains the cube and is the `3·closure` condition up to a harmless constant).
-/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal

variable {d : ℕ}

/-- Center of a triadic box. -/
noncomputable def bc (j : ℕ) (z : Fin d → ℕ) : Vec d := fun i => ((z i : ℝ) + 1 / 2) / 3 ^ j - 1 / 2

def good (S : Set (Vec d)) (j : ℕ) (z : Fin d → ℕ) : Prop :=
  ∀ x : Vec d, (∀ i, |x i - bc j z i| ≤ ((3 : ℝ) ^ j)⁻¹) → x ∈ S

def maxGood (S : Set (Vec d)) (k j : ℕ) (z : Fin d → ℕ) : Prop :=
  k ≤ j ∧ good S j z ∧
    ∀ i, k ≤ i → i < j → ∀ w : Fin d → ℕ, good S i w → ¬ box j z ⊆ box i w

theorem abs_sub_bc_lt {j : ℕ} {z : Fin d → ℕ} {x : Vec d} (hx : x ∈ box j z) (i : Fin d) :
    |x i - bc j z i| < ((3 : ℝ) ^ j)⁻¹ / 2 := by
  have hp : (0 : ℝ) < 3 ^ j := by positivity
  have h := hx i
  rw [abs_lt]
  simp only [bc]
  have e1 : (z i : ℝ) / 3 ^ j + (1 / 2) / 3 ^ j = ((z i : ℝ) + 1 / 2) / 3 ^ j := by ring
  have e2 : ((z i : ℝ) + 1) / 3 ^ j = ((z i : ℝ) + 1 / 2) / 3 ^ j + (1 / 2) / 3 ^ j := by ring
  have e3 : ((3 : ℝ) ^ j)⁻¹ / 2 = (1 / 2) / 3 ^ j := by field_simp
  constructor <;> linarith [h.1, h.2]

theorem box_subset_of_good {S : Set (Vec d)} {j : ℕ} {z : Fin d → ℕ} (h : good S j z) :
    box j z ⊆ S := by
  intro x hx
  apply h
  intro i
  have := abs_sub_bc_lt hx i
  have hp : (0 : ℝ) < ((3 : ℝ) ^ j)⁻¹ := by positivity
  linarith

/-- Distinct maximal cubes are disjoint, and the index is determined by a common point. -/
theorem maxGood_unique {S : Set (Vec d)} {k j j' : ℕ} {z z' : Fin d → ℕ} {x : Vec d}
    (h : maxGood S k j z) (h' : maxGood S k j' z') (hx : x ∈ box j z) (hx' : x ∈ box j' z') :
    j = j' ∧ z = z' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd (box_subset_of_mem hlt.le hx hx') (h'.2.2 j h.1 hlt z h.2.1)
  · subst heq; exact ⟨rfl, eq_of_mem_box hx hx'⟩
  · exact absurd (box_subset_of_mem hgt.le hx' hx) (h.2.2 j' h'.1 hgt z' h'.2.1)

/-- Floor index of a point. -/
noncomputable def zf (j : ℕ) (x : Vec d) : Fin d → ℕ := fun a => ⌊(3 : ℝ) ^ j * (x a + 1 / 2)⌋₊

/-- Grid points: coordinate hyperplanes at triadic multiples. -/
def gridNull (d : ℕ) : Set (Vec d) :=
  ⋃ (i : Fin d) (j : ℕ) (n : ℤ), {x : Vec d | x i = (n : ℝ) / 3 ^ j - 1 / 2}

theorem volume_gridNull : volume (gridNull d) = 0 := by
  unfold gridNull
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun n => ?_
  exact Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) i _

theorem mem_box_zf {j : ℕ} {x : Vec d} (hx : x ∉ gridNull d) (h0 : ∀ a, 0 < x a + 1 / 2) :
    x ∈ box j (zf j x) := by
  intro a
  have hp : (0 : ℝ) < 3 ^ j := by positivity
  have ht0 : 0 ≤ (3 : ℝ) ^ j * (x a + 1 / 2) := by have := h0 a; positivity
  have hne : (⌊(3 : ℝ) ^ j * (x a + 1 / 2)⌋₊ : ℝ) ≠ (3 : ℝ) ^ j * (x a + 1 / 2) := by
    intro h
    apply hx
    simp only [gridNull, Set.mem_iUnion]
    refine ⟨a, j, (⌊(3 : ℝ) ^ j * (x a + 1 / 2)⌋₊ : ℤ), ?_⟩
    simp only [Set.mem_ofPred_eq]
    push_cast
    rw [h]; field_simp; ring
  have hle := Nat.floor_le ht0
  have hlt := Nat.lt_floor_add_one ((3 : ℝ) ^ j * (x a + 1 / 2))
  have hlt' := lt_of_le_of_ne hle hne
  simp only [zf]
  constructor
  · have : (⌊(3 : ℝ) ^ j * (x a + 1 / 2)⌋₊ : ℝ) / 3 ^ j < x a + 1 / 2 := by
      rw [div_lt_iff₀ hp]; linarith
    linarith
  · have : x a + 1 / 2 < ((⌊(3 : ℝ) ^ j * (x a + 1 / 2)⌋₊ : ℝ) + 1) / 3 ^ j := by
      rw [lt_div_iff₀ hp]; linarith
    linarith

/-- Coverage: almost every point of an open set lies in a maximal good cube. -/
theorem exists_maxGood {S : Set (Vec d)} (hS : IsOpen S) (hSO : S ⊆ originCube 1) (k : ℕ)
    {x : Vec d} (hxS : x ∈ S) (hx : x ∉ gridNull d) :
    ∃ j z, (∀ a, z a < 3 ^ j) ∧ maxGood S k j z ∧ x ∈ box j z := by
  classical
  have hxO := hSO hxS
  have h0 : ∀ a, 0 < x a + 1 / 2 := fun a => by linarith [(hxO a).1]
  have h1 : ∀ a, x a + 1 / 2 < 1 := fun a => by linarith [(hxO a).2]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS x hxS
  -- some level where the cube is good
  have hex : ∃ j, k ≤ j ∧ good S j (zf j x) := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
      (show ((1 : ℝ) / 3) < 1 by norm_num)
    refine ⟨max k m, le_max_left _ _, ?_⟩
    intro y hy
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro a
    have hb := mem_box_zf (j := max k m) hx h0
    have h2 := abs_sub_bc_lt hb a
    have h3 := hy a
    have hpow : ((3 : ℝ) ^ (max k m))⁻¹ ≤ (1 / 3) ^ m := by
      rw [← one_div, ← one_div_pow]
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
    rw [Real.dist_eq]
    have : |y a - x a| ≤ |y a - bc (max k m) (zf (max k m) x) a| +
        |bc (max k m) (zf (max k m) x) a - x a| := abs_sub_le _ _ _
    rw [abs_sub_comm (bc _ _ _) (x a)] at this
    linarith
  classical
  let j₀ := Nat.find hex
  have hj₀ : k ≤ j₀ ∧ good S j₀ (zf j₀ x) := Nat.find_spec hex
  refine ⟨j₀, zf j₀ x, fun a => ?_, ⟨hj₀.1, hj₀.2, ?_⟩, mem_box_zf hx h0⟩
  · simp only [zf]
    have hp : (0 : ℝ) < 3 ^ j₀ := by positivity
    have : ⌊(3 : ℝ) ^ j₀ * (x a + 1 / 2)⌋₊ < 3 ^ j₀ := by
      rw [Nat.floor_lt (by have := h0 a; positivity)]
      calc (3 : ℝ) ^ j₀ * (x a + 1 / 2) < 3 ^ j₀ * 1 := mul_lt_mul_of_pos_left (h1 a) hp
        _ = ((3 ^ j₀ : ℕ) : ℝ) := by simp
    exact this
  · intro i hki hij w hw hsub
    have hxi := mem_box_zf (j := i) hx h0
    have hxj := mem_box_zf (j := j₀) hx h0
    have hxw : x ∈ box i w := hsub hxj
    have : w = zf i x := eq_of_mem_box hxw hxi
    subst this
    exact Nat.find_min hex hij ⟨hki, hw⟩

/-- A maximal cube of level `j > k` has a non-good parent cube containing it. -/
theorem maxGood_parent {S : Set (Vec d)} {k j : ℕ} {z : Fin d → ℕ} (hz : ∀ a, z a < 3 ^ j)
    (h : maxGood S k j z) (hkj : k < j) :
    box j z ⊆ box (j - 1) (fun a => z a / 3) ∧ ¬ good S (j - 1) (fun a => z a / 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hsub : box (m + 1) z ⊆ box m (fun a => z a / 3) := by
    intro y hy a
    have hp : (0 : ℝ) < 3 ^ m := by positivity
    have hy' := hy a
    have h3 : (3 : ℝ) ^ (m + 1) = 3 * 3 ^ m := by ring
    rw [h3] at hy'
    have q1 : 3 * (z a / 3) ≤ z a := Nat.mul_div_le _ _
    have q2 : z a < 3 * (z a / 3) + 3 := by omega
    have q1' : (3 : ℝ) * ((z a / 3 : ℕ) : ℝ) ≤ z a := by exact_mod_cast q1
    have q2' : (z a : ℝ) + 1 ≤ 3 * ((z a / 3 : ℕ) : ℝ) + 3 := by exact_mod_cast (by omega : z a + 1 ≤ 3 * (z a / 3) + 3)
    constructor
    · have : ((z a / 3 : ℕ) : ℝ) / 3 ^ m ≤ (z a : ℝ) / (3 * 3 ^ m) := by
        rw [div_le_div_iff₀ hp (by positivity)]; nlinarith
      linarith [hy'.1]
    · have : ((z a : ℝ) + 1) / (3 * 3 ^ m) ≤ (((z a / 3 : ℕ) : ℝ) + 1) / 3 ^ m := by
        rw [div_le_div_iff₀ (by positivity) hp]; nlinarith
      linarith [hy'.2]
  refine ⟨hsub, fun hg => ?_⟩
  exact h.2.2 m (by omega) (by omega) _ hg hsub

end CoarseDeGiorgi.Cubical
