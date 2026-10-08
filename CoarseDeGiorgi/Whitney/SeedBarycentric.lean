module

public import CoarseDeGiorgi.Whitney.SeedPartition

/-! # Ordered vertices and barycentric coordinates of the Kuhn hats -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization Set

noncomputable section

variable {d : ℕ}

/-- The integer index of the vertex with its first `t` coordinates lowered. -/
def seedKuhnVertexIndex (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) (t : Fin (d + 1)) : Fin d → ℤ :=
  fun i => if (π.symm i).val < t.val then q i - 1 else q i

/-- Ordered coordinate on the unit cube, obtained from the centered cube. -/
def seedUnitCoordinate (k : ℕ) (q : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (x : Vec d) (i : Fin d) : ℝ :=
  (x (π i) - seedScale k * (q (π i) : ℝ) + seedScale k / 2) / seedScale k

/-- The successive breakpoints of the common rounding threshold. -/
def seedKuhnBreak (k : ℕ) (q : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (x : Vec d) (n : ℕ) : ℝ :=
  if h0 : n = 0 then 0 else
    if hn : n ≤ d then seedUnitCoordinate k q π x ⟨n - 1, by omega⟩ else 1

private theorem positivePeak_le_bound {x : Vec d} {b : ℝ} (hb : 0 ≤ b)
    (hx : ∀ i, x i ≤ b) : positivePeak x ≤ b := by
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  rw [Real.norm_of_nonneg (le_max_right _ _)]
  exact max_le (hx i) hb

theorem seedKuhnVertex_displacement (k : ℕ) (q : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (t : Fin (d + 1)) (x : Vec d) (i : Fin d) :
    x i - seedNode k (seedKuhnVertexIndex q π t) i =
      if (π.symm i).val < t.val then x i - seedScale k * (q i : ℝ) + seedScale k / 2
      else x i - seedScale k * (q i : ℝ) - seedScale k / 2 := by
  unfold seedNode seedKuhnVertexIndex
  split_ifs <;> push_cast <;> ring

theorem seedKuhn_positivePeak {k : ℕ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {x : Vec d} (hx : x ∈ Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
      (fun i => seedScale k * (q i : ℝ))) (t : Fin (d + 1)) :
    positivePeak (x - seedNode k (seedKuhnVertexIndex q π t)) =
      seedScale k * seedKuhnBreak k q π x t.val := by
  have hcube (i : Fin d) : -seedScale k / 2 < x i - seedScale k * (q i : ℝ) ∧
      x i - seedScale k * (q i : ℝ) < seedScale k / 2 := hx.1 i
  by_cases ht : t.val = 0
  · rw [seedKuhnBreak, dite_eq_left ht, mul_zero]
    apply le_antisymm _ (positivePeak_nonneg _)
    apply positivePeak_le_bound le_rfl
    intro i
    rw [Pi.sub_apply, seedKuhnVertex_displacement, ite_eq_right (by omega)]
    linarith only [(hcube i).2]
  · have htd : t.val ≤ d := by have := t.isLt; omega
    let a : Fin d := ⟨t.val - 1, by omega⟩
    have ha : a.val < t.val := by dsimp only [a]; omega
    have hbreak : seedScale k * seedKuhnBreak k q π x t.val =
        x (π a) - seedScale k * (q (π a) : ℝ) + seedScale k / 2 := by
      rw [seedKuhnBreak, dite_eq_right ht, dite_eq_left htd, seedUnitCoordinate]
      exact mul_div_cancel₀ _ (seedScale_pos k).ne'
    rw [hbreak]
    have hp : 0 ≤ x (π a) - seedScale k * (q (π a) : ℝ) + seedScale k / 2 := by
      linarith only [(hcube (π a)).1]
    apply le_antisymm
    · apply positivePeak_le_bound hp
      intro i
      rw [Pi.sub_apply, seedKuhnVertex_displacement]
      split_ifs with hi
      · have hia : π.symm i ≤ a := by change (π.symm i).val ≤ t.val - 1; omega
        have ho := hx.2.monotone hia
        simp only [π.apply_symm_apply] at ho
        linarith only [ho]
      · linarith only [(hcube i).2, hp]
    · have hl := coordinate_le_positivePeak
        (x - seedNode k (seedKuhnVertexIndex q π t)) (π a)
      simpa only [Pi.sub_apply, seedKuhnVertex_displacement, π.symm_apply_apply,
        ite_eq_left ha] using hl

theorem seedKuhn_negativePeak {k : ℕ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {x : Vec d} (hx : x ∈ Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
      (fun i => seedScale k * (q i : ℝ))) (t : Fin (d + 1)) :
    positivePeak (seedNode k (seedKuhnVertexIndex q π t) - x) =
      seedScale k * (1 - seedKuhnBreak k q π x (t.val + 1)) := by
  have hcube (i : Fin d) : -seedScale k / 2 < x i - seedScale k * (q i : ℝ) ∧
      x i - seedScale k * (q i : ℝ) < seedScale k / 2 := hx.1 i
  have hneg (i : Fin d) : (seedNode k (seedKuhnVertexIndex q π t) - x) i =
      -(x i - seedNode k (seedKuhnVertexIndex q π t) i) := by simp only [Pi.sub_apply]; ring
  by_cases ht : t.val = d
  · rw [seedKuhnBreak, dite_eq_right (by omega), dite_eq_right (by omega), sub_self, mul_zero]
    apply le_antisymm _ (positivePeak_nonneg _)
    apply positivePeak_le_bound le_rfl
    intro i
    rw [hneg, seedKuhnVertex_displacement, ite_eq_left (by have := (π.symm i).isLt; omega)]
    linarith only [(hcube i).1]
  · have htd : t.val < d := by have := t.isLt; omega
    let a : Fin d := ⟨t.val, htd⟩
    have hbreak : seedScale k * (1 - seedKuhnBreak k q π x (t.val + 1)) =
        seedScale k / 2 - (x (π a) - seedScale k * (q (π a) : ℝ)) := by
      rw [seedKuhnBreak, dite_eq_right (by omega), dite_eq_left (by omega), seedUnitCoordinate]
      simp only [Nat.add_sub_cancel, a]
      field_simp [(seedScale_pos k).ne']
      ring
    rw [hbreak]
    have hp : 0 ≤ seedScale k / 2 - (x (π a) - seedScale k * (q (π a) : ℝ)) := by
      linarith only [(hcube (π a)).2]
    apply le_antisymm
    · apply positivePeak_le_bound hp
      intro i
      rw [hneg, seedKuhnVertex_displacement]
      split_ifs with hi
      · linarith only [(hcube i).1, hp]
      · have hai : a ≤ π.symm i := by change t.val ≤ (π.symm i).val; omega
        have ho := hx.2.monotone hai
        simp only [π.apply_symm_apply] at ho
        linarith only [ho]
    · have hl := coordinate_le_positivePeak
        (seedNode k (seedKuhnVertexIndex q π t) - x) (π a)
      rw [hneg, seedKuhnVertex_displacement, π.symm_apply_apply, ite_eq_right (by dsimp only [a]; omega)] at hl
      linarith only [hl]

theorem seedUnitCoordinate_bounds {k : ℕ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {x : Vec d} (hx : x ∈ Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
      (fun i => seedScale k * (q i : ℝ))) (i : Fin d) :
    0 < seedUnitCoordinate k q π x i ∧ seedUnitCoordinate k q π x i < 1 := by
  have hi := hx.1 (π i)
  change -seedScale k / 2 < x (π i) - seedScale k * (q (π i) : ℝ) ∧
    x (π i) - seedScale k * (q (π i) : ℝ) < seedScale k / 2 at hi
  unfold seedUnitCoordinate
  constructor
  · apply div_pos _ (seedScale_pos k)
    linarith only [hi.1]
  · apply (div_lt_iff₀ (seedScale_pos k)).mpr
    rw [one_mul]
    linarith only [hi.2]

theorem seedKuhnBreak_step_nonneg {k : ℕ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {x : Vec d} (hx : x ∈ Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
      (fun i => seedScale k * (q i : ℝ))) (t : Fin (d + 1)) :
    0 ≤ seedKuhnBreak k q π x (t.val + 1) - seedKuhnBreak k q π x t.val := by
  by_cases ht : t.val = 0
  · rw [show seedKuhnBreak k q π x t.val = 0 by simp [seedKuhnBreak, ht]]
    rw [seedKuhnBreak, dite_eq_right (by omega)]
    split_ifs with hn
    · exact sub_nonneg.mpr (seedUnitCoordinate_bounds hx _).1.le
    · norm_num
  · have htd : t.val ≤ d := by have := t.isLt; omega
    simp only [seedKuhnBreak, dite_eq_right ht, dite_eq_left htd,
      dite_eq_right (by omega : t.val + 1 ≠ 0)]
    split_ifs with hn
    · apply sub_nonneg.mpr
      unfold seedUnitCoordinate
      apply div_le_div_of_nonneg_right _ (seedScale_pos k).le
      have ho := hx.2.monotone (show (⟨t.val - 1, by omega⟩ : Fin d) ≤
        ⟨t.val + 1 - 1, by omega⟩ from by change t.val - 1 ≤ t.val + 1 - 1; omega)
      linarith only [ho]
    · exact sub_nonneg.mpr (seedUnitCoordinate_bounds hx _).2.le

theorem seedHat_kuhnVertex {k : ℕ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {x : Vec d} (hx : x ∈ Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
      (fun i => seedScale k * (q i : ℝ))) (t : Fin (d + 1)) :
    seedHat k (seedKuhnVertexIndex q π t) x =
      seedKuhnBreak k q π x (t.val + 1) - seedKuhnBreak k q π x t.val := by
  rw [seedHat, nodalHat, seedKuhn_positivePeak hx t, seedKuhn_negativePeak hx t]
  have he : 1 - (seedScale k * seedKuhnBreak k q π x t.val +
      seedScale k * (1 - seedKuhnBreak k q π x (t.val + 1))) / seedScale k =
      seedKuhnBreak k q π x (t.val + 1) - seedKuhnBreak k q π x t.val := by
    field_simp [(seedScale_pos k).ne']
    ring
  rw [he, max_eq_right (seedKuhnBreak_step_nonneg hx t)]

theorem sum_seedHat_kuhnVertex {k : ℕ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {x : Vec d} (hx : x ∈ Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
      (fun i => seedScale k * (q i : ℝ))) :
    ∑ t : Fin (d + 1), seedHat k (seedKuhnVertexIndex q π t) x = 1 := by
  simp only [seedHat_kuhnVertex hx]
  have htel (N : ℕ) : ∑ n ∈ Finset.range N,
      (seedKuhnBreak k q π x (n + 1) - seedKuhnBreak k q π x n) =
      seedKuhnBreak k q π x N - seedKuhnBreak k q π x 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ = ∑ n ∈ Finset.range (d + 1),
        (seedKuhnBreak k q π x (n + 1) - seedKuhnBreak k q π x n) :=
      Fin.sum_univ_eq_sum_range _ (d + 1)
    _ = seedKuhnBreak k q π x (d + 1) - seedKuhnBreak k q π x 0 := htel _
    _ = 1 := by simp [seedKuhnBreak]

theorem seedKuhnVertexIndex_injective (q : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    Function.Injective (seedKuhnVertexIndex q π) := by
  have hne (t u : Fin (d + 1)) (htu : t.val < u.val) :
      seedKuhnVertexIndex q π t ≠ seedKuhnVertexIndex q π u := by
    have htd : t.val < d := by have := u.isLt; omega
    let a : Fin d := ⟨t.val, htd⟩
    intro he
    have hi := congrFun he (π a)
    simp only [seedKuhnVertexIndex, π.symm_apply_apply] at hi
    rw [ite_eq_right (by dsimp only [a]; omega), ite_eq_left (by dsimp only [a]; omega)] at hi
    omega
  intro t u he
  apply Fin.ext
  by_contra hn
  obtain hlt | hgt := lt_or_gt_of_ne hn
  · exact hne t u hlt he
  · exact hne u t hgt he.symm

theorem seedHat_zero_off_kuhnVertices {k : ℕ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {x : Vec d} (hx : x ∈ Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
      (fun i => seedScale k * (q i : ℝ))) {m : Fin d → ℤ}
    (hm : m ∉ Set.range (seedKuhnVertexIndex q π)) : seedHat k m x = 0 := by
  classical
  let s := Finset.univ.image (seedKuhnVertexIndex q π)
  have hm' : m ∉ s := by simpa only [s, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hm
  have hs : ∑ n ∈ s, seedHat k n x = 1 := by
    rw [Finset.sum_image (fun t _ u _ he => seedKuhnVertexIndex_injective q π he)]
    exact sum_seedHat_kuhnVertex hx
  have hsum : Summable (fun n : Fin d → ℤ => seedHat k n x) := by
    simpa only [one_mul] using summable_seedWeightedHat k x (fun _ => 1)
  have hu : (∑ n ∈ insert m s, seedHat k n x) ≤ ∑' n : Fin d → ℤ, seedHat k n x :=
    hsum.sum_le_tsum (insert m s) (fun n _ => nodalHat_nonneg _ _ _)
  rw [Finset.sum_insert hm', hs, tsum_seedHat] at hu
  exact le_antisymm (by linarith only [hu]) (nodalHat_nonneg _ _ _)

theorem seedWeightedHat_kuhnInterpolation {k : ℕ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {x : Vec d} (hx : x ∈ Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
      (fun i => seedScale k * (q i : ℝ))) (c : (Fin d → ℤ) → ℝ) :
    (∑' m : Fin d → ℤ, c m * seedHat k m x) =
      ∑ t : Fin (d + 1), c (seedKuhnVertexIndex q π t) *
        (seedKuhnBreak k q π x (t.val + 1) - seedKuhnBreak k q π x t.val) := by
  classical
  let s := Finset.univ.image (seedKuhnVertexIndex q π)
  have hz : ∀ m ∉ s, c m * seedHat k m x = 0 := by
    intro m hm
    rw [seedHat_zero_off_kuhnVertices hx (by
      simpa only [s, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hm), mul_zero]
  rw [tsum_eq_sum hz, Finset.sum_image (fun t _ u _ he => seedKuhnVertexIndex_injective q π he)]
  simp only [seedHat_kuhnVertex hx]

end

end CoarseDeGiorgi.Whitney

