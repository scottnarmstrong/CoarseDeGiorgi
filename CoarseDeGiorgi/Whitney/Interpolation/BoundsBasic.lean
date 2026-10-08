import CoarseDeGiorgi.Statements.Simplex
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Kuhn simplices of side `t`: closure, vertices, barycentric coordinates

For `t > 0`, a permutation `π` and a center `z`, the closed Kuhn simplex `closedKuhn t π z`
has the vertices `kv t π z j`, `j = 0, …, d`.  Every point of it is a convex combination of
the vertices, with explicit weights given by consecutive differences of the sorted
normalized coordinates.
-/

namespace CoarseDeGiorgi.WhitneyInterp

open Homogenization Set Finset

variable {d : ℕ}

/-- Vertex `j` of the Kuhn simplex of side `t`, permutation `π`, center `z`. -/
noncomputable def kv (t : ℝ) (π : Equiv.Perm (Fin d)) (z : Vec d) (j : Fin (d + 1)) : Vec d :=
  fun i => z i + t * (if (π.symm i).val < j.val then -(1 / 2 : ℝ) else 1 / 2)

/-- The closed Kuhn simplex of side `t`. -/
def closedKuhn (t : ℝ) (π : Equiv.Perm (Fin d)) (z : Vec d) : Set (Vec d) :=
  {x | (∀ i, -(t / 2) ≤ x i - z i ∧ x i - z i ≤ t / 2) ∧
    ∀ a b : Fin d, a < b → x (π a) - z (π a) ≤ x (π b) - z (π b)}

theorem mem_simplex_iff (n : ℤ) (π : Equiv.Perm (Fin d)) (z x : Vec d) :
    x ∈ simplex n π z ↔
      (∀ i, -((3 : ℝ) ^ n / 2) < x i - z i ∧ x i - z i < (3 : ℝ) ^ n / 2) ∧
        ∀ a b : Fin d, a < b → x (π a) - z (π a) < x (π b) - z (π b) := by
  have ht : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  constructor
  · rintro ⟨y, rfl, h1, h2⟩
    refine ⟨fun i => ?_, fun a b hab => ?_⟩
    · have := h1 i
      simp only [Pi.add_apply, add_sub_cancel_left]
      constructor <;> nlinarith [this.1, this.2]
    · have := h2 a b hab
      simp only [Pi.add_apply, add_sub_cancel_left]
      exact mul_lt_mul_of_pos_left this ht
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (x i - z i) / (3 : ℝ) ^ n, ?_, ?_, ?_⟩
    · funext i
      simp only [Pi.add_apply]
      field_simp
      ring
    · intro i
      have := h1 i
      constructor
      · rw [lt_div_iff₀ ht]; linarith [this.1]
      · rw [div_lt_iff₀ ht]; linarith [this.2]
    · intro a b hab
      exact div_lt_div_of_pos_right (h2 a b hab) ht

theorem kv_mem_closedKuhn (t : ℝ) (ht : 0 ≤ t) (π : Equiv.Perm (Fin d)) (z : Vec d)
    (j : Fin (d + 1)) : kv t π z j ∈ closedKuhn t π z := by
  refine ⟨fun i => ?_, fun a b hab => ?_⟩
  · simp only [kv, add_sub_cancel_left]
    split_ifs <;> constructor <;> linarith
  · simp only [kv, add_sub_cancel_left, Equiv.symm_apply_apply]
    have hab' : a.val < b.val := hab
    split_ifs with h1 h2 h2
    · exact le_refl _
    · nlinarith
    · exfalso; omega
    · exact le_refl _

theorem isClosed_closedKuhn (t : ℝ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    IsClosed (closedKuhn t π z) := by
  have h : closedKuhn t π z =
      (⋂ i, {x : Vec d | -(t / 2) ≤ x i - z i ∧ x i - z i ≤ t / 2}) ∩
        ⋂ a, ⋂ b, {x : Vec d | a < b → x (π a) - z (π a) ≤ x (π b) - z (π b)} := by
    ext x
    simp only [closedKuhn, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [h]
  refine IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun a => isClosed_iInter
    fun b => ?_)
  · exact (isClosed_le continuous_const ((continuous_apply i).sub continuous_const)).inter
      (isClosed_le ((continuous_apply i).sub continuous_const) continuous_const)
  · by_cases hab : a < b
    · simp only [hab, true_implies]
      exact isClosed_le (((continuous_apply _).sub continuous_const))
        (((continuous_apply _).sub continuous_const))
    · simp only [hab, false_implies, ofPred_true, isClosed_univ]

/-- A strictly interior point of the Kuhn simplex. -/
noncomputable def kuhnMid (t : ℝ) (π : Equiv.Perm (Fin d)) (z : Vec d) : Vec d :=
  fun i => z i + t * (((π.symm i).val + 1 : ℝ) / ((d : ℝ) + 1) - 1 / 2)

theorem kuhnMid_mem (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    kuhnMid ((3 : ℝ) ^ n) π z ∈ simplex n π z := by
  have hs : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hd : 0 < (d : ℝ) + 1 := by positivity
  rw [mem_simplex_iff]
  have hval (i : Fin d) : (i.val : ℝ) + 1 < (d : ℝ) + 1 := by
    exact_mod_cast Nat.add_lt_add_right i.isLt 1
  refine ⟨fun i => ?_, fun a b hab => ?_⟩
  · simp only [kuhnMid, add_sub_cancel_left]
    have hr0 : 0 < (((π.symm i).val : ℝ) + 1) / ((d : ℝ) + 1) := by positivity
    have hr1 : (((π.symm i).val : ℝ) + 1) / ((d : ℝ) + 1) < 1 := (div_lt_one hd).2 (hval _)
    constructor <;> nlinarith
  · simp only [kuhnMid, add_sub_cancel_left, Equiv.symm_apply_apply]
    apply mul_lt_mul_of_pos_left _ hs
    apply sub_lt_sub_right
    have hv : (a.val : ℝ) < b.val := by exact_mod_cast hab
    exact div_lt_div_of_pos_right (by linarith) hd

theorem closure_simplex_eq (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    closure (simplex n π z) = closedKuhn ((3 : ℝ) ^ n) π z := by
  have hs : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  apply Set.Subset.antisymm
  · apply closure_minimal _ (isClosed_closedKuhn _ _ _)
    intro x hx
    rw [mem_simplex_iff] at hx
    exact ⟨fun i => ⟨(hx.1 i).1.le, (hx.1 i).2.le⟩, fun a b hab => (hx.2 a b hab).le⟩
  · intro x hx
    set p := kuhnMid ((3 : ℝ) ^ n) π z with hp
    have hpm : p ∈ simplex n π z := kuhnMid_mem n π z
    rw [mem_simplex_iff] at hpm
    let f : ℝ → Vec d := fun ε => x + ε • (p - x)
    have hf : Filter.Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds x) := by
      have hc : Continuous f := by fun_prop
      have := hc.tendsto 0
      simp only [f, zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hf ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    rw [mem_simplex_iff]
    have hmix (i : Fin d) : f ε i - z i = (1 - ε) * (x i - z i) + ε * (p i - z i) := by
      simp only [f, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    have h1ε : 0 < 1 - ε := by linarith [hε.2]
    refine ⟨fun i => ?_, fun a b hab => ?_⟩
    · rw [hmix]
      have h1 := hx.1 i
      have h2 := hpm.1 i
      constructor <;> nlinarith [mul_nonneg h1ε.le (sub_nonneg.2 h1.1),
        mul_pos hε.1 (sub_pos.2 h2.1), mul_nonneg h1ε.le (sub_nonneg.2 h1.2),
        mul_pos hε.1 (sub_pos.2 h2.2)]
    · rw [hmix, hmix]
      have h1 := hx.2 a b hab
      have h2 := hpm.2 a b hab
      nlinarith [mul_nonneg h1ε.le (sub_nonneg.2 h1), mul_pos hε.1 (sub_pos.2 h2)]

end CoarseDeGiorgi.WhitneyInterp
