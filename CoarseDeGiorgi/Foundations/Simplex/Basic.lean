module

public import Homogenization.Geometry.ConvexDomain
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-!
# Open Kuhn simplices

The plain sets below transcribe `e.simplex.def`. The coordinatewise
bounds are equivalent to the bounds on the first and last ordered coordinates.
-/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Simplex

open Homogenization Set

/-- The open cube of side `3^n`, with arbitrary center `z`. -/
def simplexCube {d : ℕ} (n : ℤ) (z : Vec d) : Set (Vec d) :=
  {x | ∀ i, -(3 : ℝ) ^ n / 2 < x i - z i ∧ x i - z i < (3 : ℝ) ^ n / 2}

/-- The open Kuhn cell with its coordinates ordered by `π`. -/
def kuhnSimplex {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) : Set (Vec d) :=
  {x | x ∈ simplexCube n z ∧ StrictMono (fun i => x (π i) - z (π i))}

theorem kuhnSimplex_subset_cube {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    kuhnSimplex n π z ⊆ simplexCube n z := fun _ hx => hx.1

theorem isOpen_kuhnSimplex {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    IsOpen (kuhnSimplex n π z) := by
  have hcube : IsOpen (simplexCube n z) := by
    have heq : simplexCube n z = ⋂ i, {x : Vec d | -(3 : ℝ) ^ n / 2 < x i - z i ∧
        x i - z i < (3 : ℝ) ^ n / 2} := by ext x; simp only [simplexCube, mem_ofPred_eq, mem_iInter]
    rw [heq]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const ((continuous_apply i).sub continuous_const)).inter
        (isOpen_lt ((continuous_apply i).sub continuous_const) continuous_const)
  have hord : IsOpen {x : Vec d | StrictMono (fun i => x (π i) - z (π i))} := by
    have heq : {x : Vec d | StrictMono (fun i => x (π i) - z (π i))} =
        ⋂ a, ⋂ b, {x | a < b → x (π a) - z (π a) < x (π b) - z (π b)} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter, StrictMono]
    rw [heq]
    refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    by_cases hab : a < b
    · simp only [hab, true_implies]
      apply isOpen_lt <;> fun_prop
    · simp only [hab, false_implies, ofPred_true, isOpen_univ]
  exact hcube.inter hord

theorem convex_kuhnSimplex {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    Convex ℝ (kuhnSimplex n π z) := by
  intro x hx y hy a b ha hb hab
  have hmix (i : Fin d) :
      (a • x + b • y) i - z i = a * (x i - z i) + b * (y i - z i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      a * x i + b * y i - z i = a * (x i - z i) + b * (y i - z i) +
        ((a + b) - 1) * z i := by ring
      _ = _ := by rw [hab]; ring
  have hpos : 0 < a ∨ 0 < b := by
    by_contra h
    push Not at h
    linarith only [h.1, h.2, hab]
  have hlt {u v r s : ℝ} (hu : u < v) (hr : r < s) : a * u + b * r < a * v + b * s := by
    rcases hpos with ha' | hb'
    · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hu ha')
        (mul_le_mul_of_nonneg_left hr.le hb)
    · exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hu.le ha)
        (mul_lt_mul_of_pos_left hr hb')
  constructor
  · intro i
    rw [hmix]
    have hlo := hlt (hx.1 i).1 (hy.1 i).1
    have hhi := hlt (hx.1 i).2 (hy.1 i).2
    constructor <;> nlinarith only [hlo, hhi, hab]
  · intro i j hij
    dsimp only
    rw [hmix, hmix]
    exact hlt (hx.2 hij) (hy.2 hij)

theorem isBoundedDomain_kuhnSimplex {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d))
    (z : Vec d) : IsBoundedDomain (kuhnSimplex n π z) := by
  have hs : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  refine ⟨(3 : ℝ) ^ n / 2 + ‖z‖ + 1, by positivity, ?_⟩
  intro x hx i
  have hxi : |x i - z i| ≤ (3 : ℝ) ^ n / 2 :=
    (abs_le).2 ⟨by simpa only [neg_div] using (hx.1 i).1.le, (hx.1 i).2.le⟩
  have hzi : |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
  calc
    |x i| = |(x i - z i) + z i| := by rw [sub_add_cancel]
    _ ≤ |x i - z i| + |z i| := abs_add_le _ _
    _ ≤ (3 : ℝ) ^ n / 2 + ‖z‖ := add_le_add hxi hzi
    _ ≤ (3 : ℝ) ^ n / 2 + ‖z‖ + 1 := by linarith

theorem nonempty_kuhnSimplex {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d))
    (z : Vec d) : (kuhnSimplex n π z).Nonempty := by
  have hs : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hd : 0 < (d : ℝ) + 1 := by positivity
  let x : Vec d := fun i => z i + (3 : ℝ) ^ n *
    (((π.symm i).val + 1 : ℝ) / ((d : ℝ) + 1) - 1 / 2)
  have hval (i : Fin d) : (i.val : ℝ) + 1 < (d : ℝ) + 1 := by
    exact_mod_cast Nat.add_lt_add_right i.isLt 1
  have hcoord (i : Fin d) : x (π i) - z (π i) = (3 : ℝ) ^ n *
      (((i.val : ℝ) + 1) / ((d : ℝ) + 1) - 1 / 2) := by
    simp only [x, π.symm_apply_apply, add_sub_cancel_left]
  refine ⟨x, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := π.surjective i
    rw [hcoord]
    have hr0 : 0 < ((j.val : ℝ) + 1) / ((d : ℝ) + 1) := by positivity
    have hr1 : ((j.val : ℝ) + 1) / ((d : ℝ) + 1) < 1 :=
      (div_lt_one hd).2 (hval j)
    constructor <;> nlinarith only [hs, hr0, hr1]
  · intro i j hij
    dsimp only
    rw [hcoord, hcoord]
    apply mul_lt_mul_of_pos_left _ hs
    apply sub_lt_sub_right
    have hv : (i.val : ℝ) < j.val := by exact_mod_cast hij
    exact div_lt_div_of_pos_right (by linarith only [hv]) hd

theorem isOpenBoundedConvexDomain_kuhnSimplex {d : ℕ} (n : ℤ)
    (π : Equiv.Perm (Fin d)) (z : Vec d) :
    IsOpenBoundedConvexDomain (kuhnSimplex n π z) :=
  ⟨isOpen_kuhnSimplex n π z, isBoundedDomain_kuhnSimplex n π z,
    convex_kuhnSimplex n π z⟩

end CoarseDeGiorgi.Foundations.Simplex
