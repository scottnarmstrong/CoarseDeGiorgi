module

public import Homogenization.Geometry.TriadicPartition
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Triadic

open Homogenization

noncomputable section

variable {d : ℕ}

def center (D : TriadicCube d) : Vec d :=
  fun i => (D.index i : ℝ) * cubeScaleFactor D

def closedCube (D : TriadicCube d) : Set (Vec d) :=
  {x | ∀ i, |x i - center D i| ≤ cubeScaleFactor D / 2}

def fivefoldCube (D : TriadicCube d) : Set (Vec d) :=
  {x | ∀ i, |x i - center D i| ≤ 5 * cubeScaleFactor D / 2}

def referenceCube (τ : ℝ) : Set (Vec d) :=
  {x | ∀ i, |x i| ≤ τ / 2}

def Admissible (τ : ℝ) (D : TriadicCube d) : Prop :=
  Disjoint (fivefoldCube D) (referenceCube τ)

theorem scaleFactor_pos (D : TriadicCube d) : 0 < cubeScaleFactor D := by
  unfold cubeScaleFactor
  positivity

theorem parent_scaleFactor (D : TriadicCube d) :
    cubeScaleFactor (parentCube D) = 3 * cubeScaleFactor D := by
  simp only [cubeScaleFactor, parentCube_scale, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  ring

theorem center_mem_closedCube (D : TriadicCube d) : center D ∈ closedCube D := by
  intro i
  simpa only [sub_self, abs_zero] using le_of_lt (half_pos (scaleFactor_pos D))

theorem endpoint_mem_closedCube (D : TriadicCube d) (positive : Bool) :
    (fun i => center D i + if positive then cubeScaleFactor D / 2
      else -(cubeScaleFactor D / 2)) ∈ closedCube D := by
  intro i
  cases positive <;> simp [abs_of_pos (half_pos (scaleFactor_pos D))]

theorem closedCube_subset_iff (D E : TriadicCube d) :
    closedCube D ⊆ closedCube E ↔
      ∀ i, |center D i - center E i| + cubeScaleFactor D / 2 ≤ cubeScaleFactor E / 2 := by
  constructor
  · intro h i
    have hp := h (endpoint_mem_closedCube D true) i
    have hm := h (endpoint_mem_closedCube D false) i
    simp only [Bool.false_eq_true, ite_false, ite_true] at hp hm
    rw [abs_le] at hp hm
    rw [← le_sub_iff_add_le, abs_le]
    constructor <;> linarith only [hp.1, hp.2, hm.1, hm.2]
  · intro h x hx i
    calc
      |x i - center E i| ≤ |x i - center D i| + |center D i - center E i| :=
        abs_sub_le _ _ _
      _ ≤ cubeScaleFactor E / 2 := by linarith only [hx i, h i]

theorem center_mem_openCubeSet (D : TriadicCube d) :
    center D ∈ Homogenization.openCubeSet D := by
  intro i
  dsimp [center]
  constructor <;> nlinarith only [scaleFactor_pos D]

theorem parent_index_bounds (D : TriadicCube d) (i : Fin d) :
    -1 ≤ D.index i - 3 * (parentCube D).index i ∧
      D.index i - 3 * (parentCube D).index i ≤ 1 := by
  change -1 ≤ D.index i - 3 * ((D.index i + 1) / 3) ∧
    D.index i - 3 * ((D.index i + 1) / 3) ≤ 1
  have hmod0 := Int.emod_nonneg (D.index i + 1) (by decide : (3 : ℤ) ≠ 0)
  have hmod3 := Int.emod_lt_of_pos (D.index i + 1) (by decide : (0 : ℤ) < 3)
  have hdiv := Int.mul_ediv_add_emod (D.index i + 1) 3
  omega

theorem parent_center_le (D : TriadicCube d) (i : Fin d) :
    |center D i - center (parentCube D) i| ≤ cubeScaleFactor D := by
  obtain ⟨hl, hu⟩ := parent_index_bounds D i
  have hl' : (-1 : ℝ) ≤ (D.index i : ℝ) - 3 * ((parentCube D).index i : ℝ) := by
    exact_mod_cast hl
  have hu' : (D.index i : ℝ) - 3 * ((parentCube D).index i : ℝ) ≤ (1 : ℝ) := by
    exact_mod_cast hu
  dsimp [center]
  rw [parent_scaleFactor, abs_le]
  constructor <;> nlinarith only [hl', hu', scaleFactor_pos D]

theorem closedCube_subset_parent (D : TriadicCube d) :
    closedCube D ⊆ closedCube (parentCube D) := by
  rw [closedCube_subset_iff]
  intro i
  rw [parent_scaleFactor]
  linarith only [parent_center_le D i]

def ancestor (D : TriadicCube d) : ℕ → TriadicCube d
  | 0 => D
  | n + 1 => parentCube (ancestor D n)

theorem ancestor_scale (D : TriadicCube d) (n : ℕ) :
    (ancestor D n).scale = D.scale + n := by
  induction n with
  | zero => simp [ancestor]
  | succ n ih => simp [ancestor, ih, Nat.cast_add, add_assoc]

theorem closedCube_subset_ancestor (D : TriadicCube d) (n : ℕ) :
    closedCube D ⊆ closedCube (ancestor D n) := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih => exact ih.trans (closedCube_subset_parent (ancestor D n))

end

end CoarseDeGiorgi.Foundations.Triadic
