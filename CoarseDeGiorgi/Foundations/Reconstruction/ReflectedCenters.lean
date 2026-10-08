module

public import CoarseDeGiorgi.Foundations.Reconstruction.ReflectedCells
public import Homogenization.Geometry.CubeMetric

/-! # The reflected parent-center field and its geometric displacement bound -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- The center of a reflected cell is the inverse image of its exact triadic center. -/
def reflectedCenter (m : ℤ) (z : Fin d → ℤ) (s : Fin d → Bool)
    (R : TriadicCube d) : Vec d := (reflectionChart m z s).symm (cubeCenter R)

/-- Reflection charts preserve sup-distances. -/
theorem norm_reflectionChart_sub (m : ℤ) (z : Fin d → ℤ) (s : Fin d → Bool)
    (x y : Vec d) :
    ‖reflectionChart m z s x - reflectionChart m z s y‖ = ‖x - y‖ := by
  change ‖(signLinear s x + _) - (signLinear s y + _)‖ = _
  rw [add_sub_add_right_eq_sub, ← map_sub, norm_signLinear]

/-- Every point of a reflected cell lies within half its side of its center. -/
theorem norm_sub_reflectedCenter_le (m : ℤ) (z : Fin d → ℤ) (s : Fin d → Bool)
    (R : TriadicCube d) {y : Vec d} (hy : y ∈ reflectedCell m z s R) :
    ‖y - reflectedCenter m z s R‖ ≤ cubeRadius R := by
  rw [← norm_reflectionChart_sub m z s, reflectedCenter,
    Homeomorph.apply_symm_apply]
  have ht := cubeSet_subset_closedBall R (openCubeSet_subset_cubeSet R hy)
  simpa only [Metric.mem_closedBall, dist_eq_norm] using ht

/-- At relative depth `j`, every reflected cell has side `auxSide (m+j)`. -/
theorem cubeRadius_reflected_depth {m : ℤ} {j : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (1 - m)) j) :
    cubeRadius R = auxSide (m + j) / 2 := by
  rw [cubeRadius, cubeScaleFactor, scale_eq_sub_of_mem_descendantsAtDepth hR]
  change (1 / 2 : ℝ) * (3 : ℝ) ^ ((1 - m) - j) = _
  rw [show (1 - m) - (j : ℤ) = 1 - (m + j) by omega]
  unfold auxSide
  ring

/-- All reflected descendants at one depth, indexed by orthant and triadic cell. -/
def reflectedCellIndices (m : ℤ) (j : ℕ) : Finset ((Fin d → Bool) × TriadicCube d) :=
  Finset.univ ×ˢ descendantsAtDepth (originCube d (1 - m)) j

/-- Distinct cells have disjoint interiors, also across the reflection planes. -/
theorem disjoint_reflectedCellIndices {m : ℤ} {z : Fin d → ℤ} {j : ℕ}
    {p q : (Fin d → Bool) × TriadicCube d}
    (hp : p ∈ reflectedCellIndices m j) (hq : q ∈ reflectedCellIndices m j) (hpq : p ≠ q) :
    Disjoint (reflectedCell m z p.1 p.2) (reflectedCell m z q.1 q.2) := by
  have hpR := (Finset.mem_product.mp hp).2
  have hqR := (Finset.mem_product.mp hq).2
  by_cases hs : p.1 = q.1
  · have hR : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hs h)
    rw [← hs]
    exact disjoint_reflectedCell_of_mem_descendantsAtDepth m z p.1 hpR hqR hR
  · apply Disjoint.mono
      (reflectedCell_subset_of_mem_descendantsAtDepth m z p.1 hpR)
      (reflectedCell_subset_of_mem_descendantsAtDepth m z q.1 hqR)
    rw [reflectedCell_root_eq_orthant, reflectedCell_root_eq_orthant]
    exact pairwise_disjoint_reflectionOrthant m hs

/-- A globally defined parent center: on internal faces and outside the box it equals the input. -/
def reflectedParentCenter (m : ℤ) (z : Fin d → ℤ) (j : ℕ) (y : Vec d) : Vec d :=
  y + ∑ p ∈ reflectedCellIndices m j,
    (reflectedCell m z p.1 p.2).indicator (fun y => reflectedCenter m z p.1 p.2 - y) y

theorem measurable_reflectedParentCenter (m : ℤ) (z : Fin d → ℤ) (j : ℕ) :
    Measurable (reflectedParentCenter m z j) := by
  apply measurable_id.add
  apply Finset.measurable_sum
  intro p _
  exact (measurable_const.sub measurable_id).indicator
    ((isOpen_openCubeSet p.2).measurableSet.preimage (reflectionChart m z p.1).measurable)

/-- On each cell the parent center field is precisely its fixed center. -/
theorem reflectedParentCenter_eq_of_mem {m : ℤ} {z : Fin d → ℤ} {j : ℕ}
    {p : (Fin d → Bool) × TriadicCube d} (hp : p ∈ reflectedCellIndices m j)
    {y : Vec d} (hy : y ∈ reflectedCell m z p.1 p.2) :
    reflectedParentCenter m z j y = reflectedCenter m z p.1 p.2 := by
  classical
  unfold reflectedParentCenter
  rw [Finset.sum_eq_single p]
  · rw [Set.indicator_of_mem hy]
    abel
  · intro q hq hqp
    exact Set.indicator_of_notMem
      (fun hyq => Set.disjoint_left.mp (disjoint_reflectedCellIndices hp hq hqp.symm) hy hyq) _
  · intro hn
    exact False.elim (hn hp)

/-- The displacement bound holds everywhere, including faces and outside the box. -/
theorem norm_sub_reflectedParentCenter_le (m : ℤ) (z : Fin d → ℤ) (j : ℕ) (y : Vec d) :
    ‖y - reflectedParentCenter m z j y‖ ≤ auxSide (m + j) / 2 := by
  classical
  by_cases h : ∃ p ∈ reflectedCellIndices (d := d) m j, y ∈ reflectedCell m z p.1 p.2
  · obtain ⟨p, hp, hy⟩ := h
    rw [reflectedParentCenter_eq_of_mem hp hy]
    exact (norm_sub_reflectedCenter_le m z p.1 p.2 hy).trans_eq
      (cubeRadius_reflected_depth (Finset.mem_product.mp hp).2)
  · have heq : reflectedParentCenter m z j y = y := by
      unfold reflectedParentCenter
      rw [Finset.sum_eq_zero (fun p hp => Set.indicator_of_notMem (fun hy => h ⟨p, hp, hy⟩) _), add_zero]
    rw [heq, sub_self, norm_zero]
    exact (div_pos (auxSide_pos _) (by norm_num)).le

end

end CoarseDeGiorgi.Foundations.Reconstruction
