import CoarseDeGiorgi.Foundations.Reconstruction.AuxProjection
import CoarseDeGiorgi.LowerFractional.CubeDomain

/-! Exact geometric tiling by the auxiliary descendants. -/

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Set
open scoped BigOperators
open Foundations.Reconstruction

/-- The finite family of open descendants is pairwise disjoint. -/
theorem lower_auxDescendants_pairwiseDisjoint {d : ℕ} (m k : ℤ) (hmk : m ≤ k)
    (z : Fin d → ℤ) :
    (CoarseDeGiorgi.auxDescendantIndices (d := d) m k : Set (Fin d → ℤ)).PairwiseDisjoint
      (CoarseDeGiorgi.auxDescendantCube m k z) := by
  intro n hn v hv hnv
  have hn' := (auxDescendantDescriptor_mem_iff m k hmk n).mpr hn
  have hv' := (auxDescendantDescriptor_mem_iff m k hmk v).mpr hv
  have hne : auxDescendantDescriptor k n ≠ auxDescendantDescriptor k v :=
    fun h => hnv (congrArg TriadicCube.index h)
  have hd := pairwiseDisjoint_descendantsAtDepth (Homogenization.originCube d (1 - m))
    (k - m).toNat hn' hv' hne
  apply Set.disjoint_left.mpr
  intro x hxn hxv
  have hxnc : x - auxCenter m z ∈ openCubeSet (auxDescendantDescriptor k n) := by
    apply (auxDescendantCube_add_mem m k z n (x - auxCenter m z)).mp
    rw [auxDescendantCube_eq_statement, sub_add_cancel]
    exact hxn
  have hxvc : x - auxCenter m z ∈ openCubeSet (auxDescendantDescriptor k v) := by
    apply (auxDescendantCube_add_mem m k z v (x - auxCenter m z)).mp
    rw [auxDescendantCube_eq_statement, sub_add_cancel]
    exact hxv
  exact Set.disjoint_left.mp hd (openCubeSet_subset_cubeSet _ hxnc)
    (openCubeSet_subset_cubeSet _ hxvc)


/-- Every indexed descendant lies in the open auxiliary root. -/
theorem lower_auxDescendant_subset {d : ℕ} (m k : ℤ) (hmk : m ≤ k)
    (z n : Fin d → ℤ) (hn : n ∈ CoarseDeGiorgi.auxDescendantIndices m k) :
    CoarseDeGiorgi.auxDescendantCube m k z n ⊆ CoarseDeGiorgi.auxCube m z := by
  have hn' := (mem_auxDescendantIndices_iff (d := d) m k hmk n).mp hn
  let j := (k - m).toNat
  let h := auxSide k
  have hh : 0 < h := auxSide_pos k
  have hr : auxSide m = h * (3 : ℝ) ^ j := auxSide_eq_mul_pow m k hmk
  have hN : 2 * (offsetRadius j : ℝ) + 1 = (3 : ℝ) ^ j := by
    exact_mod_cast two_mul_offsetRadius_add_one j
  intro x hx i
  have hlo : -(offsetRadius j : ℝ) ≤ (n i : ℝ) := by exact_mod_cast (hn' i).1
  have hhi : (n i : ℝ) ≤ (offsetRadius j : ℝ) := by exact_mod_cast (hn' i).2
  have hl := mul_le_mul_of_nonneg_right hlo hh.le
  have hu := mul_le_mul_of_nonneg_right hhi hh.le
  have hxi := abs_lt.mp (hx i)
  change -(h / 2) < x i - ((z i : ℝ) * (3 : ℝ) ^ (-m) + (n i : ℝ) * h) ∧
    x i - ((z i : ℝ) * (3 : ℝ) ^ (-m) + (n i : ℝ) * h) < h / 2 at hxi
  change |x i - (z i : ℝ) * (3 : ℝ) ^ (-m)| < auxSide m / 2
  rw [hr, ← hN, abs_lt]
  constructor <;> nlinarith only [hxi.1, hxi.2, hl, hu]


end CoarseDeGiorgi.LowerFractional
