import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition

/-! Refinement of a unit Kuhn simplex by the triadic simplex partition. -/

open Homogenization MeasureTheory Set
open scoped ENNReal

namespace CoarseDeGiorgi.Endpoint.Rescaling

open Foundations.Simplex

/-- Coordinate order is constant on a lattice Kuhn simplex. -/
theorem lattice_simplex_order {d : ℕ} {s : ℝ} (hs : 0 < s)
    (z : Fin d → ℤ) (π : Equiv.Perm (Fin d)) {x y : Vec d}
    (hx : (∀ i, -s / 2 < x i - s * (z i : ℝ) ∧ x i - s * (z i : ℝ) < s / 2) ∧
      StrictMono (fun i => x (π i) - s * (z (π i) : ℝ)))
    (hy : (∀ i, -s / 2 < y i - s * (z i : ℝ) ∧ y i - s * (z i : ℝ) < s / 2) ∧
      StrictMono (fun i => y (π i) - s * (z (π i) : ℝ)))
    {i j : Fin d} (hij : x i < x j) : y i < y j := by
  have hzij : z i ≤ z j := by
    by_contra h
    have hz : z j + 1 ≤ z i := by omega
    have hzR : (z j : ℝ) + 1 ≤ (z i : ℝ) := by exact_mod_cast hz
    have hlo := (hx.1 i).1
    have hhi := (hx.1 j).2
    have hmul := mul_le_mul_of_nonneg_left hzR hs.le
    nlinarith only [hlo, hhi, hmul, hij]
  rcases lt_or_eq_of_le hzij with hz | hz
  · have hz' : z i + 1 ≤ z j := by omega
    have hzR : (z i : ℝ) + 1 ≤ (z j : ℝ) := by exact_mod_cast hz'
    have hlo := (hy.1 j).1
    have hhi := (hy.1 i).2
    have hmul := mul_le_mul_of_nonneg_left hzR hs.le
    nlinarith only [hlo, hhi, hmul]
  · have horder : π.symm i < π.symm j := hx.2.lt_iff_lt.mp (by
      simpa only [π.apply_symm_apply, hz] using
        sub_lt_sub_right hij (s * (z j : ℝ)))
    have h := hy.2 horder
    simpa only [π.apply_symm_apply, hz, sub_lt_sub_iff_right] using h

/-- A fine simplex meeting a unit simplex lies in that unit simplex. -/
theorem simplexCell_subset_unit_simplex_of_mem {d k : ℕ}
    (π : Equiv.Perm (Fin d)) (η : SimplexIndex d k) {x : Vec d}
    (hx : x ∈ simplexCell k η) (hπ : x ∈ kuhnSimplex 0 π 0) :
    simplexCell k η ⊆ kuhnSimplex 0 π 0 := by
  have hx' := hx
  change x ∈ CoarseDeGiorgi.simplex (-(k : ℤ)) η.1.2
    (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.1.1 i : ℝ)) at hx'
  rw [Moments.simplex_eq_kuhnSimplex] at hx'
  intro y hy
  have hunit := CoarseDeGiorgi.simplexCell_subset_originCube k η hy
  change y ∈ CoarseDeGiorgi.simplex (-(k : ℤ)) η.1.2
    (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.1.1 i : ℝ)) at hy
  rw [Moments.simplex_eq_kuhnSimplex] at hy
  refine ⟨?_, ?_⟩
  · simpa only [simplexCube, mem_ofPred_eq, zpow_zero, Pi.zero_apply, sub_zero,
      CoarseDeGiorgi.originCube, neg_div] using hunit
  · intro i j hij
    have horder : x (π i) < x (π j) := by
      simpa only [Pi.zero_apply, sub_zero] using hπ.2 hij
    have h := lattice_simplex_order (zpow_pos (by norm_num) (-(k : ℤ)))
      η.1.1 η.1.2 hx' hy horder
    simpa only [Pi.zero_apply, sub_zero] using h

/-- The fine simplices contained in a specified unit Kuhn simplex. -/
def RefinementIndex {d : ℕ} (k : ℕ) (π : Equiv.Perm (Fin d)) :=
  {η : SimplexIndex d k // simplexCell k η ⊆ kuhnSimplex 0 π 0}

noncomputable instance {d k : ℕ} {π : Equiv.Perm (Fin d)} :
    Fintype (RefinementIndex k π) := by
  classical
  unfold RefinementIndex
  infer_instance

/-- Fine simplices cover the parent simplex outside a null set. -/
theorem refinement_union_ae {d : ℕ} (k : ℕ) (π : Equiv.Perm (Fin d)) :
    (⋃ η : RefinementIndex k π, simplexCell k η.1) =ᵐ[volume] kuhnSimplex 0 π 0 := by
  filter_upwards [Assembly.ClassicalMomentsImpl.simplexCell_union_ae (d := d) k] with x hx
  apply propext
  constructor
  · intro h
    obtain ⟨η, hη⟩ := mem_iUnion.mp h
    exact η.2 hη
  · intro h
    have hu : x ∈ originCube 1 := by
      simpa only [simplexCube, mem_ofPred_eq, zpow_zero, Pi.zero_apply, sub_zero,
        CoarseDeGiorgi.originCube, neg_div] using h.1
    obtain ⟨η, hη⟩ := mem_iUnion.mp (hx.mpr hu)
    exact mem_iUnion.mpr ⟨⟨η, simplexCell_subset_unit_simplex_of_mem π η hη h⟩, hη⟩

theorem refinement_cover {d : ℕ} (k : ℕ) (π : Equiv.Perm (Fin d)) :
    volume (kuhnSimplex 0 π 0 \ ⋃ η : RefinementIndex k π, simplexCell k η.1) = 0 := by
  have he : ∀ᵐ x ∂volume, x ∉
      kuhnSimplex 0 π 0 \ ⋃ η : RefinementIndex k π, simplexCell k η.1 := by
    filter_upwards [refinement_union_ae (d := d) k π] with x hx
    simp only [mem_sdiff, not_and, not_not]
    exact hx.mpr
  simpa only [not_not, ofPred_mem_eq] using ae_iff.mp he

theorem refinement_pairwise_disjoint {d : ℕ} (k : ℕ) (π : Equiv.Perm (Fin d)) :
    Pairwise (Function.onFun Disjoint (fun η : RefinementIndex k π => simplexCell k η.1)) := by
  intro η τ hne
  exact Assembly.ClassicalMomentsImpl.simplexCell_pairwise_disjoint k
    (fun h => hne (Subtype.ext h))

end CoarseDeGiorgi.Endpoint.Rescaling
