module

public import CoarseDeGiorgi.LowerFractional.AverageContraction
public import CoarseDeGiorgi.LowerFractional.CompactCover
public import CoarseDeGiorgi.LowerFractional.DescendantHolder

/-! # Same-index fine cubes and simplex averages

The auxiliary projection uses cubes of side `3^(1-k)`. Here the permutation
cells at index `k` tile the finer cube of side `3^(-k)`, retaining the
coefficient index used in `l.lower.averages` and the endpoint reconstruction.
-/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- A cube of side `3^(-k)` in the unit cube's triadic partition. -/
def fineCube {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Set (Vec d) :=
  Foundations.Simplex.simplexCube (-(k : ℤ))
    (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ))

/-- All permutations over one grid point give simplex indices in the triadic partition. -/
def fineSimplexEmbedding {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    Equiv.Perm (Fin d) ↪ SimplexIndex d k where
  toFun π := ⟨(gridOffset k j, π), by
    classical
    exact Finset.mem_image.mpr ⟨(j, π), Finset.mem_univ _, rfl⟩⟩
  inj' := by
    intro π σ h
    exact congrArg (fun η : SimplexIndex d k => η.1.2) h

/-- The `d!` cells contained in a fine cube, with the original index `k`. -/
def fineSimplexCells {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    Finset (SimplexIndex d k) := by
  classical
  exact Finset.univ.map (fineSimplexEmbedding k j)

theorem fine_simplex_cell_eq {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k))
    (π : Equiv.Perm (Fin d)) :
    simplexCell k (fineSimplexEmbedding k j π) =
      Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
        (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) :=
  Moments.simplex_eq_kuhnSimplex _ _ _

theorem fine_simplex_subset {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    ∀ η ∈ fineSimplexCells k j, simplexCell k η ⊆ fineCube k j := by
  classical
  intro η hη
  obtain ⟨π, _, rfl⟩ := Finset.mem_map.mp hη
  rw [fine_simplex_cell_eq]
  exact Foundations.Simplex.kuhnSimplex_subset_cube _ _ _

theorem fine_simplex_pairwiseDisjoint {d : ℕ} (k : ℕ)
    (j : Fin d → Fin (3 ^ k)) :
    (fineSimplexCells k j : Set (SimplexIndex d k)).PairwiseDisjoint (simplexCell k) := by
  classical
  intro η hη ξ hξ hne
  obtain ⟨π, _, rfl⟩ := Finset.mem_map.mp hη
  obtain ⟨σ, _, rfl⟩ := Finset.mem_map.mp hξ
  change Disjoint (simplexCell k (fineSimplexEmbedding k j π))
    (simplexCell k (fineSimplexEmbedding k j σ))
  rw [fine_simplex_cell_eq, fine_simplex_cell_eq]
  exact Foundations.Simplex.pairwise_disjoint_kuhnSimplex _ _
    (fun h => hne (congrArg (fineSimplexEmbedding k j) h))

theorem fine_simplex_ae_cover {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    (⋃ η ∈ fineSimplexCells k j, simplexCell k η) =ᵐ[volume] fineCube k j := by
  classical
  have heq : (⋃ η ∈ fineSimplexCells k j, simplexCell k η) =
      ⋃ π : Equiv.Perm (Fin d), simplexCell k (fineSimplexEmbedding k j π) := by
    ext x
    simp only [fineSimplexCells, Finset.mem_map, Finset.mem_univ, true_and,
      Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨η, ⟨π, rfl⟩, hx⟩
      exact ⟨π, hx⟩
    · rintro ⟨π, hx⟩
      exact ⟨fineSimplexEmbedding k j π, ⟨π, rfl⟩, hx⟩
  rw [heq]
  simp_rw [fine_simplex_cell_eq]
  exact Foundations.Simplex.iUnion_kuhnSimplex_ae_eq_cube _ _

theorem fine_simplex_cells_disjoint {d : ℕ} (k : ℕ)
    {j l : Fin d → Fin (3 ^ k)} (hjl : j ≠ l) :
    Disjoint (fineSimplexCells k j) (fineSimplexCells k l) := by
  classical
  apply Finset.disjoint_left.mpr
  intro η hηj hηl
  obtain ⟨π, _, hπ⟩ := Finset.mem_map.mp hηj
  obtain ⟨σ, _, hσ⟩ := Finset.mem_map.mp hηl
  have hgrid : gridOffset k j = gridOffset k l :=
    congrArg (fun η : SimplexIndex d k => η.1.1) (hπ.trans hσ.symm)
  exact hjl (Moments.gridOffset_injective k hgrid)

theorem fine_cubes_pairwiseDisjoint {d : ℕ} (k : ℕ) :
    Pairwise (fun j l : Fin d → Fin (3 ^ k) => Disjoint (fineCube k j) (fineCube k l)) := by
  intro j l hjl
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hjl
  apply Moments.gridOffset_injective k
  funext i
  change gridOffset k j i = gridOffset k l i
  have hs : 0 < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hxi := hx i
  have hyi := hy i
  change -(3 : ℝ) ^ (-(k : ℤ)) / 2 <
      x i - (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ) ∧
    x i - (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ) <
      (3 : ℝ) ^ (-(k : ℤ)) / 2 at hxi
  change -(3 : ℝ) ^ (-(k : ℤ)) / 2 <
      x i - (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k l i : ℝ) ∧
    x i - (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k l i : ℝ) <
      (3 : ℝ) ^ (-(k : ℤ)) / 2 at hyi
  have hlt : (gridOffset k j i : ℝ) < (gridOffset k l i : ℝ) + 1 := by
    nlinarith only [hxi.1, hyi.2, hs]
  have hgt : (gridOffset k l i : ℝ) < (gridOffset k j i : ℝ) + 1 := by
    nlinarith only [hyi.1, hxi.2, hs]
  have hlt' : gridOffset k j i < gridOffset k l i + 1 := by exact_mod_cast hlt
  have hgt' : gridOffset k l i < gridOffset k j i + 1 := by exact_mod_cast hgt
  omega

/-- Same-index Jensen contraction: no `k+1` coefficient is introduced. -/
theorem fine_cube_mean_rpow_le {d : ℕ} (k : ℕ)
    (j : Fin d → Fin (3 ^ k)) {G : Vec d → Vec d}
    (hG : IntegrableOn G (fineCube k j)) {r : ℝ} (hr : 1 ≤ r) :
    (volume (fineCube k j)).toReal * euclidNorm (volumeAverageVec (fineCube k j) G) ^ r ≤
      ∑ η ∈ fineSimplexCells k j, (volume (simplexCell k η)).toReal *
        euclidNorm (volumeAverageVec (simplexCell k η) G) ^ r := by
  have hv : volume (fineCube k j) = ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℤ) * d)) :=
    Foundations.Simplex.volume_simplexCube _ _
  apply LowerFractional.lower_simplex_tiling_mean_rpow k (fineSimplexCells k j) hG
  · rw [hv]
    exact (ENNReal.ofReal_pos.mpr (zpow_pos (by norm_num) _)).ne'
  · rw [hv]
    exact ENNReal.ofReal_ne_top
  · exact fine_simplex_subset k j
  · exact fine_simplex_pairwiseDisjoint k j
  · exact fine_simplex_ae_cover k j
  · exact hr

/-- The spatial Hölder estimate on the fine partition, with the coefficient at
index `k`, as used in the first step of the proof of `l.dirichlet.reconstruction`. -/
theorem fine_grid_spatial_holder {d : ℕ} [NeZero d] (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : MemH1a a (CoarseDeGiorgi.originCube 1) v G) {q : ℝ} (hq : 1 < q) :
    (∑ j : Fin d → Fin (3 ^ k),
      (volume (fineCube k j)).toReal * euclidNorm (volumeAverageVec (fineCube k j) G) ^
        paramR q) ≤
      lowerCellAverage a ha k q ^ (paramR q / (2 * q)) *
        (weightedEnergy a (CoarseDeGiorgi.originCube 1) G).toReal ^ (paramR q / 2) := by
  classical
  let J : Finset (Fin d → Fin (3 ^ k)) := Finset.univ
  let S := J.biUnion (fineSimplexCells k)
  have hsub : ∀ η ∈ S, simplexCell k η ⊆ CoarseDeGiorgi.originCube 1 :=
    fun η _ => Moments.simplexCell_subset_originCube k η
  have hdisj : (S : Set (SimplexIndex d k)).PairwiseDisjoint (simplexCell k) := by
    intro η hη ξ hξ hne
    obtain ⟨j, _, hηj⟩ := Finset.mem_biUnion.mp hη
    obtain ⟨l, _, hξl⟩ := Finset.mem_biUnion.mp hξ
    by_cases hjl : j = l
    · subst l
      exact fine_simplex_pairwiseDisjoint k j hηj hξl hne
    · exact (fine_cubes_pairwiseDisjoint k hjl).mono
        (fine_simplex_subset k j η hηj) (fine_simplex_subset k l ξ hξl)
  have hW := Weighted.memH1a_memW11 LowerFractional.lower_unitCube_domain
    LowerFractional.lower_unitCube_nonempty ha hv
  have hG : IntegrableOn G (CoarseDeGiorgi.originCube 1) := Integrable.of_eval hW.2.1
  have hGj (j : Fin d → Fin (3 ^ k)) : IntegrableOn G (fineCube k j) := by
    rw [← integrableOn_congr_set_ae (fine_simplex_ae_cover k j)]
    exact hG.mono_set (Set.iUnion₂_subset fun η _ => Moments.simplexCell_subset_originCube k η)
  have hmean := Finset.sum_le_sum (s := J) (fun j _ =>
    fine_cube_mean_rpow_le k j (hGj j) (LowerFractional.lower_paramR_gt_one hq).le)
  have hinc : (J : Set (Fin d → Fin (3 ^ k))).PairwiseDisjoint (fineSimplexCells k) :=
    fun _ _ _ _ hjl => fine_simplex_cells_disjoint k hjl
  rw [← Finset.sum_biUnion hinc] at hmean
  exact hmean.trans (LowerFractional.lower_simplex_spatial_holder k a ha
    LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty
    ha hv S hsub hdisj hq)

end

end CoarseDeGiorgi.Endpoint.Reconstruction
