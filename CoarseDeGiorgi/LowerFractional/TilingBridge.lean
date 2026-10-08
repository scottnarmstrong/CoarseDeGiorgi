module

public import CoarseDeGiorgi.LowerFractional.TilingGrid
public import CoarseDeGiorgi.LowerFractional.AuxTiling

/-! Finite incidence bridge between the actual global simplices and the
auxiliary descendants. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Set Aliases
open scoped BigOperators

noncomputable section

/-- The concrete local family, embedded into the actual global triangulation. -/
def lowerCubeSimplexCells {d : ℕ} (k : ℕ) (c : Fin d → ℤ)
    (hQ : auxCube (k : ℤ) c ⊆ Aliases.originCube 1) : Finset (SimplexIndex d k) :=
  Finset.univ.map (lowerChildEmbedding k c hQ)

lemma lower_cube_simplex_card {d : ℕ} (k : ℕ) (c : Fin d → ℤ)
    (hQ : auxCube (k : ℤ) c ⊆ Aliases.originCube 1) :
    (lowerCubeSimplexCells k c hQ).card = 3 ^ d * d.factorial := by
  rw [lowerCubeSimplexCells, Finset.card_map, Finset.card_univ, lower_child_index_card]

lemma lower_cube_simplex_subset {d : ℕ} (k : ℕ) (c : Fin d → ℤ)
    (hQ : auxCube (k : ℤ) c ⊆ Aliases.originCube 1) :
    ∀ η ∈ lowerCubeSimplexCells k c hQ, simplexCell k η ⊆ auxCube (k : ℤ) c := by
  intro η hη
  obtain ⟨ξ, _, rfl⟩ := Finset.mem_map.mp hη
  rw [lower_child_embedding_cell]
  exact lower_child_cell_subset _ _ _

lemma lower_cube_simplex_pairwiseDisjoint {d : ℕ} (k : ℕ) (c : Fin d → ℤ)
    (hQ : auxCube (k : ℤ) c ⊆ Aliases.originCube 1) :
    (lowerCubeSimplexCells k c hQ : Set (SimplexIndex d k)).PairwiseDisjoint (simplexCell k) := by
  intro η hη ξ hξ hne
  obtain ⟨η', _, rfl⟩ := Finset.mem_map.mp hη
  obtain ⟨ξ', _, rfl⟩ := Finset.mem_map.mp hξ
  change Disjoint (simplexCell k (lowerChildEmbedding k c hQ η'))
    (simplexCell k (lowerChildEmbedding k c hQ ξ'))
  rw [lower_child_embedding_cell, lower_child_embedding_cell]
  exact lower_child_cells_pairwiseDisjoint _ _ (fun h => hne (congrArg _ h))

lemma lower_cube_simplex_ae_cover {d : ℕ} (k : ℕ) (c : Fin d → ℤ)
    (hQ : auxCube (k : ℤ) c ⊆ Aliases.originCube 1) :
    (⋃ η ∈ lowerCubeSimplexCells k c hQ, simplexCell k η) =ᵐ[volume] auxCube (k : ℤ) c := by
  have hs : (⋃ η ∈ lowerCubeSimplexCells k c hQ, simplexCell k η) =
      ⋃ ξ : LowerChildIndex d, lowerChildCell (k : ℤ) c ξ := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨η, hη, hx⟩
      obtain ⟨ξ, _, rfl⟩ := Finset.mem_map.mp hη
      rw [lower_child_embedding_cell] at hx
      exact ⟨ξ, hx⟩
    · rintro ⟨ξ, hx⟩
      refine ⟨lowerChildEmbedding k c hQ ξ, Finset.mem_map.mpr ⟨ξ, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [lower_child_embedding_cell]
      exact hx
  rw [hs]
  exact lower_child_cells_ae_cover _ _

/-- Each auxiliary descendant is tiled by exactly 3^d d! actual global cells.
There is no assumed incidence relation or assumed spatial estimate. -/
theorem lower_descendant_simplex_tiling {d : ℕ} (m : ℤ) (k : ℕ)
    (hmk : m ≤ (k : ℤ)) (z n : Fin d → ℤ)
    (hn : n ∈ auxDescendantIndices m (k : ℤ))
    (hQ : auxCube m z ⊆ Aliases.originCube 1) :
    ∃ s : Finset (SimplexIndex d k),
      s.card = 3 ^ d * d.factorial ∧
      (∀ η ∈ s, simplexCell k η ⊆ auxDescendantCube m (k : ℤ) z n) ∧
      (s : Set (SimplexIndex d k)).PairwiseDisjoint (simplexCell k) ∧
      (⋃ η ∈ s, simplexCell k η) =ᵐ[volume] auxDescendantCube m (k : ℤ) z n := by
  let c := lowerDescendantCenterIndex m (k : ℤ) z n
  have he : auxDescendantCube m (k : ℤ) z n = auxCube (k : ℤ) c :=
    lower_descendant_eq_auxCube m (k : ℤ) hmk z n
  have hD : auxCube (k : ℤ) c ⊆ Aliases.originCube 1 := by
    rw [← he]
    exact (lower_auxDescendant_subset m (k : ℤ) hmk z n hn).trans hQ
  refine ⟨lowerCubeSimplexCells k c hD, lower_cube_simplex_card _ _ _, ?_,
    lower_cube_simplex_pairwiseDisjoint _ _ _, ?_⟩
  · rw [he]
    exact lower_cube_simplex_subset _ _ _
  · rw [he]
    exact lower_cube_simplex_ae_cover _ _ _

/-- Distinct descendants cannot share an actual simplex index. -/
theorem lower_descendant_cell_incidence_disjoint {d : ℕ} (m : ℤ) (k : ℕ)
    (hmk : m ≤ (k : ℤ)) (z : Fin d → ℤ)
    (s : (Fin d → ℤ) → Finset (SimplexIndex d k))
    (hsub : ∀ n ∈ auxDescendantIndices m (k : ℤ),
      ∀ η ∈ s n, simplexCell k η ⊆ auxDescendantCube m (k : ℤ) z n) :
    (auxDescendantIndices (d := d) m (k : ℤ) : Set (Fin d → ℤ)).PairwiseDisjoint s := by
  intro n hn v hv hnv
  apply Finset.disjoint_left.mpr
  intro η hηn hηv
  obtain ⟨x, hx⟩ := simplexCell_nonempty k η
  exact Set.disjoint_left.mp (lower_auxDescendants_pairwiseDisjoint m (k : ℤ) hmk z hn hv hnv)
    (hsub n hn η hηn hx) (hsub v hv η hηv hx)


end

end CoarseDeGiorgi.LowerFractional
