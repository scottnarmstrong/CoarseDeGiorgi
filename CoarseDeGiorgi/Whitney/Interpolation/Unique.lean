import CoarseDeGiorgi.Whitney.Interpolation.Exists

/-! # Uniqueness of the Whitney interpolant

Any interpolant is, on a selected cube, the node interpolant of its own nodal values, and its
values at Whitney vertices are forced: free values are prescribed, hanging values are the
interpolation over the larger mesh. -/

namespace CoarseDeGiorgi.Whitney.Interpolation

open Homogenization MeasureTheory

noncomputable section

open Classical

variable {d : ℕ} {τ : ℝ}

/-- An interpolant is the node interpolant of its nodal values on every selected closed cube. -/
theorem interpolant_formula
    {vals : {z : Vec d // IsFreeVertex τ z} → ℝ} {g : Vec d → ℝ}
    (hg : IsWhitneyInterpolant τ vals g) {D : TriadicCube d} (hD : D ∈ whitneyCubes τ)
    {x : Vec d} (hx : x ∈ closedTriadicCube D) : g x = interpP (D.scale - 1) g x := by
  obtain ⟨cell, hcell, hcl⟩ := exists_cell_of_mem_closedCube hD hx
  subst hcell
  obtain ⟨e, c, hec⟩ := hg.2.2.1 cell
  have hset := exteriorCellSet_eq cell
  rw [hset] at hec hcl
  have hsub : closure (exteriorCellSet cell) ⊆ (closedReferenceCube (d := d) τ)ᶜ := fun y hy hyr =>
    closedCube_disjoint_ref cell.1.property y (closure_exteriorCellSet_subset cell hy) hyr
  rw [hset] at hsub
  exact eq_interpP_on_closure hec (hg.2.1.mono hsub) x hcl

/-- Values of an interpolant at Whitney vertices. -/
theorem interpolant_vertexVal (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {vals : {z : Vec d // IsFreeVertex τ z} → ℝ} {g : Vec d → ℝ}
    (hg : IsWhitneyInterpolant τ vals g) {z : Vec d} (hz : IsWhitneyVertex τ z) :
    g z = vertexVal τ vals z := by
  by_cases hf : IsFreeVertex τ z
  · rw [vertexVal, dite_eq_left hf]
    exact hg.2.2.2 ⟨z, hf⟩
  · obtain ⟨c0, j0, hj0⟩ := hz
    have hv0 := exteriorCellVertex_eq c0 j0
    have hz0 : z ∈ closure (exteriorCellSet c0) := by
      rw [exteriorCellSet_eq, ← hj0, hv0]
      exact nodeN_vertex_mem_closure _ _ _ _
    have hzD0 := closure_exteriorCellSet_subset c0 hz0
    have hnf : ¬ ∀ cell : ExteriorCell d τ, z ∈ closure (exteriorCellSet cell) →
        ∃ j, exteriorCellVertex cell j = z := fun h => hf ⟨⟨c0, j0, hj0⟩, h⟩
    push Not at hnf
    obtain ⟨c1, hz1, hnv⟩ := hnf
    have hzD1 := closure_exteriorCellSet_subset c1 hz1
    have l1 := scale_le_succ_of_touch hτ0 hτ1 c1.1.property c0.1.property hzD1 hzD0
    have hs1 : c1.1.val.scale = c0.1.val.scale + 1 := by
      by_contra hne
      have hle : c1.1.val.scale - 1 ≤ c0.1.val.scale - 1 := by omega
      obtain ⟨m', hm'⟩ := nodeN_nest hle (Classical.choose (show ∃ m, z = nodeN (c0.1.val.scale - 1) m from
        ⟨_, by rw [← hj0, hv0]⟩))
      have hzeq : z = nodeN (c0.1.val.scale - 1)
          (Classical.choose (show ∃ m, z = nodeN (c0.1.val.scale - 1) m from
            ⟨_, by rw [← hj0, hv0]⟩)) :=
        Classical.choose_spec (show ∃ m, z = nodeN (c0.1.val.scale - 1) m from
            ⟨_, by rw [← hj0, hv0]⟩)
      obtain ⟨j, hj⟩ := vertex_of_node_mem_closure (hzeq.trans hm') hz1
      exact hnv j hj
    set D := c0.1.val with hDdef
    set E := c1.1.val with hEdef
    have hD : D ∈ whitneyCubes τ := c0.1.property
    have hE : E ∈ whitneyCubes τ := c1.1.property
    have hs : E.scale = D.scale + 1 := hs1
    rw [vertexVal, dite_eq_right hf, hangVal, selScale_eq hτ0 hτ1 hD hE hs hzD0 hzD1]
    have hform := interpolant_formula hg hE hzD1
    rw [show E.scale - 1 = D.scale by omega] at hform
    rw [hform]
    show ∑' m : Fin d → ℤ, g (nodeN D.scale m) * hatN D.scale m z =
      ∑' m : Fin d → ℤ, valsExt τ vals (nodeN D.scale m) * hatN D.scale m z
    apply tsum_congr
    intro m
    by_cases hm : hatN D.scale m z = 0
    · rw [hm, mul_zero, mul_zero]
    · have hfr := free_of_coarse_support hτ0 hτ1 hD hE hs hzD0 hzD1 hm
      congr 1
      rw [valsExt, dite_eq_left hfr]
      exact hg.2.2.2 ⟨_, hfr⟩

theorem interpolant_unique (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) {g : Vec d → ℝ}
    (hg : IsWhitneyInterpolant τ vals g) : g = whitneyInterp hτ0 hτ1 vals := by
  funext x
  by_cases hx : x ∈ closedReferenceCube (d := d) τ
  · rw [hg.1 x hx, whitneyInterp_of_mem_ref hτ0 hτ1 vals hx]
  · obtain ⟨D, hD, hxD⟩ := (whitney_cubes (d := d) hτ0 hτ1).2.1 x hx
    rw [whitneyInterp_eq hτ0 hτ1 vals hD hxD, interpolant_formula hg hD hxD]
    unfold cubeInterp
    show ∑' m : Fin d → ℤ, g (nodeN (D.scale - 1) m) * hatN (D.scale - 1) m x =
      ∑' m : Fin d → ℤ, vertexVal τ vals (nodeN (D.scale - 1) m) * hatN (D.scale - 1) m x
    apply tsum_congr
    intro m
    by_cases hm : hatN (D.scale - 1) m x = 0
    · rw [hm, mul_zero, mul_zero]
    · have hn := nodeN_mem_closedCube (le_refl _ |>.trans (by omega : D.scale - 1 ≤ D.scale)) hxD hm
      have hw := isWhitneyVertex_of_node hD hn rfl
      rw [interpolant_vertexVal hτ0 hτ1 hg hw]

theorem whitney_interpolation_existsUnique_proof (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) :
    ∃! g : Vec d → ℝ, IsWhitneyInterpolant τ vals g :=
  ⟨whitneyInterp hτ0 hτ1 vals, whitneyInterp_isWhitneyInterpolant hτ0 hτ1 vals,
    fun _ hg => interpolant_unique hτ0 hτ1 vals hg⟩

end

end CoarseDeGiorgi.Whitney.Interpolation
