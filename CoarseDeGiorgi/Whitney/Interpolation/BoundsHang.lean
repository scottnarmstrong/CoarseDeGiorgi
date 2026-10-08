import CoarseDeGiorgi.Whitney.Interpolation.BoundsCellBary

/-!
# Every vertex of a Whitney simplex is free or interpolated from free vertices

For a Whitney vertex `z` in a closed selected cube `D̄`, the value at `z` of every function that is
affine on the closure of each Whitney simplex is a convex combination of its values at free
vertices lying in `D̄`.
-/

namespace CoarseDeGiorgi.WhitneyInterp

open Homogenization Set Finset CoarseDeGiorgi

variable {d : ℕ} {τ : ℝ}

theorem hanging_rep (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {z : Vec d}
    (hz : IsWhitneyVertex τ z) {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ)
    (hzD : z ∈ closedTriadicCube D) :
    ∃ (l : Fin (d + 1) → ℝ) (v : Fin (d + 1) → Vec d), (∀ j, 0 ≤ l j) ∧ ∑ j, l j = 1 ∧
      (∀ j, l j ≠ 0 → IsFreeVertex τ (v j) ∧ v j ∈ closedTriadicCube D) ∧
      ∀ h, AffClosed τ h → h z = ∑ j, l j * h (v j) := by
  classical
  -- the least scale of a selected cube whose closure contains `z`
  obtain ⟨s0, ⟨D0, hD0, hD0s, hzD0⟩, hmin⟩ : ∃ s0 : ℤ,
      (∃ D' ∈ whitneyCubes (d := d) τ, D'.scale = s0 ∧ z ∈ closedTriadicCube D') ∧
        ∀ s : ℤ, (∃ D' ∈ whitneyCubes (d := d) τ, D'.scale = s ∧ z ∈ closedTriadicCube D') →
          s0 ≤ s := by
    refine Int.exists_least_of_bdd ⟨D.scale - 1, ?_⟩ ⟨D.scale, D, hD, rfl, hzD⟩
    rintro s ⟨D', hD', rfl, hzD'⟩
    have := scale_le_succ hτ0 hτ1 hD' hD hzD' hzD
    omega
  have F1 : ∀ D' ∈ whitneyCubes (d := d) τ, z ∈ closedTriadicCube D' →
      s0 ≤ D'.scale ∧ D'.scale ≤ s0 + 1 := by
    intro D' hD' hzD'
    refine ⟨hmin _ ⟨D', hD', rfl, hzD'⟩, ?_⟩
    have := scale_le_succ hτ0 hτ1 hD0 hD' hzD0 hzD'
    omega
  by_cases hE : ∃ E ∈ whitneyCubes (d := d) τ, E.scale = s0 + 1 ∧ z ∈ closedTriadicCube E
  · -- hanging case: interpolate on the simplices of the larger cube
    obtain ⟨E, hEw, hEs, hzE⟩ := hE
    obtain ⟨CE, hCE, hzCE⟩ := exists_cell_of_mem_cube hEw hzE
    obtain ⟨l, h0, h1, h2, h3⟩ := cell_bary CE hzCE
    have hmesh : cellT CE = (3 : ℝ) ^ s0 := by
      unfold cellT; rw [hCE, hEs]; simp
    have hms : CE.1.val.scale - 1 = s0 := by rw [hCE]; omega
    have hcube : ∀ D' ∈ whitneyCubes (d := d) τ, z ∈ closedTriadicCube D' →
        ∀ j, l j ≠ 0 → exteriorCellVertex CE j ∈ closedTriadicCube D' := by
      intro D' hD' hzD' j hj
      exact vertex_mem_cube CE hzCE (h3 j hj) (by rw [hms]; exact (F1 D' hD' hzD').1) hzD'
    refine ⟨l, fun j => exteriorCellVertex CE j, h0, h1, fun j hj => ⟨?_, hcube D hD hzD j hj⟩, h2⟩
    have hv0 := hcube D0 hD0 hzD0 j hj
    have hvE := hcube E hEw hzE j hj
    have hlatv : ∀ i, lat ((3 : ℝ) ^ s0) (exteriorCellVertex CE j i) := by
      intro i; rw [← hmesh]; exact cell_vertex_lat CE j i
    apply isFree_of_lat
    · intro C hC i
      have hvC := closure_cell_subset_cube C hC
      have hCs := C.1.2
      have a1 := scale_le_succ hτ0 hτ1 hD0 hCs hv0 hvC
      have a2 := scale_le_succ hτ0 hτ1 hCs hEw hvC hvE
      unfold cellT
      exact lat_mono (by omega) (hlatv i)
    · obtain ⟨C, -, hC⟩ := exists_cell_of_mem_cube hD0 hv0
      exact ⟨C, hC⟩
  · -- free case
    push Not at hE
    have hsc : ∀ D' ∈ whitneyCubes (d := d) τ, z ∈ closedTriadicCube D' → D'.scale = s0 := by
      intro D' hD' hzD'
      obtain ⟨a, b⟩ := F1 D' hD' hzD'
      by_contra hne
      exact hE D' hD' (by omega) hzD'
    have hfree : IsFreeVertex τ z := by
      obtain ⟨T, j, hT⟩ := hz
      have hzT : z ∈ closure (exteriorCellSet T) := hT ▸ cell_vertex_mem T j
      have hTs := hsc _ T.1.2 (closure_cell_subset_cube T hzT)
      apply isFree_of_lat
      · intro C hC i
        have hCs := hsc _ C.1.2 (closure_cell_subset_cube C hC)
        have := cell_vertex_lat T j i
        rw [hT] at this
        unfold cellT at this ⊢
        rw [hCs, ← hTs]
        exact this
      · exact ⟨T, hzT⟩
    refine ⟨fun j => if j = 0 then 1 else 0, fun _ => z, fun j => ?_, ?_, fun j hj => ?_, ?_⟩
    · show 0 ≤ (if j = 0 then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · simp
    · exact ⟨hfree, hzD⟩
    · intro h _
      simp

end CoarseDeGiorgi.WhitneyInterp
