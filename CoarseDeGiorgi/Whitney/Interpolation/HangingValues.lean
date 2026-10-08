import CoarseDeGiorgi.Whitney.Interpolation.HangingGeom

/-! # Values at free and hanging vertices

`vertexVal` is the prescribed value at a free vertex and, at a hanging vertex `z`, the affine
interpolation of the free values over the face `F_z` of the larger mesh (the mesh `3^s`, `s` the
smallest scale of a selected cube whose closure contains `z`). -/

namespace CoarseDeGiorgi.Whitney.Interpolation

open Homogenization MeasureTheory

noncomputable section

open Classical

variable {d : ℕ} (τ : ℝ) (vals : {z : Vec d // IsFreeVertex τ z} → ℝ)

/-- The prescribed values extended by zero off the free vertices. -/
def valsExt (z : Vec d) : ℝ := if hz : IsFreeVertex τ z then vals ⟨z, hz⟩ else 0

/-- A selected cube of scale `s` has `z` in its closure. -/
def ScaleAt (z : Vec d) (s : ℤ) : Prop :=
  ∃ D : TriadicCube d, D ∈ whitneyCubes τ ∧ D.scale = s ∧ z ∈ closedTriadicCube D

/-- Selected cubes of scales `s` and `s + 1` have `z` in their closures. -/
def HasPair (z : Vec d) : Prop := ∃ s : ℤ, ScaleAt τ z s ∧ ScaleAt τ z (s + 1)

/-- The smaller scale of the (unique) pair of scales, if any. -/
def selScale (z : Vec d) : ℤ :=
  if h : HasPair τ z then Classical.choose h else 0

/-- The interpolated value of the free values at a hanging vertex. -/
def hangVal (z : Vec d) : ℝ := interpP (selScale τ z) (valsExt τ vals) z

/-- The value assigned to a Whitney vertex. -/
def vertexVal (z : Vec d) : ℝ :=
  if hz : IsFreeVertex τ z then vals ⟨z, hz⟩ else hangVal τ vals z

variable {τ}

theorem selScale_eq (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D E : TriadicCube d}
    (hD : D ∈ whitneyCubes τ) (hE : E ∈ whitneyCubes τ) (hs : E.scale = D.scale + 1) {z : Vec d}
    (hzD : z ∈ closedTriadicCube D) (hzE : z ∈ closedTriadicCube E) :
    selScale τ z = D.scale := by
  have hpair : HasPair τ z := ⟨D.scale, ⟨D, hD, rfl, hzD⟩, ⟨E, hE, hs, hzE⟩⟩
  unfold selScale
  rw [dite_eq_left hpair]
  obtain ⟨⟨D1, hD1, hD1s, hzD1⟩, ⟨D2, hD2, hD2s, hzD2⟩⟩ := Classical.choose_spec hpair
  have a1 := scale_le_succ_of_touch hτ0 hτ1 hD2 hD hzD2 hzD
  have a2 := scale_le_succ_of_touch hτ0 hτ1 hE hD1 hzE hzD1
  omega

/-- Vertices of the coarse face are free. -/
theorem free_of_coarse_support (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D E : TriadicCube d}
    (hD : D ∈ whitneyCubes τ) (_hE : E ∈ whitneyCubes τ) (hs : E.scale = D.scale + 1) {z : Vec d}
    (hzD : z ∈ closedTriadicCube D) (hzE : z ∈ closedTriadicCube E) {m : Fin d → ℤ}
    (hm : hatN D.scale m z ≠ 0) : IsFreeVertex τ (nodeN D.scale m) := by
  have wD := nodeN_mem_closedCube (le_refl D.scale) hzD hm
  have wE := nodeN_mem_closedCube (by omega : D.scale ≤ E.scale) hzE hm
  refine ⟨?_, ?_⟩
  · obtain ⟨m', hm'⟩ := nodeN_nest (by omega : D.scale - 1 ≤ D.scale) m
    exact isWhitneyVertex_of_node hD wD hm'
  · intro cell hcl
    have wG := closure_exteriorCellSet_subset cell hcl
    have hG := cell.1.property
    have a1 := scale_le_succ_of_touch hτ0 hτ1 hG hD wG wD
    obtain ⟨m'', hm''⟩ := nodeN_nest (by omega : cell.1.val.scale - 1 ≤ D.scale) m
    exact vertex_of_node_mem_closure hm'' hcl

/-- The value at a fine node of `D` lying in the coarse neighbor `E` is the coarse interpolant. -/
theorem vertexVal_eq_interpP (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D E : TriadicCube d}
    (hD : D ∈ whitneyCubes τ) (hE : E ∈ whitneyCubes τ) (hs : E.scale = D.scale + 1) {v : Vec d}
    (hvD : v ∈ closedTriadicCube D) (hvE : v ∈ closedTriadicCube E) (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) :
    vertexVal τ vals v = interpP D.scale (vertexVal τ vals) v := by
  by_cases hc : ∃ m, v = nodeN D.scale m
  · obtain ⟨m, rfl⟩ := hc
    rw [interpP_node]
  · have hnf : ¬ IsFreeVertex τ v := by
      intro hf
      obtain ⟨cell, hcell, hcl⟩ := exists_cell_of_mem_closedCube hE hvE
      obtain ⟨j, hj⟩ := hf.2 cell hcl
      apply hc
      refine ⟨seedKuhnVertexIndex (cellQ cell) cell.2.2 j, ?_⟩
      rw [← hj, exteriorCellVertex_eq, hcell]
      congr 1
      omega
    unfold vertexVal hangVal
    rw [dite_eq_right hnf, selScale_eq hτ0 hτ1 hD hE hs hvD hvE]
    unfold interpP
    apply tsum_congr
    intro m
    by_cases hm : hatN D.scale m v = 0
    · rw [hm, mul_zero, mul_zero]
    · have hf := free_of_coarse_support hτ0 hτ1 hD hE hs hvD hvE hm
      congr 1
      simp only [valsExt, dite_eq_left hf]

/-- The cube-wise interpolant. -/
def cubeInterp (σ : ℝ) (w : {z : Vec d // IsFreeVertex σ z} → ℝ) (D : TriadicCube d) :
    Vec d → ℝ :=
  interpP (D.scale - 1) (vertexVal σ w)

/-- Interpolants of neighboring selected cubes agree on the intersection of the closures. -/
theorem cubeInterp_agree (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D E : TriadicCube d}
    (hD : D ∈ whitneyCubes τ) (hE : E ∈ whitneyCubes τ) {x : Vec d}
    (hxD : x ∈ closedTriadicCube D) (hxE : x ∈ closedTriadicCube E) (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) :
    cubeInterp τ vals D x = cubeInterp τ vals E x := by
  have main : ∀ {D E : TriadicCube d}, D ∈ whitneyCubes τ → E ∈ whitneyCubes τ →
      E.scale = D.scale + 1 → ∀ {x : Vec d}, x ∈ closedTriadicCube D → x ∈ closedTriadicCube E →
      cubeInterp τ vals D x = cubeInterp τ vals E x := by
    intro D E hD hE hs x hxD hxE
    have h1 : E.scale - 1 = D.scale := by omega
    unfold cubeInterp
    rw [h1, interpP_refine D.scale (vertexVal τ vals) x]
    show ∑' m : Fin d → ℤ, vertexVal τ vals (nodeN (D.scale - 1) m) * hatN (D.scale - 1) m x =
      ∑' m : Fin d → ℤ, interpP D.scale (vertexVal τ vals) (nodeN (D.scale - 1) m) *
        hatN (D.scale - 1) m x
    apply tsum_congr
    intro m
    by_cases hm : hatN (D.scale - 1) m x = 0
    · rw [hm, mul_zero, mul_zero]
    · have hnD := nodeN_mem_closedCube (by omega : D.scale - 1 ≤ D.scale) hxD hm
      have hnE := nodeN_mem_closedCube (by omega : D.scale - 1 ≤ E.scale) hxE hm
      rw [vertexVal_eq_interpP hτ0 hτ1 hD hE hs hnD hnE]
  have l1 := scale_le_succ_of_touch hτ0 hτ1 hD hE hxD hxE
  have l2 := scale_le_succ_of_touch hτ0 hτ1 hE hD hxE hxD
  rcases (by omega : D.scale = E.scale ∨ E.scale = D.scale + 1 ∨ D.scale = E.scale + 1) with h | h | h
  · unfold cubeInterp; rw [h]
  · exact main hD hE h hxD hxE
  · exact (main hE hD h hxE hxD).symm

end

end CoarseDeGiorgi.Whitney.Interpolation
