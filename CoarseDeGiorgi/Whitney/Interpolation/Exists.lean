import CoarseDeGiorgi.Whitney.Interpolation.HangingValues
import CoarseDeGiorgi.Statements.IsWhitneyInterpolant

/-! # Existence of the Whitney interpolant

The interpolant is `0` on the reference cube and, off it, the interpolant of any selected cube
whose closure contains the point; by `cubeInterp_agree` the choice does not matter. -/

namespace CoarseDeGiorgi.Whitney.Interpolation

open Homogenization MeasureTheory

noncomputable section

open Classical

variable {d : ℕ} {τ : ℝ}

/-- The glued interpolant. -/
def whitneyInterp (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) (x : Vec d) : ℝ :=
  if hx : x ∈ closedReferenceCube (d := d) τ then 0
  else cubeInterp τ vals
    (Classical.choose ((whitney_cubes (d := d) hτ0 hτ1).2.1 x hx)) x

theorem whitneyInterp_of_mem_ref (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) {x : Vec d}
    (hx : x ∈ closedReferenceCube (d := d) τ) : whitneyInterp hτ0 hτ1 vals x = 0 := by
  unfold whitneyInterp
  rw [dite_eq_left hx]

theorem whitneyInterp_eq (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes τ) {x : Vec d} (hx : x ∈ closedTriadicCube D) :
    whitneyInterp hτ0 hτ1 vals x = cubeInterp τ vals D x := by
  have hxr := closedCube_disjoint_ref hD x hx
  unfold whitneyInterp
  rw [dite_eq_right hxr]
  obtain ⟨hD', hx'⟩ := Classical.choose_spec ((whitney_cubes (d := d) hτ0 hτ1).2.1 x hxr)
  exact cubeInterp_agree hτ0 hτ1 hD' hD hx' hx vals

theorem isClosed_closedTriadicCube' (D : TriadicCube d) : IsClosed (closedTriadicCube D) :=
  seedParent_isClosed D

theorem isClosed_closedReferenceCube : IsClosed (closedReferenceCube (d := d) τ) := by
  have : closedReferenceCube (d := d) τ = ⋂ i : Fin d, {x : Vec d | |x i| ≤ τ / 2} := by
    ext x; simp [closedReferenceCube]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const

theorem continuousOn_whitneyInterp (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) :
    ContinuousOn (whitneyInterp hτ0 hτ1 vals) (closedReferenceCube (d := d) τ)ᶜ := by
  intro x0 hx0
  apply ContinuousAt.continuousWithinAt
  obtain ⟨_, hcover, hfin, _⟩ := whitney_cubes (d := d) hτ0 hτ1
  have hopen : IsOpen (closedReferenceCube (d := d) τ)ᶜ := isClosed_closedReferenceCube.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x0 hx0
  have hK : IsCompact (Metric.closedBall x0 (ε / 2)) := isCompact_closedBall _ _
  have hKsub : Metric.closedBall x0 (ε / 2) ⊆ (closedReferenceCube (d := d) τ)ᶜ :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hF := hfin _ hK hKsub
  have hcont : ContinuousOn (whitneyInterp hτ0 hτ1 vals)
      (⋃ D : {D : TriadicCube d | D ∈ whitneyCubes τ ∧
        (closedTriadicCube (d := d) D ∩ Metric.closedBall x0 (ε / 2)).Nonempty},
        closedTriadicCube D.1) := by
    have : Finite {D : TriadicCube d | D ∈ whitneyCubes τ ∧
        (closedTriadicCube (d := d) D ∩ Metric.closedBall x0 (ε / 2)).Nonempty} := hF.to_subtype
    apply LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite _)
    · intro D; exact isClosed_closedTriadicCube' D.1
    · intro D
      exact ((continuous_interpP _ _).continuousOn).congr
        (fun x hx => whitneyInterp_eq hτ0 hτ1 vals D.2.1 hx)
  apply hcont.continuousAt
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x0 (by linarith : 0 < ε / 2))
  intro y hy
  have hyr : y ∉ closedReferenceCube (d := d) τ :=
    hKsub (Metric.ball_subset_closedBall hy)
  obtain ⟨D, hD, hyD⟩ := hcover y hyr
  refine Set.mem_iUnion.mpr ⟨⟨D, hD, y, hyD, Metric.ball_subset_closedBall hy⟩, hyD⟩

theorem whitneyInterp_affine (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) (cell : ExteriorCell d τ) :
    ∃ (e : Vec d) (c : ℝ), ∀ x ∈ exteriorCellSet cell,
      whitneyInterp hτ0 hτ1 vals x = vecDot e x + c := by
  obtain ⟨e, c, h⟩ := interpP_affine (cell.1.val.scale - 1) (cellQ cell) cell.2.2 (vertexVal τ vals)
  refine ⟨e, c, fun x hx => ?_⟩
  have hxD : x ∈ closedTriadicCube cell.1.val := closure_exteriorCellSet_subset cell (subset_closure hx)
  rw [whitneyInterp_eq hτ0 hτ1 vals cell.1.property hxD]
  rw [exteriorCellSet_eq] at hx
  exact h x hx

theorem whitneyInterp_free (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) (z : {z : Vec d // IsFreeVertex τ z}) :
    whitneyInterp hτ0 hτ1 vals z.1 = vals z := by
  obtain ⟨cell, j, hj⟩ := z.2.1
  have hv := exteriorCellVertex_eq cell j
  have hmem : z.1 ∈ closedTriadicCube cell.1.val := by
    apply closure_exteriorCellSet_subset cell
    rw [exteriorCellSet_eq, ← hj, hv]
    exact nodeN_vertex_mem_closure _ _ _ _
  rw [whitneyInterp_eq hτ0 hτ1 vals cell.1.property hmem]
  unfold cubeInterp
  rw [← hj, hv, interpP_node]
  unfold vertexVal
  rw [← hv, hj, dite_eq_left z.2]

theorem whitneyInterp_isWhitneyInterpolant (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) :
    IsWhitneyInterpolant τ vals (whitneyInterp hτ0 hτ1 vals) :=
  ⟨fun _ hx => whitneyInterp_of_mem_ref hτ0 hτ1 vals hx,
    continuousOn_whitneyInterp hτ0 hτ1 vals,
    whitneyInterp_affine hτ0 hτ1 vals,
    whitneyInterp_free hτ0 hτ1 vals⟩

end

end CoarseDeGiorgi.Whitney.Interpolation
