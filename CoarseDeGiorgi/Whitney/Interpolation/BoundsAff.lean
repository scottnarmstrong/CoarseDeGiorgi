import CoarseDeGiorgi.Whitney.Interpolation.BoundsHang
import CoarseDeGiorgi.Statements.IsWhitneyInterpolant
import CoarseDeGiorgi.Foundations.Simplex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Affine functions on Whitney simplices: closure, openness, derivative
-/

namespace CoarseDeGiorgi.WhitneyInterp

open Homogenization Set Finset CoarseDeGiorgi

variable {d : ℕ} {τ : ℝ}

theorem isClosed_closedReferenceCube : IsClosed (closedReferenceCube (d := d) τ) := by
  have h : closedReferenceCube (d := d) τ = ⋂ i, {x : Vec d | |x i| ≤ τ / 2} := by
    ext x; simp [closedReferenceCube]
  rw [h]
  exact isClosed_iInter fun i => isClosed_le ((continuous_apply i).abs) continuous_const

theorem simplex_eq_kuhn (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    simplex n π z = Foundations.Simplex.kuhnSimplex n π z := by
  ext x
  rw [mem_simplex_iff]
  simp only [Foundations.Simplex.kuhnSimplex, Foundations.Simplex.simplexCube, mem_ofPred_eq,
    neg_div]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b hab => h2 a b hab⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b hab => h2 hab⟩

theorem isOpen_exteriorCellSet (cell : ExteriorCell d τ) : IsOpen (exteriorCellSet cell) := by
  unfold exteriorCellSet
  rw [simplex_eq_kuhn]
  exact Foundations.Simplex.isOpen_kuhnSimplex _ _ _

theorem aff_closed_of_cont {h : Vec d → ℝ}
    (hc : ContinuousOn h (closedReferenceCube (d := d) τ)ᶜ)
    (ha : ∀ cell : ExteriorCell d τ, ∃ (e : Vec d) (c : ℝ),
      ∀ x ∈ exteriorCellSet cell, h x = vecDot e x + c) : AffClosed τ h := by
  intro cell
  obtain ⟨e, c, he⟩ := ha cell
  refine ⟨e, c, fun x hx => ?_⟩
  have hxext : x ∈ (closedReferenceCube (d := d) τ)ᶜ := by
    refine closedTriadicCube_subset_ext ?_ (closure_cell_subset_cube cell hx)
    have := cell.1.2
    exact this.1
  have hcx : ContinuousAt h x :=
    hc.continuousAt (isClosed_closedReferenceCube.isOpen_compl.mem_nhds hxext)
  have hne : (nhdsWithin x (exteriorCellSet cell)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hx
  have haff : Continuous (fun y : Vec d => vecDot e y + c) := by
    unfold vecDot; fun_prop
  refine tendsto_nhds_unique_of_eventuallyEq (l := nhdsWithin x (exteriorCellSet cell))
    (hcx.tendsto.mono_left nhdsWithin_le_nhds) (haff.tendsto x |>.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with y hy using he y hy

/-- The derivative of a function affine on an open set. -/
theorem smoothGrad_eq_of_affine {g : Vec d → ℝ} {U : Set (Vec d)} (hU : IsOpen U) {e : Vec d}
    {c : ℝ} (he : ∀ y ∈ U, g y = vecDot e y + c) {x : Vec d} (hx : x ∈ U) (i : Fin d) :
    smoothGrad g x i = e i := by
  let L : Vec d →L[ℝ] ℝ := ∑ k, e k • (ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ)
  have hL : ∀ y, L y = vecDot e y := by
    intro y
    simp [L, vecDot]
  have h1 : HasFDerivAt (fun y : Vec d => L y + c) L x := L.hasFDerivAt.add_const c
  have h2 : (fun y : Vec d => L y + c) =ᶠ[nhds x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [hL, he y hy]
  have h3 : HasFDerivAt g L x := h1.congr_of_eventuallyEq h2.symm
  unfold smoothGrad
  rw [h3.fderiv, hL]
  simp [vecDot, basisVec, Pi.single_apply]

end CoarseDeGiorgi.WhitneyInterp
