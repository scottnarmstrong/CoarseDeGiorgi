import CoarseDeGiorgi.Whitney.Interpolation.BoundsAff

/-!
# Uniqueness of the Whitney interpolant on the exterior

The first assertion of Lemma `l.whitney.interpolation`.
-/

namespace CoarseDeGiorgi.WhitneyInterp

open Homogenization Set Finset CoarseDeGiorgi

variable {d : ℕ} {τ : ℝ}

/-- Two functions affine on each closed Whitney simplex with the same free values agree at
every Whitney vertex. -/
theorem eq_at_vertex (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {vals : {z : Vec d // IsFreeVertex τ z} → ℝ} {g g' : Vec d → ℝ}
    (hg : AffClosed τ g) (hg' : AffClosed τ g')
    (hv : ∀ z : {z : Vec d // IsFreeVertex τ z}, g z.1 = vals z)
    (hv' : ∀ z : {z : Vec d // IsFreeVertex τ z}, g' z.1 = vals z)
    {w : Vec d} (hw : IsWhitneyVertex τ w) : g' w = g w := by
  obtain ⟨T, j, hT⟩ := hw
  have hwT : w ∈ closure (exteriorCellSet T) := hT ▸ cell_vertex_mem T j
  obtain ⟨l, v, h0, h1, h2, h3⟩ :=
    hanging_rep hτ0 hτ1 ⟨T, j, hT⟩ T.1.2 (closure_cell_subset_cube T hwT)
  rw [h3 g hg, h3 g' hg']
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : l k = 0
  · simp [hk]
  · have hfree := (h2 k hk).1
    have e1 := hv ⟨v k, hfree⟩
    have e2 := hv' ⟨v k, hfree⟩
    rw [e2.trans e1.symm]

/-- Uniqueness on the exterior. -/
theorem eqOn_of_interpolant (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {vals : {z : Vec d // IsFreeVertex τ z} → ℝ} {g : Vec d → ℝ}
    (hg : IsWhitneyInterpolant τ vals g) (g' : Vec d → ℝ)
    (hc' : ContinuousOn g' (closedReferenceCube (d := d) τ)ᶜ)
    (ha' : ∀ cell : ExteriorCell d τ, ∃ (e : Vec d) (c : ℝ),
      ∀ x ∈ exteriorCellSet cell, g' x = vecDot e x + c)
    (hv' : ∀ z : {z : Vec d // IsFreeVertex τ z}, g' z.1 = vals z) :
    Set.EqOn g' g (closedReferenceCube (d := d) τ)ᶜ := by
  have hAg : AffClosed τ g := aff_closed_of_cont hg.2.1 hg.2.2.1
  have hAg' : AffClosed τ g' := aff_closed_of_cont hc' ha'
  intro x hx
  obtain ⟨-, h2, -, -⟩ := CoarseDeGiorgi.whitney_cubes (d := d) (τ := τ) hτ0 hτ1
  obtain ⟨D, hD, hxD⟩ := h2 x hx
  obtain ⟨C, -, hC⟩ := exists_cell_of_mem_cube hD hxD
  obtain ⟨l, h0, h1, h2, h3⟩ := cell_bary C hC
  rw [h2 g hAg, h2 g' hAg']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eq_at_vertex hτ0 hτ1 hAg hAg' hg.2.2.2 hv' ⟨C, k, rfl⟩]
end CoarseDeGiorgi.WhitneyInterp
