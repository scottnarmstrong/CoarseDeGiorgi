import CoarseDeGiorgi.Whitney.Interpolation.BoundsAff

/-!
# Range and gradient bounds for the Whitney interpolant (Lemma `l.whitney.interpolation`)
-/

namespace CoarseDeGiorgi.WhitneyInterp

open Homogenization Set Finset CoarseDeGiorgi

variable {d : ℕ} {τ : ℝ}

/-- The prescribed values at free vertices lying in `D̄`. -/
def freeVals (τ : ℝ) (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) (D : TriadicCube d) :
    Set ℝ :=
  {r | ∃ z : {z : Vec d // IsFreeVertex τ z}, z.1 ∈ closedTriadicCube D ∧ vals z = r}

theorem vertex_mem_hull (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {vals : {z : Vec d // IsFreeVertex τ z} → ℝ} {g : Vec d → ℝ}
    (hg : IsWhitneyInterpolant τ vals g) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) {w : Vec d} (hw : IsWhitneyVertex τ w)
    (hwD : w ∈ closedTriadicCube D) : g w ∈ convexHull ℝ (freeVals τ vals D) := by
  classical
  have hAg : AffClosed τ g := aff_closed_of_cont hg.2.1 hg.2.2.1
  obtain ⟨l, v, h0, h1, h2, h3⟩ := hanging_rep hτ0 hτ1 hw hD hwD
  rw [h3 g hAg]
  have hmem : ∀ k ∈ (Finset.univ : Finset (Fin (d + 1))).filter (fun k => l k ≠ 0),
      g (v k) ∈ convexHull ℝ (freeVals τ vals D) := by
    intro k hk
    have hk' := (Finset.mem_filter.1 hk).2
    obtain ⟨hfree, hvD⟩ := h2 k hk'
    exact subset_convexHull ℝ _ ⟨⟨v k, hfree⟩, hvD, (hg.2.2.2 ⟨v k, hfree⟩).symm⟩
  have e1 : ∑ k ∈ (Finset.univ : Finset (Fin (d + 1))).filter (fun k => l k ≠ 0), l k * g (v k) =
      ∑ k, l k * g (v k) :=
    Finset.sum_filter_of_ne (fun k _ hk => left_ne_zero_of_mul hk)
  have e2 : ∑ k ∈ (Finset.univ : Finset (Fin (d + 1))).filter (fun k => l k ≠ 0), l k = 1 := by
    rw [Finset.sum_filter_of_ne (fun k _ hk => hk), h1]
  rw [← e1]
  exact (convex_convexHull ℝ _).sum_mem (fun k _ => h0 k) e2 hmem

theorem mem_hull_of_mem_cube (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {vals : {z : Vec d // IsFreeVertex τ z} → ℝ} {g : Vec d → ℝ}
    (hg : IsWhitneyInterpolant τ vals g) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) {x : Vec d} (hx : x ∈ closedTriadicCube D) :
    g x ∈ convexHull ℝ (freeVals τ vals D) := by
  have hAg : AffClosed τ g := aff_closed_of_cont hg.2.1 hg.2.2.1
  obtain ⟨C, hCD, hC⟩ := exists_cell_of_mem_cube hD hx
  obtain ⟨l, h0, h1, h2, h3⟩ := cell_bary C hC
  rw [h2 g hAg]
  refine (convex_convexHull ℝ _).sum_mem (fun k _ => h0 k) h1 (fun k _ => ?_)
  refine vertex_mem_hull hτ0 hτ1 hg hD ⟨C, k, rfl⟩ ?_
  rw [← hCD]
  exact closure_cell_subset_cube C (cell_vertex_mem C k)

theorem exists_bounds_of_hull {T : Set ℝ} {y : ℝ} (hy : y ∈ convexHull ℝ T) :
    (∃ a ∈ T, a ≤ y) ∧ ∃ b ∈ T, y ≤ b := by
  constructor
  · by_contra h
    push Not at h
    have : convexHull ℝ T ⊆ Ioi y := convexHull_min (fun a ha => h a ha) (convex_Ioi y)
    exact lt_irrefl y (show y < y from this hy)
  · by_contra h
    push Not at h
    have : convexHull ℝ T ⊆ Iio y := convexHull_min (fun a ha => h a ha) (convex_Iio y)
    exact lt_irrefl y (show y < y from this hy)

theorem range_bound (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {vals : {z : Vec d // IsFreeVertex τ z} → ℝ} {g : Vec d → ℝ}
    (hg : IsWhitneyInterpolant τ vals g) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) {x : Vec d} (hx : x ∈ closedTriadicCube D) :
    ∃ z z' : {z : Vec d // IsFreeVertex τ z},
      z.1 ∈ closedTriadicCube D ∧ z'.1 ∈ closedTriadicCube D ∧ vals z ≤ g x ∧ g x ≤ vals z' := by
  obtain ⟨⟨a, ⟨z, hz, rfl⟩, ha⟩, ⟨b, ⟨z', hz', rfl⟩, hb⟩⟩ :=
    exists_bounds_of_hull (mem_hull_of_mem_cube hτ0 hτ1 hg hD hx)
  exact ⟨z, z', hz, hz', ha, hb⟩

/-- Differences of `g` on `D̄` are bounded by the differences at the free vertices of `D̄`. -/
theorem diff_le (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {vals : {z : Vec d // IsFreeVertex τ z} → ℝ} {g : Vec d → ℝ}
    (hg : IsWhitneyInterpolant τ vals g) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) {M : ℝ}
    (hM : ∀ z z' : {z : Vec d // IsFreeVertex τ z},
      z.1 ∈ closedTriadicCube D → z'.1 ∈ closedTriadicCube D → |g z.1 - g z'.1| ≤ M)
    {u u' : Vec d} (hu : u ∈ closedTriadicCube D) (hu' : u' ∈ closedTriadicCube D) :
    g u - g u' ≤ M := by
  obtain ⟨z1, z1', h1, h1', a1, b1⟩ := range_bound hτ0 hτ1 hg hD hu
  obtain ⟨z2, z2', h2, h2', a2, b2⟩ := range_bound hτ0 hτ1 hg hD hu'
  have := hM z1' z2 h1' h2
  have e1 := hg.2.2.2 z1'
  have e2 := hg.2.2.2 z2
  have := (abs_le.1 this).2
  linarith

theorem kv_succ_sub (t : ℝ) (π : Equiv.Perm (Fin d)) (z : Vec d) (i : Fin d) (k : Fin d) :
    kv t π z ⟨(π.symm i).val + 1, by have := (π.symm i).isLt; omega⟩ k -
      kv t π z ⟨(π.symm i).val, by have := (π.symm i).isLt; omega⟩ k =
        if k = i then -t else 0 := by
  simp only [kv]
  by_cases hk : k = i
  · subst hk
    simp
    ring
  · have hne : (π.symm k).val ≠ (π.symm i).val := by
      intro h
      exact hk (π.symm.injective (Fin.ext h))
    rw [ite_eq_right hk]
    split_ifs <;> first | (exfalso; omega) | ring

end CoarseDeGiorgi.WhitneyInterp
