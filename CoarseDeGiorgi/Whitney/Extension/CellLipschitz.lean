module

public import CoarseDeGiorgi.Whitney.Extension.Linear

/-!
# Gradient and Lipschitz bounds of `L_h f` on the Whitney cells
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

theorem abs_vecDot_le (G v : Vec d) :
    |vecDot G v| ≤ euclidNorm G * euclidDist v 0 := by
  have hs := sq_vecDot_le_vecNormSq_mul_vecNormSq G v
  have hv : euclidDist v 0 = Real.sqrt (vecNormSq v) := by
    unfold euclidDist; congr 1; simp
  rw [hv]
  unfold euclidNorm
  rw [← Real.sqrt_mul (vecNormSq_nonneg _)]
  apply Real.abs_le_sqrt hs

/-- The gradient bound on a near Whitney cube. -/
theorem grad_bound_near (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (hh : 0 < h)
    (hh1 : h ≤ 1) {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ)
    (hnear : infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ) < h)
    {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hLip : ∀ x ∈ cubeSurface τ, ∀ y ∈ cubeSurface τ, |f x - f y| ≤ K * euclidDist x y)
    (hbd : ∀ᵐ y ∂surfaceMeasure τ, |f y| ≤ B)
    {cell : ExteriorCell d τ} (hc : cell.1.val = D) {x : Vec d} (hx : x ∈ exteriorCellSet cell) :
    euclidNorm (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x) ≤
      C32 d * (2 * B / h + 2 * Real.sqrt (d : ℝ) * K) := by
  have hp := cubeScaleFactor_pos D
  have hl2 := (near_gap hτ0 hτ1 hD hnear).1
  have hl : cubeScaleFactor D < 1 := by linarith only [hl2, hh1]
  have hM : ∀ z z' : {z : Vec d // IsFreeVertex τ z}, z.1 ∈ closedTriadicCube D →
      z'.1 ∈ closedTriadicCube D → |whitneyAffineExtension τ h f hτ0 hτ1 z.1 -
        whitneyAffineExtension τ h f hτ0 hτ1 z'.1| ≤
        2 * cubeScaleFactor D / h * B + K * (2 * Real.sqrt (d : ℝ) * cubeScaleFactor D) := by
    intro z z' hz hz'
    have hI := interp_spec (h := h) hτ0 hτ1 f
    rw [hI.2.2.2 z, hI.2.2.2 z']
    exact freeValue_sub_le_lip hd hτ0 hτ1 hh hD hl hf hK hB hLip hbd hz hz'
  have := ((C32_spec hτ0 hτ1 (interp_spec (h := h) hτ0 hτ1 f)).2 D hD).2 _ hM cell hc x hx
  refine this.trans (le_of_eq ?_)
  field_simp

/-- On the closure of every cell `L_h f` is Lipschitz, with the same constant. -/
theorem closure_cell_lipschitz (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (hh : 0 < h)
    (hh1 : h ≤ 1) {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) {K B : ℝ} (hK : 0 ≤ K)
    (hB : 0 ≤ B)
    (hLip : ∀ x ∈ cubeSurface τ, ∀ y ∈ cubeSurface τ, |f x - f y| ≤ K * euclidDist x y)
    (hbd : ∀ᵐ y ∂surfaceMeasure τ, |f y| ≤ B) (cell : ExteriorCell d τ) {x y : Vec d}
    (hx : x ∈ closure (exteriorCellSet cell)) (hy : y ∈ closure (exteriorCellSet cell)) :
    |whitneyAffineExtension τ h f hτ0 hτ1 x - whitneyAffineExtension τ h f hτ0 hτ1 y| ≤
      C32 d * (2 * B / h + 2 * Real.sqrt (d : ℝ) * K) * euclidDist x y := by
  have hI := interp_spec (h := h) hτ0 hτ1 f
  have hD : cell.1.val ∈ whitneyCubes (d := d) τ := cell.1.2
  have hsub := WhitneyInterp.closure_cell_subset_cube cell
  by_cases hnear : infSupDist (closedTriadicCube cell.1.val) (closedReferenceCube (d := d) τ) < h
  · have hAff := WhitneyInterp.aff_closed_of_cont hI.2.1 hI.2.2.1 cell
    obtain ⟨e, c, he⟩ := hAff
    have hne : (exteriorCellSet cell).Nonempty := closure_nonempty_iff.mp ⟨x, hx⟩
    obtain ⟨x0, hx0⟩ := hne
    have hgrad : smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x0 = e := by
      funext i
      exact WhitneyInterp.smoothGrad_eq_of_affine (WhitneyInterp.isOpen_exteriorCellSet cell)
        (fun y hy => he y (subset_closure hy)) hx0 i
    have hb := grad_bound_near hd hτ0 hτ1 hh hh1 hD hnear hf hK hB hLip hbd rfl hx0
    rw [hgrad] at hb
    rw [he x hx, he y hy]
    have : vecDot e x + c - (vecDot e y + c) = vecDot e (x - y) := by
      simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]; ring
    rw [this]
    refine (abs_vecDot_le e (x - y)).trans ?_
    have hd0 : euclidDist (x - y) 0 = euclidDist x y := by
      unfold euclidDist; congr 1; simp
    rw [hd0]
    exact mul_le_mul_of_nonneg_right hb (euclidDist_nonneg _ _)
  · have hfar : h ≤ infSupDist (closedTriadicCube cell.1.val) (closedReferenceCube (d := d) τ) :=
      not_lt.mp hnear
    rw [ext_eq_zero_of_far hτ0 hτ1 hh f hD hfar (hsub hx),
      ext_eq_zero_of_far hτ0 hτ1 hh f hD hfar (hsub hy), sub_self, abs_zero]
    have h2 : 0 ≤ 2 * B / h + 2 * Real.sqrt (d : ℝ) * K := by positivity
    exact mul_nonneg (mul_nonneg (C32_nonneg d) h2) (euclidDist_nonneg _ _)

end

end CoarseDeGiorgi.WhitneyExt
