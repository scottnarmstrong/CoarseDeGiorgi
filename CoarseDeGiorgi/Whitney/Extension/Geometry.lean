module

public import CoarseDeGiorgi.Whitney.Extension.Basic
public import CoarseDeGiorgi.Whitney.Interpolation.BoundsCells
public import CoarseDeGiorgi.Statements.WhitneySimplicesNear
public import CoarseDeGiorgi.Statements.WhitneyPatch

/-!
# Geometry of free vertices of near Whitney cubes
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

theorem cubeScaleFactor_pos (D : TriadicCube d) : 0 < cubeScaleFactor D := by
  unfold cubeScaleFactor; positivity

/-- Distance of the points of a Whitney cube to the reference cube. -/
theorem gap_bounds (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) {x : Vec d} (hx : x ∈ closedTriadicCube D) :
    2 * cubeScaleFactor D < infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ) ∧
      infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ) ≤ ‖x‖ - τ / 2 ∧
      ‖x‖ - τ / 2 ≤ 9 * cubeScaleFactor D := by
  obtain ⟨h1, h2, h3⟩ := (whitney_cubes hτ0 hτ1).2.2.2 D hD x hx
  have hp := cubeScaleFactor_pos D
  have he := seedPointDistance_eq (d := d) (by linarith only [hτ0]) x
  have hpos : 0 < max 0 (‖x‖ - τ / 2) := by rw [← he]; linarith only [h1, h2, hp]
  have hm : max 0 (‖x‖ - τ / 2) = ‖x‖ - τ / 2 := by
    rcases le_total 0 (‖x‖ - τ / 2) with hh | hh
    · exact max_eq_right hh
    · rw [max_eq_left hh] at hpos; exact absurd hpos (lt_irrefl _)
  rw [he, hm] at h2 h3
  exact ⟨h1, h2, h3⟩

theorem gap_lower (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) {x : Vec d} (hx : x ∈ closedTriadicCube D) :
    2 * cubeScaleFactor D < ‖x‖ - τ / 2 := by
  obtain ⟨h1, h2, _⟩ := gap_bounds hτ0 hτ1 hD hx
  linarith only [h1, h2]

theorem gap_upper (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) {x : Vec d} (hx : x ∈ closedTriadicCube D) :
    ‖x‖ - τ / 2 ≤ 9 * cubeScaleFactor D := (gap_bounds hτ0 hτ1 hD hx).2.2

/-- The sup-diameter of a closed triadic cube. -/
theorem norm_sub_le_of_mem_cube {D : TriadicCube d} {x y : Vec d} (hx : x ∈ closedTriadicCube D)
    (hy : y ∈ closedTriadicCube D) : ‖x - y‖ ≤ cubeScaleFactor D := by
  have hp := cubeScaleFactor_pos D
  apply (pi_norm_le_iff_of_nonneg hp.le).mpr
  intro i
  have h1 := hx i
  have h2 := hy i
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem norm_le_of_mem_ref (hτ : 0 ≤ τ) {q : Vec d} (hq : q ∈ closedReferenceCube (d := d) τ) :
    ‖q‖ ≤ τ / 2 :=
  (pi_norm_le_iff_of_nonneg (div_nonneg hτ (by norm_num))).mpr (fun i => by
    simpa only [Real.norm_eq_abs] using hq i)

theorem zero_mem_ref (hτ : 0 ≤ τ) : (0 : Vec d) ∈ closedReferenceCube (d := d) τ := by
  intro i
  simp only [Pi.zero_apply, abs_zero]
  linarith only [hτ]

/-- If the cube is closer than `h` to the reference cube, one of its points has gap `< h`. -/
theorem exists_point_gap_lt (hτ : 0 ≤ τ) {D : TriadicCube d}
    (hnear : infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ) < h) :
    ∃ p ∈ closedTriadicCube D, ‖p‖ - τ / 2 < h := by
  have hp := cubeScaleFactor_pos D
  have hne : ((fun p : Vec d × Vec d => dist p.1 p.2) ''
      (closedTriadicCube D ×ˢ closedReferenceCube (d := d) τ)).Nonempty :=
    ⟨_, ⟨(triadicCenter D, 0), ⟨fun i => by
      simp only [sub_self, abs_zero]; linarith only [hp], zero_mem_ref hτ⟩, rfl⟩⟩
  obtain ⟨_, ⟨⟨p, q⟩, ⟨hpD, hq⟩, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne hnear
  refine ⟨p, hpD, ?_⟩
  have hqn := norm_le_of_mem_ref hτ hq
  have hn : ‖p‖ ≤ ‖q‖ + ‖p - q‖ := by
    have := norm_add_le q (p - q)
    simpa [add_comm] using this
  simp only at hlt
  rw [dist_eq_norm] at hlt
  linarith only [hn, hqn, hlt]

/-- Points of a near Whitney cube. -/
theorem near_gap (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ)
    (hnear : infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ) < h) :
    2 * cubeScaleFactor D < h ∧ ∀ x ∈ closedTriadicCube D, ‖x‖ - τ / 2 < 3 * h / 2 := by
  have hp := cubeScaleFactor_pos D
  have hx0 : triadicCenter D ∈ closedTriadicCube D := fun i => by
    simp only [sub_self, abs_zero]; linarith only [hp]
  have h2 := (gap_bounds hτ0 hτ1 hD hx0).1
  have hh : 2 * cubeScaleFactor D < h := h2.trans hnear
  refine ⟨hh, fun x hx => ?_⟩
  obtain ⟨p, hpD, hpg⟩ := exists_point_gap_lt (by linarith only [hτ0]) hnear
  have := norm_sub_le_of_mem_cube hx hpD
  have hn : ‖x‖ ≤ ‖p‖ + ‖x - p‖ := by
    have := norm_add_le p (x - p)
    simpa using this
  linarith only [hn, this, hpg, hh]

/-- Points of a far Whitney cube. -/
theorem far_gap (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ)
    (hfar : h ≤ infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ)) :
    ∀ x ∈ closedTriadicCube D, h ≤ ‖x‖ - τ / 2 := fun _x hx =>
  hfar.trans (gap_bounds hτ0 hτ1 hD hx).2.1

end

end CoarseDeGiorgi.WhitneyExt
