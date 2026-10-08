import CoarseDeGiorgi.Foundations.Triadic.Admissibility
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace CoarseDeGiorgi.Foundations.Triadic

open Homogenization

noncomputable section

variable {d : ℕ}

/-- Infimum of the sup-norm point-to-reference-cube distances over the closed cube. -/
def cubeInfDist (τ : ℝ) (D : TriadicCube d) : ℝ :=
  sInf ((fun x : Vec d => Metric.infDist x (referenceCube τ)) '' closedCube D)

theorem referenceCube_nonempty {τ : ℝ} (hτ : 0 ≤ τ) :
    (referenceCube (d := d) τ).Nonempty := by
  refine ⟨0, fun i => ?_⟩
  simpa only [Pi.zero_apply, abs_zero] using (by linarith : (0 : ℝ) ≤ τ / 2)

theorem cubeInfDist_le (τ : ℝ) (D : TriadicCube d) {x : Vec d}
    (hx : x ∈ closedCube D) : cubeInfDist τ D ≤ Metric.infDist x (referenceCube τ) := by
  apply csInf_le
  · exact ⟨0, by rintro r ⟨y, _, rfl⟩; exact Metric.infDist_nonneg⟩
  · exact ⟨x, hx, rfl⟩

theorem le_cubeInfDist {τ r : ℝ} {D : TriadicCube d}
    (h : ∀ x ∈ closedCube D, r ≤ Metric.infDist x (referenceCube τ)) :
    r ≤ cubeInfDist τ D := by
  apply le_csInf
  · exact ⟨_, ⟨center D, center_mem_closedCube D, rfl⟩⟩
  · rintro s ⟨x, hx, rfl⟩
    exact h x hx

theorem coordinate_gap_le_infDist {τ : ℝ} (hτ : 0 ≤ τ)
    (D : TriadicCube d) (i : Fin d) {x : Vec d} (hx : x ∈ closedCube D) :
    |center D i| - cubeScaleFactor D / 2 - τ / 2 ≤
      Metric.infDist x (referenceCube τ) := by
  apply (Metric.le_infDist (referenceCube_nonempty hτ)).mpr
  intro y hy
  have h1 := abs_sub_le (center D i) (x i) 0
  have h2 := abs_sub_le (x i) (y i) 0
  have hcoord : |x i - y i| ≤ dist x y := by
    simpa only [Real.dist_eq] using dist_le_pi_dist x y i
  rw [sub_zero, sub_zero, abs_sub_comm (center D i)] at h1
  rw [sub_zero, sub_zero] at h2
  linarith only [h1, h2, hx i, hy i, hcoord]

theorem two_scale_lt_cubeInfDist {τ : ℝ} (hτ : 0 ≤ τ)
    {D : TriadicCube d} (hD : Admissible τ D) :
    2 * cubeScaleFactor D < cubeInfDist τ D := by
  obtain ⟨i, hi⟩ := (admissible_iff τ hτ D).mp hD
  have hgap : 2 * cubeScaleFactor D <
      |center D i| - cubeScaleFactor D / 2 - τ / 2 := by linarith only [hi]
  exact hgap.trans_le (le_cubeInfDist fun _ hx => coordinate_gap_le_infDist hτ D i hx)

theorem infDist_le_nine_scale_of_parent_not_admissible {τ : ℝ}
    {D : TriadicCube d} (hparent : ¬Admissible τ (parentCube D))
    {x : Vec d} (hx : x ∈ closedCube D) :
    Metric.infDist x (referenceCube τ) ≤ 9 * cubeScaleFactor D := by
  obtain ⟨y, hyP, hyR⟩ := Set.not_disjoint_iff.mp hparent
  have hxP := closedCube_subset_parent D hx
  apply (Metric.infDist_le_dist_of_mem hyR).trans
  apply (dist_pi_le_iff (by linarith only [scaleFactor_pos D] :
    (0 : ℝ) ≤ 9 * cubeScaleFactor D)).mpr
  intro i
  rw [Real.dist_eq]
  have htri := abs_sub_le (x i) (center (parentCube D) i) (y i)
  have hpy := hyP i
  rw [abs_sub_comm (y i)] at hpy
  have hpx := hxP i
  rw [parent_scaleFactor D] at hpx hpy
  linarith only [htri, hpx, hpy]

/-- The source Whitney distance chain, with the ambient sup-norm metric. -/
theorem distance_chain {τ : ℝ} (hτ : 0 ≤ τ) {D : TriadicCube d}
    (hD : Admissible τ D) (hparent : ¬Admissible τ (parentCube D))
    {x : Vec d} (hx : x ∈ closedCube D) :
    2 * cubeScaleFactor D < cubeInfDist τ D ∧
      cubeInfDist τ D ≤ Metric.infDist x (referenceCube τ) ∧
      Metric.infDist x (referenceCube τ) ≤ 9 * cubeScaleFactor D :=
  ⟨two_scale_lt_cubeInfDist hτ hD, cubeInfDist_le τ D hx,
    infDist_le_nine_scale_of_parent_not_admissible hparent hx⟩

end

end CoarseDeGiorgi.Foundations.Triadic
