import CoarseDeGiorgi.Whitney.Harmonic.Admissible
import CoarseDeGiorgi.Whitney.Harmonic.Glue
import CoarseDeGiorgi.Whitney.Harmonic.Surface

/-! The globally Lipschitz glued extension `Φ_w`, and its correction. -/

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

variable {d : ℕ}

/-- Points of the closed cube outside the open cube lie on the surface. -/
theorem mem_surface_of_mem_closed_not_open {τ : ℝ} (hτ : 0 < τ) {y : Vec d}
    (hB : y ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ)
    (hO : y ∉ CoarseDeGiorgi.originCube (d := d) τ) : y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ := by
  rw [closedRef_eq_closedBall hτ.le] at hB
  rw [Whitney.source_originCube_eq_ball hτ] at hO
  change ‖y‖ = τ / 2
  rw [Metric.mem_closedBall, dist_zero_right] at hB
  rw [Metric.mem_ball, dist_zero_right, not_lt] at hO
  exact le_antisymm hB hO

/-- Surface points lie in the closed cube. -/
theorem surface_subset_closedRef {τ : ℝ} (hτ : 0 < τ) :
    CoarseDeGiorgi.cubeSurface (d := d) τ ⊆ CoarseDeGiorgi.closedReferenceCube (d := d) τ := by
  intro y hy
  rw [closedRef_eq_closedBall hτ.le, Metric.mem_closedBall, dist_zero_right]
  exact (show ‖y‖ = τ / 2 from hy).le

open scoped Classical in
/-- The glued function `Φ_w`: `w` on the closed cube and `F` outside. -/
theorem exists_glued {τ : ℝ} (hτ : 0 < τ) {K₂ : ℝ≥0} {F w f : Vec d → ℝ}
    (hFlip : CoarseDeGiorgi.euclidLipConst (CoarseDeGiorgi.originCube (d := d) τ)ᶜ F < ⊤)
    (hFf : ∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, F y = f y)
    (hw : LipschitzOnWith K₂ w (CoarseDeGiorgi.closedReferenceCube (d := d) τ))
    (hwf : ∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, w y = f y) :
    ∃ K : ℝ≥0, LipschitzWith K
      (fun x => if x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ then w x else F x) := by
  obtain ⟨K₁, hK₁⟩ := lipschitzOn_of_euclidLipConst_lt_top hFlip
  exact ⟨max K₁ K₂, lipschitz_glue hτ hK₁ hw (fun y hyB hyO => by
    have hy := mem_surface_of_mem_closed_not_open hτ hyB hyO
    rw [hwf y hy, hFf y hy])⟩

end CoarseDeGiorgi.Whitney.Harmonic
