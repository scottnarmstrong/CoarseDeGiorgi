import CoarseDeGiorgi.Selection.Sampling
import CoarseDeGiorgi.Statements.CubeSurface
import CoarseDeGiorgi.Foundations.Triadic.Basic
import CoarseDeGiorgi.Foundations.Euclid.Basic
import CoarseDeGiorgi.Foundations.Simplex.Basic
import Mathlib.Topology.Maps.Proper.Basic

namespace CoarseDeGiorgi.Selection

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Nearby-cell incidence, using Euclidean distance and the cube surface `cubeSurface`.
For a compact cell closure this is precisely the distance-to-surface test with threshold `h`:
the distance minimum is attained. The fixed surface is scaled by the positive radius. -/
def radiusIncidence (C : Set (Vec d)) (h : ℝ) : Set ℝ :=
  {τ | τ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ p : C × CoarseDeGiorgi.cubeSurface (d := d) 1,
    Foundations.Euclid.eDist2 p.1 (τ • (p.2 : Vec d)) ≤ h}

theorem isCompact_cubeSurface (τ : ℝ) : IsCompact (CoarseDeGiorgi.cubeSurface (d := d) τ) := by
  have he : CoarseDeGiorgi.cubeSurface (d := d) τ = Metric.sphere 0 (τ / 2) := by
    ext x
    simp only [CoarseDeGiorgi.cubeSurface, mem_ofPred_eq, Metric.mem_sphere, dist_zero_right]
  rw [he]
  exact isCompact_sphere _ _

/-- Compactness makes the radius-incidence test measurable. -/
theorem radiusIncidence_measurable {C : Set (Vec d)} (hC : IsCompact C) (h : ℝ) :
    MeasurableSet (radiusIncidence C h) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have : CompactSpace (CoarseDeGiorgi.cubeSurface (d := d) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_cubeSurface 1)
  let P := C × CoarseDeGiorgi.cubeSurface (d := d) 1
  have hp : Continuous (fun p : ℝ × P =>
      ((p.2.1 : Vec d), p.1 • (p.2.2 : Vec d))) := by dsimp [P]; fun_prop
  have hcont : Continuous (fun p : ℝ × P =>
      Foundations.Euclid.eDist2 p.2.1 (p.1 • (p.2.2 : Vec d))) :=
    Foundations.Euclid.continuous_eDist2.comp hp
  have hclosed : IsClosed {τ : ℝ | ∃ p : P,
      Foundations.Euclid.eDist2 p.1 (τ • (p.2 : Vec d)) ≤ h} := by
    have he : {τ : ℝ | ∃ p : P, Foundations.Euclid.eDist2 p.1 (τ • (p.2 : Vec d)) ≤ h} =
        Prod.fst '' {p : ℝ × P | Foundations.Euclid.eDist2 p.2.1 (p.1 • (p.2.2 : Vec d)) ≤ h} := by
      ext τ
      simp only [mem_ofPred_eq, mem_image]
      constructor
      · rintro ⟨p, hp⟩; exact ⟨(τ, p), hp, rfl⟩
      · rintro ⟨⟨τ', p⟩, hp, rfl⟩; exact ⟨p, hp⟩
    rw [he]
    exact isClosedMap_fst_of_compactSpace _ (isClosed_le hcont continuous_const)
  exact measurableSet_Ioo.inter hclosed.measurableSet

/-- A compact cell in a cube can be sampled only in a short radius interval. -/
theorem radiusIncidence_subset_interval {C : Set (Vec d)} {z : Vec d} {ell h : ℝ}
    (hshape : ∀ x ∈ C, ‖x - z‖ ≤ ell / 2) :
    radiusIncidence C h ⊆ Icc (2 * ‖z‖ - (ell + 2 * h)) (2 * ‖z‖ + (ell + 2 * h)) := by
  rintro τ ⟨hτ, p, hp⟩
  have hτpos : 0 < τ := (by norm_num : (0 : ℝ) < 1 / 2).trans hτ.1
  have hn : ‖τ • (p.2 : Vec d)‖ = τ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτpos]
    rw [p.2.property]
    ring
  have hdist : dist z (τ • (p.2 : Vec d)) ≤ ell / 2 + h := by
    apply (dist_triangle z (p.1 : Vec d) _).trans
    have hx : dist z (p.1 : Vec d) ≤ ell / 2 := by
      rw [dist_comm, dist_eq_norm]
      exact hshape p.1 p.1.property
    exact add_le_add hx ((Foundations.Euclid.dist_le_eDist2 _ _).trans hp)
  have hnorm := abs_norm_sub_norm_le z (τ • (p.2 : Vec d))
  rw [← dist_eq_norm, hn] at hnorm
  have hb := abs_le.mp (hnorm.trans hdist)
  constructor <;> linarith [hb.1, hb.2]


/-- The radius parameterization of the fixed surface equals the source moving-surface test. -/
theorem radiusIncidence_iff (C : Set (Vec d)) (h τ : ℝ) :
    τ ∈ radiusIncidence C h ↔ τ ∈ Ioo (1 / 2 : ℝ) 1 ∧
      ∃ x ∈ C, ∃ y ∈ CoarseDeGiorgi.cubeSurface τ, Foundations.Euclid.eDist2 x y ≤ h := by
  constructor
  · rintro ⟨hτ, p, hp⟩
    refine ⟨hτ, p.1, p.1.property, τ • (p.2 : Vec d), ?_, hp⟩
    change ‖τ • (p.2 : Vec d)‖ = τ / 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hτ.1]), p.2.property]
    ring
  · rintro ⟨hτ, x, hx, y, hy, hxy⟩
    have hτpos : 0 < τ := by linarith [hτ.1]
    have hunit : τ⁻¹ • y ∈ CoarseDeGiorgi.cubeSurface 1 := by
      change ‖τ⁻¹ • y‖ = 1 / 2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτpos), hy]
      field_simp
    refine ⟨hτ, (⟨x, hx⟩, ⟨τ⁻¹ • y, hunit⟩), ?_⟩
    simpa only [smul_inv_smul₀ hτpos.ne'] using hxy





end

end CoarseDeGiorgi.Selection
