module

public import CoarseDeGiorgi.Endpoint.Capacitary.Geometry
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! Essential bounds used on the interior and remote cubes. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Set Metric
open scoped ENNReal

variable {d : ℕ}

/-- Restriction to a smaller domain increases the nonnegative essential infimum. -/
theorem capacitary_essInf_mono {U V : Set (Vec d)} (hUV : U ⊆ V) (u : Vec d → ℝ) :
    nonnegativeEssInf V u ≤ nonnegativeEssInf U u := by
  exact le_essInf_of_ae_le _ (ae_mono (Measure.restrict_mono hUV le_rfl)
    (ae_essInf_le (f := fun x => ENNReal.ofReal (u x)) (μ := volume.restrict V)))

/-- The positive finite normalization supplied by the remote obstacle. -/
noncomputable def capacitaryNormalization (d : ℕ) (η : ℝ) : ℝ≥0∞ :=
  (volume (remoteCube d (1 / 2))) ^ (1 / η)

theorem capacitaryNormalization_pos {η : ℝ} (_hη : 0 < η) :
    0 < capacitaryNormalization d η := by
  unfold capacitaryNormalization
  apply ENNReal.rpow_pos
  · exact (remoteCube_domain (d := d) (by norm_num : (0 : ℝ) < 1 / 2)).isOpen.measure_pos volume (by
      rw [remoteCube_eq_ball (by norm_num : (0 : ℝ) < 1 / 2)]
      exact nonempty_ball.mpr (by norm_num))
  · exact (remoteCube_domain (d := d) (by norm_num : (0 : ℝ) < 1 / 2)).isBoundedDomain.isBounded.measure_lt_top.ne

theorem capacitaryNormalization_ne_top {η : ℝ} (hη : 0 < η) :
    capacitaryNormalization d η ≠ ⊤ := by
  unfold capacitaryNormalization
  exact ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (remoteCube_domain (d := d) (by norm_num : (0 : ℝ) < 1 / 2)).isBoundedDomain.isBounded.measure_lt_top.ne

/-- Value one on the obstacle yields a fixed lower bound on the interior norm. -/
theorem capacitary_obstacle_norm {ψ : Vec d → ℝ} {η : ℝ} (hη : 0 < η)
    (hψQ : ∀ᵐ x ∂volume.restrict (originCube 1), x ∈ remoteCube d (1 / 2) → ψ x = 1) :
    capacitaryNormalization d η ≤
      eLpNorm ψ (ENNReal.ofReal η) (volume.restrict (originCube (15 / 16))) := by
  have hQsub : remoteCube d (1 / 2) ⊆ originCube (15 / 16) := by
    intro x hx
    apply closure_remoteCube_subset_interior
    apply subset_closure
    rw [remoteCube_eq_ball (by norm_num : (0 : ℝ) < 1)]
    rw [remoteCube_eq_ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx
    exact ball_subset_ball (by norm_num) hx
  have hQunit := hQsub.trans (originCube_mono' (by norm_num) one_pos (by norm_num))
  have heq : ψ =ᵐ[volume.restrict (remoteCube d (1 / 2))] (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_mono (Measure.restrict_mono hQunit le_rfl) hψQ,
      ae_restrict_mem (remoteCube_domain (d := d) (by norm_num : (0 : ℝ) < 1 / 2)).isOpen.measurableSet]
      with x hx hxQ
    exact hx hxQ
  have hconst : eLpNorm (fun _ : Vec d => (1 : ℝ)) (ENNReal.ofReal η)
      (volume.restrict (remoteCube d (1 / 2))) = capacitaryNormalization d η := by
    rw [eLpNorm_const' 1 (ENNReal.ofReal_pos.mpr hη).ne' ENNReal.ofReal_ne_top]
    simp only [enorm_one, one_mul, Measure.restrict_apply_univ,
      ENNReal.toReal_ofReal hη.le, capacitaryNormalization]
  rw [← hconst, ← eLpNorm_congr_ae heq]
  exact eLpNorm_mono_measure _ (Measure.restrict_mono hQsub le_rfl)

/-- Weak Harnack supplies a positive a.e. lower bound on every smaller interior domain. -/
theorem capacitary_lower_bound {ψ : Vec d → ℝ} {η X : ℝ} (hη : 0 < η)
    (hψ0 : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ ψ x)
    (hψQ : ∀ᵐ x ∂volume.restrict (originCube 1), x ∈ remoteCube d (1 / 2) → ψ x = 1)
    (hweak : eLpNorm ψ (ENNReal.ofReal η) (volume.restrict (originCube (15 / 16))) ≤
      ENNReal.ofReal (Real.exp X) * nonnegativeEssInf (originCube (15 / 16)) ψ) :
    ∀ᵐ x ∂volume.restrict (originCube (3 / 4)),
      (capacitaryNormalization d η).toReal * Real.exp (-X) ≤ ψ x := by
  have hc := (capacitary_obstacle_norm hη hψQ).trans hweak
  have hprod : ENNReal.ofReal (Real.exp (-X)) * ENNReal.ofReal (Real.exp X) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  have hlow := mul_le_mul_right hc (ENNReal.ofReal (Real.exp (-X)))
  rw [← mul_assoc, hprod, one_mul] at hlow
  have hsub : originCube (d := d) (3 / 4) ⊆ originCube (15 / 16) :=
    originCube_mono' (by norm_num) (by norm_num) (by norm_num)
  have hsub1 : originCube (d := d) (3 / 4) ⊆ originCube 1 :=
    originCube_mono' (by norm_num) one_pos (by norm_num)
  have hae := ae_mono (Measure.restrict_mono hsub le_rfl)
    (ae_essInf_le (f := fun x => ENNReal.ofReal (ψ x))
      (μ := volume.restrict (originCube (15 / 16))))
  filter_upwards [hae, ae_mono (Measure.restrict_mono hsub1 le_rfl) hψ0] with x hx hx0
  apply (ENNReal.ofReal_le_ofReal_iff hx0).mp
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (capacitaryNormalization_ne_top hη), mul_comm]
  exact hlow.trans hx

end CoarseDeGiorgi.Endpoint
