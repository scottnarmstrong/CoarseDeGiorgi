import CoarseDeGiorgi.Endpoint.Source.Geometry
import CoarseDeGiorgi.Harnack.Iterations.MomentNormalization
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! The normalized quasi-triangle estimate used at the endpoint, including exponents below one. -/

open Homogenization MeasureTheory ENNReal
open scoped ENNReal

namespace CoarseDeGiorgi.Endpoint

/-- Constants depend only on the dimension and the exponent. -/
theorem completion_norm_bound (d : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∀ (u V : Vec d → ℝ),
        AEStronglyMeasurable u (volume.restrict (originCube 1)) →
        AEStronglyMeasurable V (volume.restrict (originCube 1)) →
        normalizedLpMoment r hr (originCube (5 / 8)) u ≤
          ENNReal.ofReal A * eLpNorm V (ENNReal.ofReal r) (volume.restrict (originCube 1)) +
          ENNReal.ofReal D * eLpNorm (fun x => u x - V x) ⊤
            (volume.restrict (originCube (5 / 8))) := by
  let E := originCube (d := d) (5 / 8)
  let m := volume E
  have hE := originCube_domain (d := d) (by norm_num : (0 : ℝ) < 5 / 8)
  have hm0 : m ≠ 0 := (hE.isOpen.measure_pos volume
    (originCube_nonempty (by norm_num))).ne'
  let : IsFiniteMeasure (volume.restrict E) := hE.isFiniteMeasure_restrict_volume
  have hmt : m ≠ ⊤ := by simpa only [Measure.restrict_apply_univ] using
    (measure_ne_top (volume.restrict E) Set.univ)
  let a := m ^ (-(1 / r)) * LpAddConst (ENNReal.ofReal r)
  let b := a * m ^ (1 / r)
  have hat : a ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_ne_zero hm0 hmt) (LpAddConst_lt_top _).ne
  have hbt : b ≠ ⊤ := ENNReal.mul_ne_top hat (ENNReal.rpow_ne_top_of_ne_zero hm0 hmt)
  refine ⟨a.toReal, b.toReal, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg, ?_⟩
  intro u V hu hV
  have hsub : E ⊆ originCube 1 := originCube_mono' (by norm_num) one_pos (by norm_num)
  have hμ := Measure.restrict_mono hsub (le_refl volume)
  have huE := hu.mono_measure hμ
  have hVE := hV.mono_measure hμ
  have hwE := huE.sub hVE
  have hw := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (p := ENNReal.ofReal r) (q := ⊤) le_top hwE
  simp only [ENNReal.toReal_ofReal hr.le, ENNReal.toReal_top, _root_.div_zero, sub_zero,
    Measure.restrict_apply_univ] at hw
  rw [ENNReal.ofReal_toReal hat, ENNReal.ofReal_toReal hbt,
    Harnack.Iterations.normalizedLpMoment_eq_eLpNorm E u hr huE]
  have huadd : u = V + (fun x => u x - V x) := by funext x; simp only [Pi.add_apply]; ring
  calc
    _ ≤ m ^ (-(1 / r)) * (LpAddConst (ENNReal.ofReal r) *
        (eLpNorm V (ENNReal.ofReal r) (volume.restrict E) +
          eLpNorm (fun x => u x - V x) (ENNReal.ofReal r) (volume.restrict E))) := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      conv_lhs => rw [huadd]
      exact eLpNorm_add_le' (f := V) (g := fun x => u x - V x) _
    _ ≤ m ^ (-(1 / r)) * (LpAddConst (ENNReal.ofReal r) *
        (eLpNorm V (ENNReal.ofReal r) (volume.restrict (originCube 1)) +
          eLpNorm (fun x => u x - V x) ⊤ (volume.restrict E) * m ^ (1 / r))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (add_le_add (eLpNorm_mono_measure V hμ) hw) zero_le) zero_le
    _ = _ := by dsimp only [a, b]; rw [← mul_assoc, mul_add]; ac_rfl

end CoarseDeGiorgi.Endpoint
