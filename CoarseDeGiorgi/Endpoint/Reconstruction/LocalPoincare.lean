module

public import CoarseDeGiorgi.Endpoint.Morrey.Transport
public import Homogenization.Sobolev.W1p.CubeVector

/-! # Uniform finite-exponent Poincaré on cubes -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Pointwise

noncomputable section

theorem exists_cube_subAverage_poincare {d : ℕ} [NeZero d] {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : TriadicCube d)
      (u : W1pFunction (openCubeSet Q) (ENNReal.ofReal p)),
      u.subAverageLpSeminorm ≤ C * cubeScaleFactor Q * u.gradientCoordLpSeminormSum := by
  let U0 := openCubeSet (Homogenization.originCube d 0)
  obtain ⟨C, hC, hbase⟩ :=
    W1pFunction.exists_subAverage_poincare_constant_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet (Homogenization.originCube d 0)) hp
  refine ⟨C, hC, ?_⟩
  intro Q
  rw [openCubeSet_eq_translateSet_smul_originCube_zero Q]
  intro u
  let a := cubeScaleFactor Q
  have ha : 0 < a := zpow_pos (by norm_num) _
  let uD : W1pFunction (a • U0) (ENNReal.ofReal p) :=
    Morrey.untranslateW1p (triadicCubeShift Q) u
  let u0 : W1pFunction U0 (ENNReal.ofReal p) := uD.unscale ha
  have hb := hbase u0
  have htrans : uD.subAverageLpSeminorm = u.subAverageLpSeminorm :=
    congrArg ENNReal.toReal
      (Morrey.eLpNorm_subAverage_untranslateW1p (triadicCubeShift Q) u (ENNReal.ofReal p))
  have hgrad : uD.gradientCoordLpSeminormSum = u.gradientCoordLpSeminormSum :=
    Morrey.gradientCoordLpSeminormSum_untranslateW1p (triadicCubeShift Q) u
  have hdil := W1pFunction.subAverageLpSeminorm_unscale_eq ha ENNReal.ofReal_ne_top uD
  have hgdil := W1pFunction.gradientCoordLpSeminormSum_unscale_eq ha ENNReal.ofReal_ne_top uD
  have hscaled : W1pFunction.dilationLpFactor d (ENNReal.ofReal p) a⁻¹ *
      u.subAverageLpSeminorm ≤
      W1pFunction.dilationLpFactor d (ENNReal.ofReal p) a⁻¹ *
        (C * a * u.gradientCoordLpSeminormSum) := by
    calc
      _ = u0.subAverageLpSeminorm := by rw [hdil, htrans]
      _ ≤ C * u0.gradientCoordLpSeminormSum := hb
      _ = _ := by rw [hgdil, hgrad]; ring
  exact (mul_le_mul_iff_right₀
    (W1pFunction.dilationLpFactor_pos d (ENNReal.ofReal p) (inv_pos.mpr ha))).mp hscaled

theorem exists_cube_subAverage_poincare_finite {d : ℕ} [NeZero d]
    (p : FiniteLpExponent) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : TriadicCube d)
      (u : W1pFunction (openCubeSet Q) p.exponent),
      eLpNorm (fun x => u.toFun x - integralAverage (openCubeSet Q) u.toFun) p.exponent
          (volume.restrict (openCubeSet Q)) ≤
        ENNReal.ofReal (C * cubeScaleFactor Q * u.gradientCoordLpSeminormSum) := by
  have hp : 1 < p.exponent.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top p.lt_top.ne).mpr p.one_lt
  obtain ⟨C, hC, hbound⟩ := exists_cube_subAverage_poincare (d := d) hp
  refine ⟨C, hC, ?_⟩
  rw [← ENNReal.ofReal_toReal p.lt_top.ne]
  intro Q u
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hu : MemLp (fun x => u.toFun x - integralAverage (openCubeSet Q) u.toFun)
      (ENNReal.ofReal p.exponent.toReal) (volume.restrict (openCubeSet Q)) :=
    u.memLp.sub (memLp_const _)
  have hb := hbound Q u
  have he := ENNReal.ofReal_le_ofReal hb
  rwa [W1pFunction.subAverageLpSeminorm, ENNReal.ofReal_toReal hu.eLpNorm_ne_top] at he

end

end CoarseDeGiorgi.Endpoint.Reconstruction
