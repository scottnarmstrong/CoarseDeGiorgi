module

public import CoarseDeGiorgi.Endpoint.Morrey.Transport

/-! # Uniform scaled Morrey inequality for weak functions on cubes -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Morrey

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem morrey_holderConjugate {d : ℕ} (hd : 1 ≤ d) :
    (2 * (d : ℝ)).HolderConjugate (2 * d / (2 * d - 1)) := by
  have hdReal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply Real.holderConjugate_iff.mpr
  constructor
  · linarith
  · field_simp
    ring

theorem morrey_dual_kernel_exponent_lt {d : ℕ} (hd : 1 ≤ d) :
    ((d : ℝ) - 1) * (2 * d / (2 * d - 1)) < d := by
  have hdReal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < 2 * (d : ℝ) - 1 := by linarith
  rw [← mul_div_assoc, div_lt_iff₀ hden]
  nlinarith

/-- For the exponent `2d`, the Morrey dilation factor is the square root of
the side length. -/
theorem morrey_dilation_factor {d : ℕ} (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) :
    a * W1pFunction.dilationLpFactor d (ENNReal.ofReal (2 * d)) a⁻¹ = a ^ (1 / 2 : ℝ) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hexp : -(d : ℝ) * (1 / (2 * d)) = -(1 / 2 : ℝ) := by field_simp
  have hfactor : W1pFunction.dilationLpFactor d (ENNReal.ofReal (2 * d)) a⁻¹ =
      a ^ (-(1 / 2 : ℝ)) := by
    unfold W1pFunction.dilationLpFactor
    simp only [inv_inv, ← ENNReal.toReal_rpow, ENNReal.toReal_inv, one_div,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (d : ℝ)),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (a ^ d)⁻¹)]
    rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul ha.le,
      ← Real.rpow_mul ha.le]
    congr 1
    rw [mul_neg_one]
    simpa only [one_div] using hexp
  rw [hfactor]
  calc
    a * a ^ (-(1 / 2 : ℝ)) = a ^ (1 : ℝ) * a ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
    _ = a ^ (1 / 2 : ℝ) := by rw [← Real.rpow_add ha]; norm_num

/-- The reusable weak cube estimate needed for the reconstruction blocks. -/
theorem exists_cube_morrey_bound {d : ℕ} [NeZero d] :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
      MemLp u.grad (ENNReal.ofReal (2 * d)) (volume.restrict (openCubeSet Q)) →
      eLpNorm (fun x => u.toFun x - integralAverage (openCubeSet Q) u.toFun) ⊤
          (volume.restrict (openCubeSet Q)) ≤
        ENNReal.ofReal M * ENNReal.ofReal ((cubeScaleFactor Q) ^ (1 / 2 : ℝ)) *
          eLpNorm u.grad (ENNReal.ofReal (2 * d)) (volume.restrict (openCubeSet Q)) := by
  classical
  have hd : 1 ≤ d := NeZero.one_le
  obtain ⟨C, hC, hweak⟩ := exists_cube_weak_morrey_bound
    (morrey_holderConjugate hd) (morrey_dual_kernel_exponent_lt hd)
  refine ⟨C * d, mul_nonneg hC (Nat.cast_nonneg _), ?_⟩
  intro Q u hgrad
  let P : FiniteLpExponent := ⟨ENNReal.ofReal (2 * d),
    by rw [ENNReal.one_lt_ofReal]; have hdReal : (1 : ℝ) ≤ d := by exact_mod_cast hd
       linarith, ENNReal.ofReal_lt_top⟩
  have hg : GradMemLpOn (openCubeSet Q) P.exponent u.grad := memLp_pi_iff.mp hgrad
  let v := u.toW1pOfGradMemLp (isOpenBoundedConvexDomain_openCubeSet Q) P hg
  have hb := hweak Q v
  have ha : 0 < cubeScaleFactor Q := zpow_pos (by norm_num) _
  have hcoord (i : Fin d) : v.gradCoordLpSeminorm i ≤
      (eLpNorm u.grad (ENNReal.ofReal (2 * d)) (volume.restrict (openCubeSet Q))).toReal := by
    apply ENNReal.toReal_mono hgrad.eLpNorm_ne_top
    exact eLpNorm_mono_ae (v.grad_memLp i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => norm_le_pi_norm (u.grad x) i)
  have hsum : v.gradientCoordLpSeminormSum ≤
      d * (eLpNorm u.grad (ENNReal.ofReal (2 * d))
        (volume.restrict (openCubeSet Q))).toReal :=
    (Finset.sum_le_sum fun i _ => hcoord i).trans_eq (by simp)
  have hfactor := morrey_dilation_factor hd ha
  rw [show C * cubeScaleFactor Q *
      W1pFunction.dilationLpFactor d (ENNReal.ofReal (2 * d)) (cubeScaleFactor Q)⁻¹ =
      C * (cubeScaleFactor Q) ^ (1 / 2 : ℝ) by rw [mul_assoc, hfactor]] at hb
  refine hb.trans ?_
  calc
    ENNReal.ofReal (C * (cubeScaleFactor Q) ^ (1 / 2 : ℝ) * v.gradientCoordLpSeminormSum) ≤
        ENNReal.ofReal (C * (cubeScaleFactor Q) ^ (1 / 2 : ℝ) *
          (d * (eLpNorm u.grad (ENNReal.ofReal (2 * d))
            (volume.restrict (openCubeSet Q))).toReal)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = _ := by
      rw [show C * (cubeScaleFactor Q) ^ (1 / 2 : ℝ) *
          (d * (eLpNorm u.grad (ENNReal.ofReal (2 * d))
            (volume.restrict (openCubeSet Q))).toReal) =
          (C * d) * (cubeScaleFactor Q) ^ (1 / 2 : ℝ) *
            (eLpNorm u.grad (ENNReal.ofReal (2 * d))
              (volume.restrict (openCubeSet Q))).toReal by ring,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_toReal hgrad.eLpNorm_ne_top]

end

end CoarseDeGiorgi.Endpoint.Morrey
