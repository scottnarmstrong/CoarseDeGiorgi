import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Foundations.Euclid.Basic
import CoarseDeGiorgi.LowerFractional.CubeDomain
import CoarseDeGiorgi.Sharpness.Defs
import Homogenization.Sobolev.WeakDerivatives
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Homogenization MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Sharpness

/-- The unit cube is an open bounded convex domain and is nonempty. -/
theorem originCube_one_domain {d : ℕ} [NeZero d] :
    IsOpenBoundedConvexDomain (CoarseDeGiorgi.originCube (d := d) 1) ∧
      (CoarseDeGiorgi.originCube (d := d) 1).Nonempty := by
  let z : Fin d → ℤ := fun _ => 0
  have he : CoarseDeGiorgi.originCube (d := d) 1 =
      CoarseDeGiorgi.auxCube 1 z := by
    ext x
    simp [z, CoarseDeGiorgi.originCube, CoarseDeGiorgi.auxCube,
      sub_self, sub_zero, Int.cast_zero, zero_mul, abs_lt]
  constructor
  · rw [he]
    exact LowerFractional.auxCube_isOpenBoundedConvexDomain 1 z
  · rw [he]
    exact LowerFractional.auxCube_nonempty 1 z

/-- The transverse radius on the unit cube is bounded by the cube radius. -/
theorem transverseNorm_le_sqrt_d_div_two {d : ℕ} {x : Vec d}
    (hx : x ∈ CoarseDeGiorgi.originCube 1) :
    transverseNorm x ≤ Real.sqrt (d : ℝ) / 2 := by
  have hmask : ‖transversePart x‖ ≤ (1 / 2 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
    intro i
    by_cases hi : i.val = 0
    · simp [transversePart, hi]
    · have hpart : transversePart x i = x i := by simp [transversePart, hi]
      rw [Real.norm_eq_abs, hpart]
      rcases hx i with ⟨hlo, hhi⟩
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hrad : transverseNorm x = CoarseDeGiorgi.Foundations.Euclid.eNorm2
      (transversePart x) := rfl
  rw [hrad]
  calc
    CoarseDeGiorgi.Foundations.Euclid.eNorm2 (transversePart x)
        ≤ Real.sqrt (d : ℝ) * ‖transversePart x‖ :=
          CoarseDeGiorgi.Foundations.Euclid.eNorm2_le_sqrt_mul_norm _
    _ ≤ Real.sqrt (d : ℝ) * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hmask (Real.sqrt_nonneg _)
    _ = Real.sqrt (d : ℝ) / 2 := by ring

/-- A diagonal matrix acts on its quadratic form coordinate by coordinate. -/
theorem vecDot_diagonal {d : ℕ} (b : Fin d → ℝ) (v : Vec d) :
    vecDot v (matVecMul (Matrix.diagonal b) v) =
      ∑ i, b i * (v i) ^ 2 := by
  calc
    vecDot v (matVecMul (Matrix.diagonal b) v) =
        ∑ i, v i * (b i * v i) := by
      simp [vecDot, matVecMul, Matrix.diagonal_apply]
    _ = ∑ i, b i * (v i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      ring

end CoarseDeGiorgi.Sharpness
