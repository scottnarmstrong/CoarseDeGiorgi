import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
import CoarseDeGiorgi.Statements.LowerCellAverage
import CoarseDeGiorgi.Statements.UpperCellAverage
import CoarseDeGiorgi.Harnack.Moments.LowerAggregation
import CoarseDeGiorgi.Harnack.Moments.UpperGluing
import CoarseDeGiorgi.Weighted.UpperSpecNorm
import CoarseDeGiorgi.Weighted.LowerSpecNorm
import Mathlib.Analysis.MeanInequalitiesPow

namespace CoarseDeGiorgi.Harnack.Moments

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

private theorem upperResponse_norm_le_cellMean {d : ℕ} [NeZero d] (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) :
    ‖upperResponse a (originCube 1) LowerFractional.lower_unitCube_domain
      LowerFractional.lower_unitCube_nonempty ha‖ ≤
      ((triangulation (d := d) k).attach.sum fun η =>
        ‖upperResponseOnCell k a ha η‖) /
          ((triangulation (d := d) k).card : ℝ) := by
  classical
  let N : ℝ := ((triangulation (d := d) k).card : ℝ)
  let M : ℝ := ((triangulation (d := d) k).attach.sum fun η =>
    ‖upperResponseOnCell k a ha (show SimplexIndex d k from η)‖) / N
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (Finset.sum_nonneg fun η hη => norm_nonneg _)
      (Nat.cast_nonneg _)
  have hquad (e : Vec d) :
      vecDot e (matVecMul (upperResponse a (originCube 1)
        LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha) e) ≤
        M * vecNormSq e := by
    calc
      _ ≤ ((triangulation (d := d) k).attach.sum fun η =>
          vecDot e (matVecMul (upperResponseOnCell k a ha
            (show SimplexIndex d k from η)) e)) / N := by
        exact upper_gluing hd k a ha e
      _ ≤ ((triangulation (d := d) k).attach.sum fun η =>
          ‖upperResponseOnCell k a ha (show SimplexIndex d k from η)‖ *
            vecNormSq e) / N := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro η hη
        exact Weighted.LowerResponseImpl.lower_quadratic_le_norm
          (upperResponseOnCell k a ha (show SimplexIndex d k from η)) e
      _ = M * vecNormSq e := by
        dsimp [M, N]
        rw [div_eq_mul_inv, ← Finset.sum_mul]
        ring
  let S : Mat d := M • (1 : Mat d)
  have hS (e : Vec d) : vecDot e (matVecMul S e) = M * vecNormSq e := by
    simp [S, vecDot, matVecMul, vecNormSq, Matrix.one_apply]
    change (∑ i, e i * (M * e i)) = M * ∑ i, e i * e i
    calc
      (∑ i, e i * (M * e i)) = ∑ i, M * (e i * e i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = M * ∑ i, e i * e i := by rw [Finset.mul_sum]
  have hnorm := Weighted.UpperResponseImpl.matrix_l2_norm_le_of_quadratic
    (A := upperResponse a (originCube 1) LowerFractional.lower_unitCube_domain
      LowerFractional.lower_unitCube_nonempty ha)
    (B := S)
    (Weighted.UpperResponseImpl.upperResponse_posDef LowerFractional.lower_unitCube_domain
      LowerFractional.lower_unitCube_nonempty ha).posSemidef
    (fun e => hquad e |>.trans_eq (hS e).symm)
  have hnormS : ‖S‖ = M := by
    change ‖M • (1 : Mat d)‖ = M
    rw [norm_smul, show ‖(M : ℝ)‖ = M from abs_of_nonneg hM]
    have hOne : ‖(1 : Mat d)‖ = 1 := by
      rw [Matrix.cstar_norm_def]
      have hclm : Matrix.toEuclideanCLM (𝕜 := ℝ) (1 : Mat d) =
          ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) := by
        ext x
        simp [Matrix.toEuclideanCLM]
      rw [hclm]
      apply le_antisymm ContinuousLinearMap.norm_id_le
      let i : Fin d := ⟨0, by omega⟩
      let x : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (basisVec i)
      have hx : ‖x‖ ≠ 0 := by simp [x, basisVec]
      have hid :=
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))).ratio_le_opNorm x
      rw [ContinuousLinearMap.id_apply, div_self hx] at hid
      exact hid
    rw [hOne]
    ring
  change ‖upperResponse a (originCube 1) LowerFractional.lower_unitCube_domain
    LowerFractional.lower_unitCube_nonempty ha‖ ≤ M
  exact hnorm.trans_eq hnormS

private theorem finite_power_mean {ι : Type*} (s : Finset ι) (N p : ℝ)
    (hN : 0 < N) (hcard : (s.card : ℝ) = N) (hp : 1 ≤ p)
    (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i) :
    Real.rpow ((∑ i ∈ s, z i) / N) p ≤
      (∑ i ∈ s, Real.rpow (z i) p) / N := by
  have hweights : ∑ i ∈ s, (N⁻¹ : ℝ) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    exact mul_inv_cancel₀ hN.ne'
  have hmean := Real.rpow_arith_mean_le_arith_mean_rpow s
    (fun _ => N⁻¹) z (fun i _ => inv_nonneg.mpr hN.le) hweights hz hp
  have hweighted : (∑ i ∈ s, N⁻¹ * z i) = (∑ i ∈ s, z i) / N := by
    rw [← Finset.mul_sum, div_eq_mul_inv]
    ring
  calc
    Real.rpow ((∑ i ∈ s, z i) / N) p =
        Real.rpow (∑ i ∈ s, N⁻¹ * z i) p := by rw [hweighted]
    _ ≤ ∑ i ∈ s, N⁻¹ * Real.rpow (z i) p := hmean
    _ = (∑ i ∈ s, Real.rpow (z i) p) / N := by
      rw [← Finset.mul_sum, div_eq_mul_inv]
      ring

private theorem simplexCount_pos (d k : ℕ) :
    0 < ((triangulation (d := d) k).card : ℝ) := by
  exact_mod_cast Assembly.ClassicalMomentsImpl.triangulation_card_pos d k

/-- The `p`-th power of the upper response norm is at most the level-`k` cell average. -/
theorem upper_level_mean {d : ℕ} (hd : 1 ≤ d) (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {p : ℝ} (hp : 1 ≤ p) :
    Real.rpow ‖upperResponse a (originCube 1)
        LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖ p ≤
      upperCellAverage a ha k p := by
  classical
  let T := triangulation (d := d) k
  let N : ℝ := (T.card : ℝ)
  have hN : 0 < N := simplexCount_pos d k
  have hnorm := @upperResponse_norm_le_cellMean d ⟨by omega⟩ k a ha
  have hnorm' : ‖upperResponse a (originCube 1) LowerFractional.lower_unitCube_domain
      LowerFractional.lower_unitCube_nonempty ha‖ ≤
      (T.attach.sum fun η => ‖upperResponseOnCell k a ha
        (show SimplexIndex d k from η)‖) / N := by
      simpa [T, N] using hnorm
  have hp0 : 0 ≤ p := by linarith
  have hpow : Real.rpow ‖upperResponse a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖ p ≤
      Real.rpow ((T.attach.sum fun η => ‖upperResponseOnCell k a ha
        (show SimplexIndex d k from η)‖) / N) p :=
    Real.rpow_le_rpow (norm_nonneg _) hnorm' hp0
  calc
    _ ≤ Real.rpow ((T.attach.sum fun η => ‖upperResponseOnCell k a ha
          (show SimplexIndex d k from η)‖) / N) p := hpow
    _ ≤ (T.attach.sum fun η => Real.rpow
          (‖upperResponseOnCell k a ha (show SimplexIndex d k from η)‖) p) / N := by
      apply finite_power_mean T.attach N p hN ?_ hp (fun η =>
        ‖upperResponseOnCell k a ha (show SimplexIndex d k from η)‖)
        (fun _ _ => norm_nonneg _)
      simp [N]
    _ = upperCellAverage a ha k p := by
      rfl

/-- The `q`-th power of the inverse lower response norm is at most the level-`k` cell average.
-/
theorem lower_level_mean {d : ℕ} (hd : 1 ≤ d) (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {q : ℝ} (hq : 1 ≤ q) :
    Real.rpow ‖lowerResponseInv a (originCube 1)
        LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖ q ≤
      lowerCellAverage a ha k q := by
  classical
  let T := triangulation (d := d) k
  let N : ℝ := (T.card : ℝ)
  have hN : 0 < N := simplexCount_pos d k
  have hnorm := lower_whole_cube_aggregation hd k a ha
  have hnorm' : ‖lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖ ≤
      (T.attach.sum fun η => ‖lowerResponseInvOnCell k a ha
        (show SimplexIndex d k from η)‖) / N := by
      simpa [T, N] using hnorm
  have hq0 : 0 ≤ q := by linarith
  have hpow : Real.rpow ‖lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖ q ≤
      Real.rpow ((T.attach.sum fun η => ‖lowerResponseInvOnCell k a ha
        (show SimplexIndex d k from η)‖) / N) q :=
    Real.rpow_le_rpow (norm_nonneg _) hnorm' hq0
  calc
    _ ≤ Real.rpow ((T.attach.sum fun η => ‖lowerResponseInvOnCell k a ha
          (show SimplexIndex d k from η)‖) / N) q := hpow
    _ ≤ (T.attach.sum fun η => Real.rpow
          (‖lowerResponseInvOnCell k a ha (show SimplexIndex d k from η)‖) q) / N := by
      apply finite_power_mean T.attach N q hN ?_ hq (fun η =>
        ‖lowerResponseInvOnCell k a ha (show SimplexIndex d k from η)‖)
        (fun _ _ => norm_nonneg _)
      simp [N]
    _ = lowerCellAverage a ha k q := by
      rfl

end CoarseDeGiorgi.Harnack.Moments
