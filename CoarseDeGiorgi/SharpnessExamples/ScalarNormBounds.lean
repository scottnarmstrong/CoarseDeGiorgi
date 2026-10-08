module

public import CoarseDeGiorgi.SharpnessExamples.ScalarMajorants

/-! # Finite negative regularity norms of the scalar sharpness field -/

@[expose] public section

open Homogenization MeasureTheory
open CoarseDeGiorgi.Sharpness CoarseDeGiorgi.Foundations.FracGeometry
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem scalarMajorant_average (m n k : ℕ) (ζ κ α L : ℝ)
    (η : SimplexIndex (m + 1) k) :
    volumeAverage (simplexCell k η) (scalarMajorantTerm m n ζ κ α L) =
      cylinderB n * Real.rpow (cylinderRadius (m + 1) n ζ κ) (-α) *
        cylinderFraction (simplexCell k η) (L * cylinderRadius (m + 1) n ζ κ)
          (scalarTailCenter m n) := by
  unfold scalarMajorantTerm cylinderFraction volumeAverage
  rw [integral_const_mul]
  ring

private theorem cylinderFractionLevelMoment_eq_mean {m k : ℕ}
    (ε : ℝ) (c : Vec m) (v : ℝ) :
    cylinderFractionLevelMoment k ε c v = finitePowerMean
      (fun η : SimplexIndex (m + 1) k => cylinderFraction (simplexCell k η) ε c) v := by
  simp only [cylinderFractionLevelMoment, finitePowerMean, SimplexIndex,
    Fintype.card_coe, Finset.univ_eq_attach]

/-- Each positive cylinder summand contributes at most a dimensional constant
times `b_n`, uniformly over all discounted levels. -/
theorem scalarMajorant_discounted_bound {m : ℕ} (hm : 2 ≤ m)
    {ζ κ α L v b : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ)
    (hαm : α ≤ (m : ℝ)) (hαvb : α ≤ (m : ℝ) / v + 2 * b)
    (hL0 : 0 < L) (hL2 : L ≤ 2) (hv : 1 ≤ v) (hb : 0 ≤ b) (k n : ℕ) :
    Real.rpow 3 (-(2 * (k : ℝ) * b)) * finitePowerMean
      (fun η : SimplexIndex (m + 1) k =>
        volumeAverage (simplexCell k η) (scalarMajorantTerm m n ζ κ α L)) v ≤
      (cylinderFractionDiscountedUpperConstant m v *
        Real.rpow L (min (m : ℝ) ((m : ℝ) / v + 2 * b))) * cylinderB n := by
  let ε := cylinderRadius (m + 1) n ζ κ
  let e := min (m : ℝ) ((m : ℝ) / v + 2 * b)
  let A := cylinderB n * Real.rpow ε (-α)
  have hrad := scalarRadius_small (m := m) (k := n) (by omega) hζ0 hζ2 hκ
  have hε : 0 < ε := hrad.1
  have hA : 0 ≤ A := mul_nonneg (cylinderB_pos n).le (Real.rpow_nonneg hε.le _)
  have hsmall : L * ε < 1 / 4 :=
    (mul_le_mul_of_nonneg_right hL2 hε.le).trans_lt hrad.2
  have he : 0 ≤ e - α := sub_nonneg.mpr (le_min hαm hαvb)
  have hpow : Real.rpow ε (e - α) ≤ 1 :=
    Real.rpow_le_one hε.le (by linarith [hrad.2]) he
  have hC : 0 ≤ cylinderFractionDiscountedUpperConstant m v := by
    unfold cylinderFractionDiscountedUpperConstant
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _)
  have hbound := cylinderFractionDiscountedLevel_upper (mul_pos hL0 hε) hsmall
    (scalarTailCenter m n) scalarTailCenter_coord_bound v b hv hb k
  have hmean : finitePowerMean
      (fun η : SimplexIndex (m + 1) k => volumeAverage (simplexCell k η)
        (scalarMajorantTerm m n ζ κ α L)) v =
      A * cylinderFractionLevelMoment k (L * ε) (scalarTailCenter m n) v := by
    simp only [scalarMajorant_average]
    rw [finitePowerMean_smul _
      (fun η => (cylinderSimplex_fraction_bounds (L * ε) (scalarTailCenter m n) η).1)
      hA (zero_lt_one.trans_le hv), cylinderFractionLevelMoment_eq_mean]
  rw [hmean]
  have hfactor : A * Real.rpow (L * ε) e =
      Real.rpow L e * cylinderB n * Real.rpow ε (e - α) := by
    dsimp [A]
    rw [Real.mul_rpow hL0.le hε.le]
    have hcomb : ε ^ (-α) * ε ^ e = ε ^ (e - α) := by
      rw [← Real.rpow_add hε]
      congr 1
      ring
    calc
      _ = L ^ e * cylinderB n * (ε ^ (-α) * ε ^ e) := by ring
      _ = _ := by rw [hcomb]
  calc
    _ = A * cylinderFractionDiscountedLevel k (L * ε) (scalarTailCenter m n) v b := by
      unfold cylinderFractionDiscountedLevel
      ring
    _ ≤ A * (cylinderFractionDiscountedUpperConstant m v * Real.rpow (L * ε) e) :=
      mul_le_mul_of_nonneg_left hbound hA
    _ = (cylinderFractionDiscountedUpperConstant m v * Real.rpow L e) *
        cylinderB n * Real.rpow ε (e - α) := by
      calc
        _ = cylinderFractionDiscountedUpperConstant m v * (A * Real.rpow (L * ε) e) := by ring
        _ = _ := by rw [hfactor]; ring
    _ ≤ (cylinderFractionDiscountedUpperConstant m v * Real.rpow L e) * cylinderB n := by
      exact mul_le_of_le_one_right
        (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hL0.le _)) (cylinderB_pos n).le) hpow

end

end CoarseDeGiorgi.SharpnessExamples
