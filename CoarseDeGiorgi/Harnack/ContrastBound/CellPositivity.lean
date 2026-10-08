module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Harnack.Moments.LevelMeans
public import CoarseDeGiorgi.Weighted.LowerSpecNorm

@[expose] public section

namespace CoarseDeGiorgi.Harnack.ContrastBound

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- The level-`k` lower cell average is positive. -/
theorem lower_cell_average_pos {d : ℕ} (hd : 1 ≤ d) (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {q : ℝ} (hq : 1 ≤ q) :
    0 < lowerCellAverage a ha k q := by
  have hresponse : 0 < ‖lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖ := by
    change 0 < ‖Weighted.LowerResponseImpl.lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖
    exact Weighted.LowerResponseImpl.lowerResponseInv_norm_pos
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha
      (by omega)
  have hmean := Harnack.Moments.lower_level_mean hd k a ha hq
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hresponse q) hmean

/-- The lower moment is finite. -/
theorem lower_moment_lt_top {d : ℕ} (hd : 3 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {t q : ℝ} (ht : 0 < t) (hq : 1 ≤ q) :
    lowerMoment a ha t q ht hq < ⊤ := by
  have hfactorReal : 0 < 1 - Real.rpow 3 (-t) := by
    have hpow : Real.rpow 3 (-t) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht)
    linarith
  have hfactor : 0 < ENNReal.ofReal (1 - Real.rpow 3 (-t)) :=
    ENNReal.ofReal_pos.mpr hfactorReal
  have hzeroAverage : 0 < lowerCellAverage a ha 0 q :=
    lower_cell_average_pos (by omega) 0 a ha hq
  have hzeroPower : 0 < (ENNReal.ofReal (lowerCellAverage a ha 0 q)).rpow
      (1 / (2 * q)) :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hzeroAverage) ENNReal.ofReal_ne_top
  have hzeroScale : 0 < ENNReal.ofReal (Real.rpow 3 (-(((0 : ℕ) : ℝ) * t))) := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hzeroTerm : 0 < ENNReal.ofReal (Real.rpow 3 (-(((0 : ℕ) : ℝ) * t))) *
      (ENNReal.ofReal (lowerCellAverage a ha 0 q)).rpow (1 / (2 * q)) :=
    bot_lt_iff_ne_bot.mpr (mul_ne_zero hzeroScale.ne' hzeroPower.ne')
  have hsum : 0 < ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
        (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q)) := by
    exact lt_of_lt_of_le hzeroTerm
      (ENNReal.le_tsum (f := fun k : ℕ =>
        ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
          (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q))) 0)
  let M : ℝ≥0∞ := ENNReal.ofReal (1 - Real.rpow 3 (-t)) *
    ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
        (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q))
  have hMpos : 0 < M := by
    apply bot_lt_iff_ne_bot.mpr
    dsimp [M]
    exact mul_ne_zero hfactor.ne' hsum.ne'
  unfold lowerMoment
  change M.rpow (-2) < ⊤
  by_cases hMtop : M = ⊤
  · rw [hMtop]
    change ((⊤ : ℝ≥0∞) ^ (-2 : ℝ)) < ⊤
    rw [ENNReal.top_rpow_of_neg (by norm_num : (-2 : ℝ) < 0)]
    exact bot_lt_iff_ne_bot.mpr (by simp)
  · exact lt_top_iff_ne_top.mpr
      (ENNReal.rpow_ne_top_of_ne_zero hMpos.ne' hMtop)

end CoarseDeGiorgi.Harnack.ContrastBound
