module

public import CoarseDeGiorgi.SharpnessExamples.CylinderAveragesMoments
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

/-- One discounted scalar level of the norm in (`e.sharpness.cylinder.discount`). -/
noncomputable def cylinderFractionDiscountedLevel {n : ℕ}
    (k : ℕ) (epsilon : ℝ) (center : Vec n) (v b : ℝ) : ℝ :=
  Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
    cylinderFractionLevelMoment k epsilon center v

private theorem epsilon_rpow_decreasing {epsilon a b : ℝ}
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1) (hab : a ≤ b) :
    Real.rpow epsilon b ≤ Real.rpow epsilon a := by
  have hdiff : 0 ≤ b - a := sub_nonneg.mpr hab
  have htail : Real.rpow epsilon (b - a) ≤ 1 := by
    calc
      _ ≤ Real.rpow 1 (b - a) :=
        Real.rpow_le_rpow (le_of_lt heps) heps1 hdiff
      _ = 1 := Real.one_rpow _
  calc
    Real.rpow epsilon b = Real.rpow epsilon (a + (b - a)) := by
      congr 1
      ring
    _ = Real.rpow epsilon a * Real.rpow epsilon (b - a) :=
      Real.rpow_add heps _ _
    _ ≤ Real.rpow epsilon a * 1 :=
      mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg (le_of_lt heps) _)
    _ = Real.rpow epsilon a := by ring

private theorem epsilon_rpow_min_eq_max {epsilon a b : ℝ}
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1) :
    Real.rpow epsilon (min a b) =
      max (Real.rpow epsilon a) (Real.rpow epsilon b) := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab, max_eq_left]
    exact epsilon_rpow_decreasing heps heps1 hab
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba, max_eq_right]
    exact epsilon_rpow_decreasing heps heps1 hba

private theorem triadicSide_rpow {k : ℕ} {b : ℝ} :
    Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) =
      Real.rpow ((3 : ℝ) ^ (-(k : ℤ))) (2 * b) := by
  have hside : (3 : ℝ) ^ (-(k : ℤ)) = Real.rpow 3 (-(k : ℝ)) := by
    exact (Real.rpow_neg_natCast (3 : ℝ) k).symm
  calc
    _ = Real.rpow 3 ((-(k : ℝ)) * (2 * b)) := by
      congr 1
      ring
    _ = Real.rpow (Real.rpow 3 (-(k : ℝ))) (2 * b) :=
      Real.rpow_mul (by norm_num : 0 ≤ (3 : ℝ)) _ _
    _ = _ := by rw [← hside]

private theorem cylinderPhi_fine {n : ℕ} {epsilon v side : ℝ}
    (heps : 0 < epsilon) (hv : 1 ≤ v) (hside : side ≤ epsilon) :
    Real.rpow epsilon (n : ℝ) *
        Real.rpow (max epsilon side) (-((n : ℝ) * (1 - 1 / v))) =
      Real.rpow epsilon ((n : ℝ) / v) := by
  rw [max_eq_left hside]
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hexp : (n : ℝ) + -((n : ℝ) * (1 - 1 / v)) = (n : ℝ) / v := by
    field_simp [hvpos.ne']
    ring
  calc
    _ = Real.rpow epsilon ((n : ℝ) + -((n : ℝ) * (1 - 1 / v))) :=
      (Real.rpow_add heps _ _).symm
    _ = Real.rpow epsilon ((n : ℝ) / v) := by rw [hexp]

private theorem cylinderPhi_coarse {n : ℕ} {epsilon v side : ℝ}
    (hside : epsilon ≤ side) :
    Real.rpow epsilon (n : ℝ) *
        Real.rpow (max epsilon side) (-((n : ℝ) * (1 - 1 / v))) =
      Real.rpow epsilon (n : ℝ) *
        Real.rpow side (-((n : ℝ) * (1 - 1 / v))) := by
  rw [max_eq_right hside]

private theorem cylinderPhi_weighted_le_min {n : ℕ}
    {epsilon v b : ℝ} (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (vbound : 1 ≤ v) (hb : 0 ≤ b) (k : ℕ) :
    Real.rpow ((3 : ℝ) ^ (-(k : ℤ))) (2 * b) *
      cylinderPhi n v epsilon k ≤
        Real.rpow epsilon (min (n : ℝ) ((n : ℝ) / v + 2 * b)) := by
  let side : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let alpha : ℝ := 1 - 1 / v
  let m : ℝ := (n : ℝ) / v + 2 * b
  have hvpos : 0 < v := zero_lt_one.trans_le vbound
  have hsidepos : 0 < side := by dsimp [side]; positivity
  have hside1 : side ≤ 1 := by
    dsimp [side]
    rw [show (3 : ℝ) ^ (-(k : ℤ)) = ((3 : ℝ) ^ k)⁻¹ by simp [zpow_neg]]
    apply (inv_le_one₀ (by positivity : 0 < (3 : ℝ) ^ k)).2
    exact one_le_pow₀ (by norm_num : 1 ≤ (3 : ℝ))
  by_cases hside : side ≤ epsilon
  · have hphi : cylinderPhi n v epsilon k = Real.rpow epsilon ((n : ℝ) / v) := by
      change Real.rpow epsilon (n : ℝ) *
        Real.rpow (max epsilon side) (-((n : ℝ) * (1 - 1 / v))) = _
      exact cylinderPhi_fine (n := n) heps vbound hside
    have hsidePow : Real.rpow side (2 * b) ≤ Real.rpow epsilon (2 * b) :=
      Real.rpow_le_rpow hsidepos.le hside (by positivity)
    have hsum : 2 * b + (n : ℝ) / v = m := by dsimp [m]; ring
    have hprod : Real.rpow epsilon (2 * b) *
        Real.rpow epsilon ((n : ℝ) / v) = Real.rpow epsilon m := by
      calc
        _ = Real.rpow epsilon (2 * b + (n : ℝ) / v) :=
          (Real.rpow_add heps _ _).symm
        _ = Real.rpow epsilon m := by rw [hsum]
    calc
      _ = Real.rpow side (2 * b) * Real.rpow epsilon ((n : ℝ) / v) := by
        rw [hphi]
      _ ≤ Real.rpow epsilon (2 * b) * Real.rpow epsilon ((n : ℝ) / v) :=
        mul_le_mul_of_nonneg_right hsidePow (Real.rpow_nonneg (le_of_lt heps) _)
      _ = Real.rpow epsilon m := hprod
      _ ≤ max (Real.rpow epsilon (n : ℝ)) (Real.rpow epsilon m) := le_max_right _ _
      _ = Real.rpow epsilon (min (n : ℝ) m) := by
        exact (epsilon_rpow_min_eq_max (epsilon := epsilon) (a := n) (b := m)
          heps heps1).symm
  · have hepsside : epsilon ≤ side := le_of_not_ge hside
    have hphi : cylinderPhi n v epsilon k = Real.rpow epsilon (n : ℝ) *
        Real.rpow side (-((n : ℝ) * (1 - 1 / v))) := by
      change Real.rpow epsilon (n : ℝ) *
        Real.rpow (max epsilon side) (-((n : ℝ) * (1 - 1 / v))) = _
      exact cylinderPhi_coarse hepsside
    let gamma : ℝ := 2 * b - (n : ℝ) * alpha
    have hgamma : gamma = m - (n : ℝ) := by
      dsimp [gamma, m, alpha]
      field_simp [hvpos.ne']
      ring
    have hgammaAdd : 2 * b + -((n : ℝ) * alpha) = gamma := by
      dsimp [gamma]
      ring
    have hcombine : Real.rpow side (2 * b) *
        Real.rpow side (-((n : ℝ) * alpha)) = Real.rpow side gamma := by
      calc
        _ = Real.rpow side (2 * b + -((n : ℝ) * alpha)) :=
          (Real.rpow_add hsidepos _ _).symm
        _ = Real.rpow side gamma := by rw [hgammaAdd]
    by_cases hgammaPos : 0 ≤ gamma
    · have hgammapow : Real.rpow side gamma ≤ 1 := by
        calc
          _ ≤ Real.rpow 1 gamma := Real.rpow_le_rpow hsidepos.le hside1 hgammaPos
          _ = 1 := Real.one_rpow _
      have hn : Real.rpow epsilon (n : ℝ) * 1 =
          Real.rpow epsilon (n : ℝ) := by ring
      calc
        _ = Real.rpow side (2 * b) *
            (Real.rpow epsilon (n : ℝ) *
              Real.rpow side (-((n : ℝ) * alpha))) := by rw [hphi]
        _ = Real.rpow epsilon (n : ℝ) * Real.rpow side gamma := by
          calc
            _ = Real.rpow epsilon (n : ℝ) *
                (Real.rpow side (2 * b) *
                  Real.rpow side (-((n : ℝ) * alpha))) := by ring
            _ = _ := by rw [hcombine]
        _ ≤ Real.rpow epsilon (n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hgammapow (Real.rpow_nonneg (le_of_lt heps) _)
        _ ≤ Real.rpow epsilon (min (n : ℝ) m) := by
          rw [epsilon_rpow_min_eq_max (epsilon := epsilon) (a := n) (b := m)
            heps heps1]
          rw [hn]
          exact le_max_left _ _
    · have hgammaNeg : gamma ≤ 0 := le_of_not_ge hgammaPos
      have hgammapow : Real.rpow side gamma ≤ Real.rpow epsilon gamma :=
        Real.rpow_le_rpow_of_nonpos heps hepsside hgammaNeg
      have hsum : (n : ℝ) + gamma = m := by rw [hgamma]; ring
      have hprod : Real.rpow epsilon (n : ℝ) * Real.rpow epsilon gamma =
          Real.rpow epsilon m := by
        calc
          _ = Real.rpow epsilon ((n : ℝ) + gamma) :=
            (Real.rpow_add heps _ _).symm
          _ = Real.rpow epsilon m := by rw [hsum]
      calc
        _ = Real.rpow side (2 * b) *
            (Real.rpow epsilon (n : ℝ) *
              Real.rpow side (-((n : ℝ) * alpha))) := by rw [hphi]
        _ = Real.rpow epsilon (n : ℝ) * Real.rpow side gamma := by
          calc
            _ = Real.rpow epsilon (n : ℝ) *
                (Real.rpow side (2 * b) *
                  Real.rpow side (-((n : ℝ) * alpha))) := by ring
            _ = _ := by rw [hcombine]
        _ ≤ Real.rpow epsilon (n : ℝ) * Real.rpow epsilon gamma :=
          mul_le_mul_of_nonneg_left hgammapow (Real.rpow_nonneg (le_of_lt heps) _)
        _ = Real.rpow epsilon m := hprod
        _ ≤ max (Real.rpow epsilon (n : ℝ)) (Real.rpow epsilon m) := le_max_right _ _
        _ = Real.rpow epsilon (min (n : ℝ) m) := by
          exact (epsilon_rpow_min_eq_max (epsilon := epsilon) (a := n) (b := m)
            heps heps1).symm

/-- Constant in the upper discounted estimate. -/
noncomputable def cylinderFractionDiscountedUpperConstant (n : ℕ) (v : ℝ) : ℝ :=
  Real.rpow ((Nat.factorial (n + 1) : ℝ) * (2 : ℝ) ^ (n + 1))
      (1 - 1 / v) * Real.rpow 2 ((n : ℝ) / v)

/-- Every discounted scalar level is bounded by the scale in
(`e.sharpness.cylinder.discount`). -/
theorem cylinderFractionDiscountedLevel_upper {n : ℕ}
    {epsilon : ℝ} (heps : 0 < epsilon) (heps4 : epsilon < 1 / 4)
    (center : Vec n) (hcenter : ∀ i, |center i| ≤ 1 / 4)
    (v b : ℝ) (hv : 1 ≤ v) (hb : 0 ≤ b) (k : ℕ) :
    cylinderFractionDiscountedLevel k epsilon center v b ≤
      cylinderFractionDiscountedUpperConstant n v *
        Real.rpow epsilon (min (n : ℝ) ((n : ℝ) / v + 2 * b)) := by
  let C := cylinderFractionDiscountedUpperConstant n v
  have hC : 0 ≤ C := by
    dsimp [C, cylinderFractionDiscountedUpperConstant]
    positivity
  have hweight : 0 ≤ Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) :=
    Real.rpow_nonneg (by norm_num) _
  have heps1 : epsilon ≤ 1 :=
    le_of_lt (heps4.trans (by norm_num : (1 / 4 : ℝ) < 1))
  have hmoment := cylinderFraction_level_moment_upper heps heps4 center
    hcenter v hv k
  have hprofile := cylinderPhi_weighted_le_min (n := n) heps heps1 hv hb k
  have hweightSide : Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) =
      Real.rpow ((3 : ℝ) ^ (-(k : ℤ))) (2 * b) := triadicSide_rpow
  calc
    _ = Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
        cylinderFractionLevelMoment k epsilon center v := rfl
    _ ≤ Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
        (Real.rpow ((Nat.factorial (n + 1) : ℝ) * (2 : ℝ) ^ (n + 1))
            (1 - 1 / v) * Real.rpow 2 ((n : ℝ) / v) *
          cylinderPhi n v epsilon k) :=
      mul_le_mul_of_nonneg_left hmoment hweight
    _ = C * (Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
          cylinderPhi n v epsilon k) := by
      dsimp [C, cylinderFractionDiscountedUpperConstant]
      ring
    _ = C * (Real.rpow ((3 : ℝ) ^ (-(k : ℤ))) (2 * b) *
          cylinderPhi n v epsilon k) := by rw [hweightSide]
    _ ≤ C * Real.rpow epsilon
          (min (n : ℝ) ((n : ℝ) / v + 2 * b)) :=
      mul_le_mul_of_nonneg_left hprofile hC
    _ = _ := rfl

end CoarseDeGiorgi.SharpnessExamples
