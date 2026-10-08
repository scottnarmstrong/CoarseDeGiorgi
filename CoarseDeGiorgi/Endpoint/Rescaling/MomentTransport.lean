module

public import CoarseDeGiorgi.Endpoint.Rescaling.CellMoments
public import CoarseDeGiorgi.Endpoint.Rescaling.DiscountShift
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.Contrast

/-! Uniform moment and contrast bounds for the interior lattice maps. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Endpoint.Rescaling

noncomputable def seriesCost (d : ℕ) (s p : ℝ) : ℝ≥0∞ :=
  let A := (ENNReal.ofReal ((3 : ℝ) ^ (3 * d))).rpow (1 / (2 * p))
  let B := (ENNReal.ofReal (Real.rpow (Nat.factorial d : ℝ) p)).rpow (1 / (2 * p))
  let w := ENNReal.ofReal (Real.rpow 3 (-s))
  B * A * (w ^ 4)⁻¹ + A * (w ^ 3)⁻¹

theorem seriesCost_ne_top (d : ℕ) (s p : ℝ) (hp : 0 < p) : seriesCost d s p ≠ ⊤ := by
  have hA : (ENNReal.ofReal ((3 : ℝ) ^ (3 * d))).rpow (1 / (2 * p)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hB : (ENNReal.ofReal (Real.rpow (Nat.factorial d : ℝ) p)).rpow (1 / (2 * p)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hw : ENNReal.ofReal (Real.rpow 3 (-s)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top hB hA)
      (ENNReal.inv_ne_top.mpr (pow_ne_zero _ hw)),
      ENNReal.mul_ne_top hA (ENNReal.inv_ne_top.mpr (pow_ne_zero _ hw))⟩

theorem geometric_weight (s : ℝ) (k : ℕ) :
    ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) =
      (ENNReal.ofReal (Real.rpow 3 (-s))) ^ k := by
  simp only [Real.rpow_eq_pow]
  rw [show -((k : ℝ) * s) = -s * k by ring]
  rw [Real.rpow_mul_natCast (by norm_num), ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _)]

theorem response_series_le {d : ℕ} (D : ResponseFamily d) (a b : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (hb : IsWeightedCoeffOn (originCube 1) b)
    (z : Fin d → ℤ) (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39)
    {s p : ℝ} (hp : 1 ≤ p)
    (hcov : ∀ (l : ℕ) (η : SimplexIndex d (l + 1)), cellResponse D b hb (l + 1) η =
      cellResponse D a ha (l + 4) (latticeIndex z hz l η)) :
    (ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
      ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal (cellAverage D b hb k p)).rpow (1 / (2 * p))) ≤
    seriesCost d s p * (ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
      ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal (cellAverage D a ha k p)).rpow (1 / (2 * p))) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  let f := fun k => (ENNReal.ofReal (cellAverage D b hb k p)).rpow (1 / (2 * p))
  let g := fun k => (ENNReal.ofReal (cellAverage D a ha k p)).rpow (1 / (2 * p))
  let A := (ENNReal.ofReal ((3 : ℝ) ^ (3 * d))).rpow (1 / (2 * p))
  let B := (ENNReal.ofReal (Real.rpow (Nat.factorial d : ℝ) p)).rpow (1 / (2 * p))
  let w := ENNReal.ofReal (Real.rpow 3 (-s))
  have hzero : f 0 ≤ B * f 1 := by
    dsimp [f, B]
    have h := ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (cellAverage_zero_le D b hb hp)) (by positivity : 0 ≤ 1 / (2 * p))
    simp only [Real.rpow_eq_pow] at h
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at h
    simpa only [ENNReal.rpow_eq_pow] using h
  have hshift : ∀ k, f (k + 1) ≤ A * g (k + 4) := by
    intro k
    have h := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
      (cellAverage_shift_le D a b ha hb z hz k p (hcov k))) (by positivity : 0 ≤ 1 / (2 * p))
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (3 : ℝ) ^ (3 * d)),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at h
    simpa only [f, g, A, ENNReal.rpow_eq_pow] using h
  have h := discounted_shift_bound f g A B w
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)))
    ENNReal.ofReal_ne_top hzero hshift
  simp only [geometric_weight]
  calc
    _ ≤ ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
        ((B * A * (w ^ 4)⁻¹ + A * (w ^ 3)⁻¹) * ∑' k, w ^ k * g k) :=
      mul_le_mul_right h _
    _ = _ := by
      change _ = (B * A * (w ^ 4)⁻¹ + A * (w ^ 3)⁻¹) * _
      dsimp only [g, w]
      ac_rfl

theorem upperMoment_affine_le {d : ℕ} [NeZero d] (z : Fin d → ℤ)
    (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (hb : IsWeightedCoeffOn (originCube 1) (a ∘ affineMap (latticeCenter z) (1 / 27)))
    {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) :
    upperMoment (a ∘ affineMap (latticeCenter z) (1 / 27)) hb s p hs hp ≤
      (seriesCost d s p) ^ 2 * upperMoment a ha s p hs hp := by
  have h := response_series_le (upperFamily d) a _ ha hb z hz (s := s) hp
    (upper_cellResponse_affine z hz a ha hb)
  unfold upperMoment
  simp_rw [upperCellAverage_eq]
  exact (pow_le_pow_left' h 2).trans_eq (mul_pow _ _ _)

theorem lowerMoment_inv_affine_le {d : ℕ} [NeZero d] (z : Fin d → ℤ)
    (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (hb : IsWeightedCoeffOn (originCube 1) (a ∘ affineMap (latticeCenter z) (1 / 27)))
    {t q : ℝ} (ht : 0 < t) (hq : 1 ≤ q) :
    (lowerMoment (a ∘ affineMap (latticeCenter z) (1 / 27)) hb t q ht hq)⁻¹ ≤
      (seriesCost d t q) ^ 2 * (lowerMoment a ha t q ht hq)⁻¹ := by
  have h := response_series_le (lowerFamily d) a _ ha hb z hz (s := t) hq
    (lower_cellResponse_affine z hz a ha hb)
  unfold lowerMoment
  simp_rw [lowerCellAverage_eq, ENNReal.rpow_eq_pow,
    ENNReal.rpow_neg, inv_inv, ENNReal.rpow_two]
  exact (pow_le_pow_left' h 2).trans_eq (mul_pow _ _ _)

noncomputable def contrastCost (d : ℕ) (s t p q : ℝ) : ℝ≥0∞ :=
  (seriesCost d s p) ^ 2 * (seriesCost d t q) ^ 2

theorem contrastCost_ne_top (d : ℕ) (s t p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    contrastCost d s t p q ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.pow_ne_top (seriesCost_ne_top d s p hp))
    (ENNReal.pow_ne_top (seriesCost_ne_top d t q hq))

theorem momentData_affine {d : ℕ} [NeZero d] (z : Fin d → ℤ)
    (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (hb : IsWeightedCoeffOn (originCube 1) (a ∘ affineMap (latticeCenter z) (1 / 27)))
    {s t p q : ℝ} (hs : 0 < s) (ht : 0 < t) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hU : upperMoment a ha s p hs hp < ⊤) (hL : 0 < lowerMoment a ha t q ht hq) :
    upperMoment (a ∘ affineMap (latticeCenter z) (1 / 27)) hb s p hs hp < ⊤ ∧
    0 < lowerMoment (a ∘ affineMap (latticeCenter z) (1 / 27)) hb t q ht hq ∧
    contrast (a ∘ affineMap (latticeCenter z) (1 / 27)) hb s t p q hs ht hp hq ≤
      contrastCost d s t p q * contrast a ha s t p q hs ht hp hq := by
  have hUc := upperMoment_affine_le z hz a ha hb hs hp
  have hLc := lowerMoment_inv_affine_le z hz a ha hb ht hq
  have hCU := ENNReal.pow_ne_top (seriesCost_ne_top d s p (zero_lt_one.trans_le hp)) (n := 2)
  have hCL := ENNReal.pow_ne_top (seriesCost_ne_top d t q (zero_lt_one.trans_le hq)) (n := 2)
  have hUb := lt_of_le_of_lt hUc (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hCU hU.ne))
  have hLb : 0 < lowerMoment (a ∘ affineMap (latticeCenter z) (1 / 27)) hb t q ht hq :=
    bot_lt_iff_ne_bot.mpr (ENNReal.inv_ne_top.mp
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top hCL (ENNReal.inv_ne_top.mpr hL.ne')) hLc))
  refine ⟨hUb, hLb, ?_⟩
  unfold contrast contrastCost
  simp only [div_eq_mul_inv]
  exact (mul_le_mul' hUc hLc).trans_eq (by ac_rfl)

theorem sqrt_contrast_affine_le {d : ℕ} [NeZero d] (z : Fin d → ℤ)
    (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (hb : IsWeightedCoeffOn (originCube 1) (a ∘ affineMap (latticeCenter z) (1 / 27)))
    {s t p q : ℝ} (hs : 0 < s) (ht : 0 < t) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hU : upperMoment a ha s p hs hp < ⊤) (hL : 0 < lowerMoment a ha t q ht hq) :
    Real.sqrt (contrast (a ∘ affineMap (latticeCenter z) (1 / 27)) hb s t p q hs ht hp hq).toReal ≤
      Real.sqrt (contrastCost d s t p q).toReal *
        Real.sqrt (contrast a ha s t p q hs ht hp hq).toReal := by
  have hK := contrastCost_ne_top d s t p q (zero_lt_one.trans_le hp) (zero_lt_one.trans_le hq)
  have hT : contrast a ha s t p q hs ht hp hq ≠ ⊤ :=
    (ENNReal.div_lt_top hU.ne hL.ne').ne
  have hc := (momentData_affine z hz a ha hb hs ht hp hq hU hL).2.2
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hK hT) hc
  rw [ENNReal.toReal_mul] at hr
  exact (Real.sqrt_le_sqrt hr).trans_eq (Real.sqrt_mul ENNReal.toReal_nonneg _)

end CoarseDeGiorgi.Endpoint.Rescaling
