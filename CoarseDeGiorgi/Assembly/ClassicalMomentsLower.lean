module

public import CoarseDeGiorgi.Assembly.ClassicalMomentsSeries
public import CoarseDeGiorgi.Weighted.ResponseBoundsLower

@[expose] public section

namespace CoarseDeGiorgi.Assembly.ClassicalMomentsImpl

open Homogenization MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

/-- The exact lower norm statement for a fixed dimension and coefficient field. -/
def LowerNormBound {d : ℕ} (a : CoeffField d) : Prop :=
  ∀ {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a),
    ‖lowerResponseInv a V hV hne ha‖ ≤ ‖volumeAverageMat V (fun x => (a x)⁻¹)‖

theorem lowerCellAverage_bound_of_lower_norm {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (hlower : LowerNormBound a)
    {q : ℝ} (hq : 1 ≤ q)
    (hLp : eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
      (volume.restrict (originCube 1)) < ⊤) (k : ℕ) :
    lowerCellAverage a ha k q ≤ ∫ x in originCube 1, ‖(a x)⁻¹‖ ^ q := by
  have hM := (Weighted.response_inverse_coefficient ha).1
  obtain ⟨hi, hip⟩ := classical_integrability hq hM hLp
  apply classical_level_bound k hq hi hip (lowerResponseInvOnCell k a ha)
  intro η
  exact hlower (simplexCell_isOpenBoundedConvexDomain k η) (simplexCell_nonempty k η)
    (weightedCoeffOn_simplexCell k a ha η)

theorem lowerMoment_inv_eq_series_sq {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (t q : ℝ) (ht : 0 < t) (hq : 1 ≤ q) :
    (lowerMoment a ha t q ht hq)⁻¹ =
      (ENNReal.ofReal (1 - Real.rpow 3 (-t)) *
        ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
          (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q))) ^ 2 := by
  unfold lowerMoment
  change ((_ ^ (-2 : ℝ))⁻¹ : ENNReal) = _
  rw [ENNReal.rpow_neg, inv_inv]
  exact ENNReal.rpow_ofNat _ 2

/-- The lower reciprocal-moment comparison, conditional only on the lower norm bound. -/
theorem lowerMoment_inv_le_classical_of_lower_norm {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (hlower : LowerNormBound a)
    {q t : ℝ} (hq : 1 ≤ q) (ht : 0 < t)
    (hLp : eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
      (volume.restrict (originCube 1)) < ⊤) :
    (lowerMoment a ha t q ht hq)⁻¹ ≤
      eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q) (volume.restrict (originCube 1)) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hM := (Weighted.response_inverse_coefficient ha).1
  have hb := normalized_series_le hq0 ht (fun k => lowerCellAverage a ha k q)
    (lowerCellAverage_bound_of_lower_norm a ha hlower hq hLp)
  obtain ⟨_, hi⟩ := classical_integrability hq hM hLp
  rw [classical_eLpNorm_eq hq0 hM hi, lowerMoment_inv_eq_series_sq]
  exact (pow_le_pow_left' hb 2).trans_eq (half_power_sq _ hq0)

theorem contrast_le_classical_of_lower_norm {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (hlower : LowerNormBound a)
    {p q s t : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 0 < s) (ht : 0 < t)
    (hLp : eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
      (volume.restrict (originCube 1)) < ⊤)
    (hLq : eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
      (volume.restrict (originCube 1)) < ⊤) :
    contrast a ha s t p q hs ht hp hq ≤
      eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p) (volume.restrict (originCube 1)) *
        eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q) (volume.restrict (originCube 1)) := by
  change (CoarseDeGiorgi.upperMoment a ha s p hs hp /
    CoarseDeGiorgi.lowerMoment a ha t q ht hq) ≤ _
  rw [div_eq_mul_inv]
  exact mul_le_mul' (upperMoment_le_classical a ha hp hs hLp)
    (lowerMoment_inv_le_classical_of_lower_norm a ha hlower hq ht hLq)


end CoarseDeGiorgi.Assembly.ClassicalMomentsImpl
