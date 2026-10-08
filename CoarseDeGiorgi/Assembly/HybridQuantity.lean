import CoarseDeGiorgi.Assembly.HybridParameters
import CoarseDeGiorgi.Assembly.EnergyToSupQuantity

namespace CoarseDeGiorgi.Assembly
open Homogenization MeasureTheory Filter
open scoped ENNReal

/-- The weighted energy square root is bounded by the combined source quantity,
including an infinite lower moment. -/
theorem hybrid_weighted_part_le_quantity {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a) (q t : ℝ) (ht : 0 < t) (hq : 1 ≤ q)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (l R : ℝ) :
    (lowerMoment a ha t q ht hq) ^ (-1 / 2 : ℝ) *
        weightedEnergy a (CoarseDeGiorgi.originCube R) (positiveTruncationGradient u G l) ^ (1 / 2 : ℝ) ≤
      twoLevelQuantity a ha q t ht hq u G l R := by
  have he : (lowerMoment a ha t q ht hq) ^ (-1 / 2 : ℝ) *
      weightedEnergy a (CoarseDeGiorgi.originCube R) (positiveTruncationGradient u G l) ^ (1 / 2 : ℝ) =
    ((lowerMoment a ha t q ht hq) ^ (-1 : ℝ) *
      weightedEnergy a (CoarseDeGiorgi.originCube R) (positiveTruncationGradient u G l)) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num only [neg_mul, one_mul]
  rw [he]
  unfold twoLevelQuantity
  simp only [ENNReal.rpow_eq_pow]
  exact ENNReal.rpow_le_rpow (le_add_left le_rfl) (by norm_num)

/-- The two separate localization inputs cost at most twice Y. -/
theorem hybrid_localization_inputs_le_quantity {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a) (q t : ℝ) (ht : 0 < t) (hq : 1 ≤ q)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (l R : ℝ) :
    (lowerMoment a ha t q ht hq) ^ (-1 / 2 : ℝ) *
        weightedEnergy a (CoarseDeGiorgi.originCube R) (positiveTruncationGradient u G l) ^ (1 / 2 : ℝ) +
      eLpNorm (fun x => max (u x - l) 0) (ENNReal.ofReal (paramR q))
        (volume.restrict (CoarseDeGiorgi.originCube R)) ≤ 2 * twoLevelQuantity a ha q t ht hq u G l R := by
  have hN : eLpNorm (fun x => max (u x - l) 0) (ENNReal.ofReal (paramR q))
      (volume.restrict (CoarseDeGiorgi.originCube R)) ≤ twoLevelQuantity a ha q t ht hq u G l R := by
    unfold twoLevelQuantity
    dsimp only
    calc
      _ = (eLpNorm (fun x => max (u x - l) 0) (ENNReal.ofReal (paramR q))
          (volume.restrict (CoarseDeGiorgi.originCube R)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num
      _ ≤ _ := ENNReal.rpow_le_rpow (le_add_right le_rfl) (by norm_num)
  simpa only [two_mul] using add_le_add
    (hybrid_weighted_part_le_quantity a ha q t ht hq u G l R) hN

/-- Changing the source value on a null set preserves Y on every smaller cube. -/
theorem hybrid_quantity_congr_ae {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a) (q t : ℝ) (ht : 0 < t) (hq : 1 ≤ q)
    {u v : Vec d → ℝ} (G : Vec d → Vec d)
    (heq : u =ᵐ[volume.restrict (CoarseDeGiorgi.originCube 1)] v) (l R : ℝ) (hR : R ≤ 1) :
    twoLevelQuantity a ha q t ht hq u G l R = twoLevelQuantity a ha q t ht hq v G l R := by
  have heR := ae_restrict_of_ae_restrict_of_subset (caccioppoli_cube_mono hR) heq
  have hv : (fun x => max (u x - l) 0) =ᵐ[volume.restrict (CoarseDeGiorgi.originCube R)]
      (fun x => max (v x - l) 0) := heR.mono fun x hx => by dsimp only; rw [hx]
  have hG : positiveTruncationGradient u G l =ᵐ[volume.restrict (CoarseDeGiorgi.originCube R)]
      positiveTruncationGradient v G l := by
    filter_upwards [heR] with x hx
    simp only [positiveTruncationGradient, hx]
  have hE : weightedEnergy a (CoarseDeGiorgi.originCube R) (positiveTruncationGradient u G l) =
      weightedEnergy a (CoarseDeGiorgi.originCube R) (positiveTruncationGradient v G l) :=
    Weighted.energy_congr_ae (a := a) hG
  unfold twoLevelQuantity
  dsimp only
  rw [eLpNorm_congr_ae hv, hE]

/-- The squared source quantity is exactly the value square plus normalized energy. -/
theorem hybrid_quantity_sq {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a) (q t : ℝ) (ht : 0 < t) (hq : 1 ≤ q)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (l R : ℝ) :
    twoLevelQuantity a ha q t ht hq u G l R ^ (2 : ℝ) =
      eLpNorm (fun x => max (u x - l) 0) (ENNReal.ofReal (paramR q))
          (volume.restrict (CoarseDeGiorgi.originCube R)) ^ (2 : ℝ) +
        (lowerMoment a ha t q ht hq) ^ (-1 : ℝ) *
          weightedEnergy a (CoarseDeGiorgi.originCube R) (positiveTruncationGradient u G l) := by
  unfold twoLevelQuantity
  simp only [ENNReal.rpow_eq_pow, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

end CoarseDeGiorgi.Assembly
