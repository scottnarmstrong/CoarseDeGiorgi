import CoarseDeGiorgi.Localization.SummedLocalSum
import CoarseDeGiorgi.Localization.SummedCells
import CoarseDeGiorgi.Localization.SummedEnergy
import CoarseDeGiorgi.Localization.SourceCover
import CoarseDeGiorgi.Localization.LowerFractional
import CoarseDeGiorgi.Assembly.HybridParameters
import CoarseDeGiorgi.LowerFractional.Restriction
import CoarseDeGiorgi.LowerFractional.CubeDomain
import CoarseDeGiorgi.Weighted.Identification
import CoarseDeGiorgi.Statements.LowerFractionalScaleBound
import CoarseDeGiorgi.Statements.LowerFractionalEmbedding

/-! # The localization bound with the local estimate summed over the cover

Proposition `p.fractional.localization`: the localized function is estimated by summing the local
bound over the cubes of the cover (Minkowski in the scale, Hölder over the cubes with
`1/r = 1/(2q) + 1/2`, bounded overlap), so there is no loss from the number of cubes. -/
namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem radiusCube_eq_originCube (R : ℝ) :
    radiusCube (d := d) R = CoarseDeGiorgi.originCube R := by
  ext x
  simp only [radiusCube, CoarseDeGiorgi.originCube, mem_ofPred_eq, abs_lt]

theorem originCube_mono {R R' : ℝ} (h : R ≤ R') :
    CoarseDeGiorgi.originCube (d := d) R ⊆ CoarseDeGiorgi.originCube R' := by
  intro x hx i
  exact ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩

theorem unitCube_domain :
    IsOpenBoundedConvexDomain (CoarseDeGiorgi.originCube (d := d) 1) ∧
      (CoarseDeGiorgi.originCube (d := d) 1).Nonempty := by
  have he : CoarseDeGiorgi.originCube (d := d) 1 = auxCube 1 (fun _ => 0) := by
    ext x
    simp only [CoarseDeGiorgi.originCube, auxCube, sub_self, sub_zero, zpow_zero,
      Int.cast_zero, zero_mul, abs_lt]
  rw [he]
  exact ⟨LowerFractional.auxCube_isOpenBoundedConvexDomain _ _,
    LowerFractional.auxCube_nonempty _ _⟩

/-- The half series identity, written for the normalized lower moment. -/
theorem lowerMoment_series_eq {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (t q : ℝ) (ht : 0 < t) (hq : 1 ≤ q) :
    (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
      (ENNReal.ofReal (lowerCellAverage a ha k q)) ^ (1 / (2 * q))) =
      ENNReal.ofReal ((1 - Real.rpow 3 (-t))⁻¹) * (lowerMoment a ha t q ht hq) ^ (-(1 / 2) : ℝ) := by
  have hpos : 0 < 1 - Real.rpow 3 (-t) :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht))
  have h : (lowerMoment a ha t q ht hq) ^ (-(1 / 2) : ℝ) =
      ENNReal.ofReal (1 - Real.rpow 3 (-t)) *
        ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
          (ENNReal.ofReal (lowerCellAverage a ha k q)) ^ (1 / (2 * q)) := by
    unfold lowerMoment
    simp only [ENNReal.rpow_eq_pow]
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [h, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le), inv_mul_cancel₀ hpos.ne',
    ENNReal.ofReal_one, one_mul]

end
end CoarseDeGiorgi.Localization
