import CoarseDeGiorgi.NegSobolev.TestNormRestriction
import Mathlib.Analysis.MeanInequalitiesPow

/-! Bounding the Sobolev expression by the sum of its constituent norms. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.NegSobolev

theorem testNorm_rpow_sum_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞)
    (r : ℝ) (hr : 1 ≤ r) :
    (∑ i ∈ s, a i ^ r) ^ (1 / r) ≤ ∑ i ∈ s, a i := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hp : 0 < 1 / r := by positivity
  have hp1 : 1 / r ≤ 1 := (div_le_one hr0).mpr hr
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, ENNReal.zero_rpow_of_pos hp, le_refl]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    refine (ENNReal.rpow_add_le_add_rpow _ _ hp.le hp1).trans ?_
    rw [← ENNReal.rpow_mul, show r * (1 / r) = 1 by field_simp, ENNReal.rpow_one]
    exact add_le_add_right ih _

theorem testNorm_sobolevNorm_le_sum {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {β r : ℝ} (hβ : 0 ≤ β) (hr : 1 ≤ r) {w : Vec d → ℝ}
    (D : (j : Fin (⌊β⌋₊ + 1)) → (Fin j → Fin d) → Vec d → ℝ)
    (hD : ∀ j : Fin (⌊β⌋₊ + 1), IsWeakDerivArray U j w (D j)) :
    sobolevNorm U hU β r hβ hr w ≤
      (∑ j : Fin (⌊β⌋₊ + 1), eLpNorm (fun x => Real.sqrt (∑ ι, D j ι x ^ 2))
        (ENNReal.ofReal r) (volume.restrict U)) +
      (if β - ⌊β⌋₊ = 0 then 0 else arrayFracSeminorm U (β - ⌊β⌋₊) r (D (Fin.last ⌊β⌋₊))) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hp : 0 < 1 / r := by positivity
  have hp1 : 1 / r ≤ 1 := (div_le_one hr0).mpr hr
  refine (testNorm_sobolevNorm_le_of_isWeakDerivArray hU hβ hr D hD).trans ?_
  refine (ENNReal.rpow_add_le_add_rpow _ _ hp.le hp1).trans ?_
  apply add_le_add (testNorm_rpow_sum_le_sum Finset.univ _ r hr)
  split_ifs
  · simp only [ENNReal.zero_rpow_of_pos hp, le_refl]
  · rw [← ENNReal.rpow_mul, show r * (1 / r) = 1 by field_simp, ENNReal.rpow_one]

end CoarseDeGiorgi.NegSobolev
