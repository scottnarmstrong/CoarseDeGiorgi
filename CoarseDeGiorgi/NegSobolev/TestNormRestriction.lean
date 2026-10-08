module

public import CoarseDeGiorgi.Statements.SobolevNorm
public import Mathlib.MeasureTheory.Measure.Prod

/-! Restriction and evaluation bounds for the Sobolev norm. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.NegSobolev

/-- Restriction decreases the array fractional seminorm. -/
theorem testNorm_arrayFracSeminorm_mono {d : ℕ} {ι : Type*} [Fintype ι]
    {U V : Set (Vec d)} (hUV : U ⊆ V) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (F : ι → Vec d → ℝ) :
    arrayFracSeminorm U α r F ≤ arrayFracSeminorm V α r F := by
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hr.le)
  exact lintegral_mono' (Measure.prod_mono
    (Measure.restrict_mono hUV le_rfl) (Measure.restrict_mono hUV le_rfl)) le_rfl

/-- A smooth test supported in a smaller set gives the same integration-by-parts
identity on the larger and smaller carriers. -/
theorem testNorm_isWeakDerivArray_mono {d j : ℕ} {U V : Set (Vec d)}
    (hUV : U ⊆ V) {w : Vec d → ℝ} {D : (Fin j → Fin d) → Vec d → ℝ}
    (hD : IsWeakDerivArray V j w D) : IsWeakDerivArray U j w D := by
  refine ⟨hD.1.mono_set hUV, fun ι => ⟨(hD.2 ι).1.mono_set hUV, ?_⟩⟩
  intro φ hφ hc hs
  have hdφs : tsupport (fun x => iteratedFDeriv ℝ j φ x (fun k => basisVec (ι k))) ⊆ U := by
    apply Set.Subset.trans _ hs
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    apply support_iteratedFDeriv_subset (𝕜 := ℝ) j
    intro hz
    exact hx (by change iteratedFDeriv ℝ j φ x _ = 0; rw [hz]; rfl)
  have hid := (hD.2 ι).2 φ hφ hc (hs.trans hUV)
  have hleft (W : Set (Vec d)) (hUW : U ⊆ W) :
      (∫ x in W, w x * iteratedFDeriv ℝ j φ x (fun k => basisVec (ι k))) =
        ∫ x, w x * iteratedFDeriv ℝ j φ x (fun k => basisVec (ι k)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hUW (hdφs h))), mul_zero]
  have hright (W : Set (Vec d)) (hUW : U ⊆ W) :
      (∫ x in W, D ι x * φ x) = ∫ x, D ι x * φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hUW (hs h))), mul_zero]
  rw [hleft V hUV, hright V hUV] at hid
  rw [hleft U Set.Subset.rfl, hright U Set.Subset.rfl]
  exact hid

/-- Any actual family of weak derivatives bounds the infimum defining the norm. -/
theorem testNorm_sobolevNorm_le_of_isWeakDerivArray {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {β r : ℝ} (hβ : 0 ≤ β) (hr : 1 ≤ r) {w : Vec d → ℝ}
    (D : (j : Fin (⌊β⌋₊ + 1)) → (Fin j → Fin d) → Vec d → ℝ)
    (hD : ∀ j : Fin (⌊β⌋₊ + 1), IsWeakDerivArray U j w (D j)) :
    sobolevNorm U hU β r hβ hr w ≤
      ((∑ j : Fin (⌊β⌋₊ + 1),
          (eLpNorm (fun x => Real.sqrt (∑ ι, D j ι x ^ 2)) (ENNReal.ofReal r)
            (volume.restrict U)) ^ r) +
        (if β - ⌊β⌋₊ = 0 then 0
          else (arrayFracSeminorm U (β - ⌊β⌋₊) r (D (Fin.last ⌊β⌋₊))) ^ r)) ^ (1 / r) :=
  iInf_le_of_le D (iInf_le_of_le hD le_rfl)

/-- Restricting a function to an open subset cannot increase its Sobolev norm. -/
theorem testNorm_sobolevNorm_mono {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) {β r : ℝ}
    (hβ : 0 ≤ β) (hr : 1 ≤ r) (w : Vec d → ℝ) :
    sobolevNorm U hU β r hβ hr w ≤ sobolevNorm V hV β r hβ hr w := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  unfold sobolevNorm
  apply le_iInf
  intro D
  apply le_iInf
  intro hD
  refine (iInf_le_of_le D (iInf_le_of_le
    (fun j => testNorm_isWeakDerivArray_mono hUV (hD j)) le_rfl)).trans ?_
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hr0.le)
  apply add_le_add
  · exact Finset.sum_le_sum fun j _ => ENNReal.rpow_le_rpow
      (eLpNorm_mono_measure _ (Measure.restrict_mono hUV le_rfl)) hr0.le
  · split_ifs
    · exact le_rfl
    · exact ENNReal.rpow_le_rpow (testNorm_arrayFracSeminorm_mono hUV _ hr0 _) hr0.le

end CoarseDeGiorgi.NegSobolev
