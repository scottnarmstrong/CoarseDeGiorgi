module

public import CoarseDeGiorgi.Harnack.PowerLimits.SignedInterior
public import CoarseDeGiorgi.Assembly.LocalBoundedness
public import CoarseDeGiorgi.Weighted.Energy
public import CoarseDeGiorgi.Weighted.GradientHilbert
public import CoarseDeGiorgi.Weighted.UpperResponseAffine
public import CoarseDeGiorgi.Whitney.LiftZeroExtension

/-! # Signed-interior pairing on a smaller domain -/

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open Homogenization MeasureTheory Filter Set Topology
open scoped ENNReal

/-- Use the weighted-pairing limit on the enclosing domain while localizing
the fixed test gradient to a measurable subdomain. This is the interior
pairing convergence needed when the smooth cap approximants converge in
weighted energy on the unit cube.
-/
theorem pairing_tendsto_on_subset_of_energy_approximation
    {d : ℕ} {V U : Set (Vec d)} (hU : MeasurableSet U) (hUV : U ⊆ V)
    (a : CoeffField d) (ha : IsWeightedCoeffOn V a)
    {F : ℕ → Vec d → Vec d} {K H : Vec d → Vec d}
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict V))
    (hKmeas : AEStronglyMeasurable K (volume.restrict V))
    (hHmeas : AEStronglyMeasurable H (volume.restrict V))
    (hFE : ∀ n, weightedEnergy a V (F n) < ⊤)
    (hKE : weightedEnergy a V K < ⊤)
    (hHE : weightedEnergy a V H < ⊤)
    (hFK : Tendsto (fun n => weightedEnergy a V (F n - K)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U,
      vecDot (F n x) (matVecMul (a x) (H x))) atTop
      (𝓝 (∫ x in U, vecDot (K x) (matVecMul (a x) (H x)))) := by
  have hHUmeas : AEStronglyMeasurable (U.indicator H) (volume.restrict V) := by
    rw [aestronglyMeasurable_indicator_iff hU]
    rw [Measure.restrict_restrict hU, inter_eq_left.mpr hUV]
    exact hHmeas.mono_measure (Measure.restrict_mono hUV le_rfl)
  have hHUenergy : weightedEnergy a V (U.indicator H) < ⊤ := by
    rw [Whitney.lift_energy_indicator hU hUV]
    exact (LowerFractional.weightedEnergy_mono hUV H).trans_lt hHE
  have hlimit := PowerLimits.weighted_pairing_tendsto_of_energy_approximation
    ha hFmeas hKmeas hHUmeas hFE hKE hHUenergy hFK
  have hpair (X : Vec d → Vec d) (n : ℕ) :
      (fun x => vecDot (X x) (matVecMul (a x) (U.indicator H x))) =
        U.indicator (fun x => vecDot (X x) (matVecMul (a x) (H x))) := by
    funext x
    by_cases hx : x ∈ U
    · simp [hx]
    · simp only [Set.indicator_of_notMem hx, matVecMul_zero, vecDot_zero_right]
  have hleft (n : ℕ) :
      ∫ x in V, vecDot (F n x) (matVecMul (a x) (U.indicator H x)) =
        ∫ x in U, vecDot (F n x) (matVecMul (a x) (H x)) := by
    rw [show (fun x => vecDot (F n x) (matVecMul (a x) (U.indicator H x))) =
        U.indicator (fun x => vecDot (F n x) (matVecMul (a x) (H x))) from hpair (F n) n]
    rw [integral_indicator hU, Measure.restrict_restrict hU,
      inter_eq_left.mpr hUV]
  have hright :
      ∫ x in V, vecDot (K x) (matVecMul (a x) (U.indicator H x)) =
        ∫ x in U, vecDot (K x) (matVecMul (a x) (H x)) := by
    rw [show (fun x => vecDot (K x) (matVecMul (a x) (U.indicator H x))) =
        U.indicator (fun x => vecDot (K x) (matVecMul (a x) (H x))) from hpair K 0]
    rw [integral_indicator hU, Measure.restrict_restrict hU,
      inter_eq_left.mpr hUV]
  simpa only [hleft, hright] using hlimit

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
