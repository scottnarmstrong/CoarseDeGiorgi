module

public import CoarseDeGiorgi.Statements.WeightedEnergy
public import CoarseDeGiorgi.Harnack.LogLimit.EnergyLimit
public import Mathlib.Order.LiminfLimsup

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- Fatou's lower-limit step in the logarithmic energy argument.  The pointwise
power-Caccioppoli estimate is the source-specific input used to establish
`hPowerBound`; this lemma isolates the subsequent uniform-limit passage.
-/
theorem logEnergy_le_of_fatou_and_power_bound
    (E : ℕ → ℝ≥0∞) (Elog bound : ℝ≥0∞)
    (hFatou : Elog ≤ Filter.liminf E atTop)
    (hPowerBound : ∀ i, E i ≤ bound) :
    Elog ≤ bound := by
  calc
    Elog ≤ Filter.liminf E atTop := hFatou
    _ ≤ Filter.liminf (fun _ : ℕ => bound) atTop :=
      Filter.liminf_le_liminf (Filter.Eventually.of_forall hPowerBound)
    _ = bound := by simp

/-- The weighted-energy limit for the divided negative powers, as `m → 0`
(adapter to `LogLimit.tendsto_weightedEnergy_shifted_negative_power`). -/
theorem log_shifted_power_energy_tendsto {d : ℕ} {V : Set (Vec d)}
    {a : CoeffField d} (ha : IsWeightedCoeffOn V a)
    (U : Vec d → ℝ) (G : Vec d → Vec d) (ε : ℝ) (hε : 0 < ε)
    (hU : AEStronglyMeasurable U (volume.restrict V))
    (hUlower : ∀ᵐ x ∂(volume.restrict V), ε ≤ U x)
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (hGenergy : weightedEnergy a V G < ⊤)
    (m : ℕ → ℝ) (hmlo : ∀ n, -1 ≤ m n) (hmhi : ∀ n, m n ≤ 0)
    (hmtendsto : Tendsto m atTop (𝓝 0)) :
    Tendsto
      (fun n => weightedEnergy a V
        (fun x => U x ^ (m n - 1) • G x))
      atTop (𝓝 (weightedEnergy a V (fun x => U x ^ (-1 : ℝ) • G x))) :=
  CoarseDeGiorgi.Harnack.LogLimit.tendsto_weightedEnergy_shifted_negative_power
    ha U G ε hε hU hUlower hG hGenergy m hmlo hmhi hmtendsto

/-- On a probability space, the `Lʳ` norm of `U^m` tends to `1` as `m → 0` (adapter to
`LogLimit.tendsto_eLpNorm_shifted_negative_power_one`). -/
theorem log_shifted_power_norm_tendsto_one {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    (ε : ℝ) (hε : 0 < ε) (U : α → ℝ)
    (hU : AEStronglyMeasurable U μ)
    (hUlower : ∀ᵐ x ∂μ, ε ≤ U x)
    (r : ℝ) (hr : 0 < r)
    (m : ℕ → ℝ) (hmlo : ∀ n, -1 ≤ m n) (hmhi : ∀ n, m n ≤ 0)
    (hmtendsto : Tendsto m atTop (𝓝 0)) :
    Tendsto
      (fun n => eLpNorm (fun x => U x ^ (m n)) (ENNReal.ofReal r) μ)
      atTop (𝓝 1) :=
  CoarseDeGiorgi.Harnack.LogLimit.tendsto_eLpNorm_shifted_negative_power_one
    ε hε U hU hUlower r hr m hmlo hmhi hmtendsto

end

end CoarseDeGiorgi.Harnack.Log
