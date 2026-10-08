module

public import CoarseDeGiorgi.Harnack.Crossover.Normalization
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Crossover

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- Positive powers and negative powers remain integrable after the constant
log-centering factors are applied. The two base integrability facts are the
output of the power statement of Lemma `l.weighted.testing`, with no upper bound on `U`
assumed. -/
theorem centered_weights_integrable_of_shifted_powers {d : ℕ}
    (V : Set (Vec d)) (U : Vec d → ℝ) (p : ℝ)
    (hplus : IntegrableOn (fun x => U x ^ p) V)
    (hminus : IntegrableOn (fun x => U x ^ (-p)) V) :
    IntegrableOn (centeredWeight V U p) V ∧
      IntegrableOn (centeredWeightInv V U p) V := by
  let kplus := Real.exp (-p * volumeAverage V (fun y => Real.log (U y)))
  let kminus := Real.exp (p * volumeAverage V (fun y => Real.log (U y)))
  have hplus' : Integrable (fun x => kplus • (fun y => U y ^ p) x)
      (volume.restrict V) := by
    change Integrable (fun x => U x ^ p) (volume.restrict V) at hplus
    simpa [smul_eq_mul, mul_comm] using hplus.const_mul kplus
  have hminus' : Integrable (fun x => kminus • (fun y => U y ^ (-p)) x)
      (volume.restrict V) := by
    change Integrable (fun x => U x ^ (-p)) (volume.restrict V) at hminus
    simpa [smul_eq_mul, mul_comm] using hminus.const_mul kminus
  constructor
  · change Integrable (centeredWeight V U p) (volume.restrict V)
    change Integrable (fun x => Real.exp (-p * volumeAverage V
      (fun y => Real.log (U y))) * U x ^ p) (volume.restrict V)
    simpa [kplus, smul_eq_mul] using hplus'
  · change Integrable (centeredWeightInv V U p) (volume.restrict V)
    change Integrable (fun x => Real.exp (p * volumeAverage V
      (fun y => Real.log (U y))) * U x ^ (-p)) (volume.restrict V)
    simpa [kminus, smul_eq_mul] using hminus'

/-- Both signs of the centered weight are strictly positive almost everywhere
where the shifted function is strictly positive. Real-valuedness supplies
finiteness without an essential upper bound. -/
theorem centered_weights_positive_ae {d : ℕ} (V : Set (Vec d))
    (U : Vec d → ℝ) (p : ℝ)
    (hU : ∀ᵐ x ∂(volume.restrict V), 0 < U x) :
    (∀ᵐ x ∂(volume.restrict V), 0 < centeredWeight V U p x) ∧
      (∀ᵐ x ∂(volume.restrict V), 0 < centeredWeightInv V U p x) := by
  constructor
  · filter_upwards [hU] with x hx
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hx p)
  · filter_upwards [hU] with x hx
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hx (-p))

end
end CoarseDeGiorgi.Harnack.Crossover
