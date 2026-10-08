module

public import CoarseDeGiorgi.Harnack.Crossover.Integrability
public import CoarseDeGiorgi.Harnack.Crossover.ScalarPremises
public import CoarseDeGiorgi.Harnack.Scalar.Bombieri
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ChiParam
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Crossover

open Homogenization MeasureTheory

noncomputable section

/-- Cancel the two logarithmic normalizations in the product of the positive
and negative power averages. The hypothesis bounds are the scalar integral
outputs that the Bombieri estimate `l.bombieri` supplies. -/
theorem crossover_product_bound_of_centered_integral_bounds {d : ℕ}
    (U : Vec d → ℝ) (pC K : ℝ)
    (hK : 0 ≤ K)
    (_hUpos : ∀ᵐ x ∂(volume.restrict
      (originCube (d := d) (7 / 8))), 0 < U x)
    (hplusInt : IntegrableOn (fun x => U x ^ pC)
      (originCube (d := d) (7 / 8)))
    (hminusInt : IntegrableOn (fun x => U x ^ (-pC))
      (originCube (d := d) (7 / 8)))
    (hplus0 : 0 ≤ ∫ x in originCube (d := d) (3 / 4),
      Real.exp (-pC * volumeAverage (originCube (d := d) (7 / 8))
        (fun y => Real.log (U y))) * U x ^ pC)
    (hplus : (∫ x in originCube (d := d) (3 / 4),
      Real.exp (-pC * volumeAverage (originCube (d := d) (7 / 8))
        (fun y => Real.log (U y))) * U x ^ pC) ≤ K)
    (hminus0 : 0 ≤ ∫ x in originCube (d := d) (3 / 4),
      Real.exp (pC * volumeAverage (originCube (d := d) (7 / 8))
        (fun y => Real.log (U y))) * U x ^ (-pC))
    (hminus : (∫ x in originCube (d := d) (3 / 4),
      Real.exp (pC * volumeAverage (originCube (d := d) (7 / 8))
        (fun y => Real.log (U y))) * U x ^ (-pC)) ≤ K) :
    volumeAverage (originCube (d := d) (3 / 4))
        (fun x => U x ^ pC) *
      volumeAverage (originCube (d := d) (3 / 4))
        (fun x => U x ^ (-pC)) ≤
        ((volume (originCube (d := d) (3 / 4))).toReal⁻¹ * K) ^ 2 := by
  let V₃ : Set (Vec d) := originCube (d := d) (3 / 4)
  let V₇ : Set (Vec d) := originCube (d := d) (7 / 8)
  let ℓ : ℝ := volumeAverage V₇ (fun y => Real.log (U y))
  let kp : ℝ := Real.exp (-pC * ℓ)
  let km : ℝ := Real.exp (pC * ℓ)
  let Iplus : ℝ := ∫ x in V₃, U x ^ pC
  let Iminus : ℝ := ∫ x in V₃, U x ^ (-pC)
  let ν : ℝ := (volume V₃).toReal⁻¹
  have hkp : 0 < kp := Real.exp_pos _
  have hkm : 0 < km := Real.exp_pos _
  have hcancel : kp * km = 1 := by
    dsimp [kp, km]
    rw [← Real.exp_add]
    rw [show -pC * ℓ + pC * ℓ = 0 by ring, Real.exp_zero]
  have hVsub : V₃ ⊆ V₇ :=
    Harnack.Scalar.originCube_subset_of_le (by norm_num)
  have hIplusInt : Integrable (fun x => U x ^ pC) (volume.restrict V₃) :=
    hplusInt.mono_set hVsub
  have hIminusInt : Integrable (fun x => U x ^ (-pC)) (volume.restrict V₃) :=
    hminusInt.mono_set hVsub
  have hplusFactor : (∫ x in V₃, kp * U x ^ pC) = kp * Iplus := by
    change (∫ x, kp * U x ^ pC ∂volume.restrict V₃) =
      kp * ∫ x, U x ^ pC ∂volume.restrict V₃
    exact integral_const_mul_of_integrable hIplusInt
  have hminusFactor : (∫ x in V₃, km * U x ^ (-pC)) = km * Iminus := by
    change (∫ x, km * U x ^ (-pC) ∂volume.restrict V₃) =
      km * ∫ x, U x ^ (-pC) ∂volume.restrict V₃
    exact integral_const_mul_of_integrable hIminusInt
  have hplus0' : 0 ≤ kp * Iplus := by
    rw [← hplusFactor]
    simpa [V₃, V₇, ℓ, kp] using hplus0
  have hminus0' : 0 ≤ km * Iminus := by
    rw [← hminusFactor]
    simpa [V₃, V₇, ℓ, km] using hminus0
  have hplus' : kp * Iplus ≤ K := by
    calc
      kp * Iplus = ∫ x in V₃, kp * U x ^ pC := hplusFactor.symm
      _ ≤ K := by simpa [V₃, V₇, ℓ, kp] using hplus
  have hminus' : km * Iminus ≤ K := by
    calc
      km * Iminus = ∫ x in V₃, km * U x ^ (-pC) := hminusFactor.symm
      _ ≤ K := by simpa [V₃, V₇, ℓ, km] using hminus
  have hweighted : (kp * Iplus) * (km * Iminus) ≤ K ^ 2 := by
    calc
      (kp * Iplus) * (km * Iminus) ≤ K * K :=
        mul_le_mul hplus' hminus' hminus0' hK
      _ = K ^ 2 := by rw [pow_two]
  have hproduct : Iplus * Iminus ≤ K ^ 2 := by
    calc
      Iplus * Iminus = 1 * (Iplus * Iminus) := by ring
      _ = (kp * km) * (Iplus * Iminus) := by rw [← hcancel]
      _ = (kp * Iplus) * (km * Iminus) := by ring
      _ ≤ K ^ 2 := hweighted
  have hmeanPlus : volumeAverage V₃ (fun x => U x ^ pC) = ν * Iplus := by
    rfl
  have hmeanMinus : volumeAverage V₃ (fun x => U x ^ (-pC)) = ν * Iminus := by
    rfl
  change volumeAverage V₃ (fun x => U x ^ pC) *
      volumeAverage V₃ (fun x => U x ^ (-pC)) ≤ (ν * K) ^ 2
  rw [hmeanPlus, hmeanMinus]
  calc
    (ν * Iplus) * (ν * Iminus) = ν ^ 2 * (Iplus * Iminus) := by ring
    _ ≤ ν ^ 2 * K ^ 2 := mul_le_mul_of_nonneg_left hproduct (sq_nonneg ν)
    _ = (ν * K) ^ 2 := by ring

end

end CoarseDeGiorgi.Harnack.Crossover
