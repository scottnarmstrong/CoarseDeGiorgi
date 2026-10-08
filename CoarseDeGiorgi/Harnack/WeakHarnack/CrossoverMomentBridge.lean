module

public import CoarseDeGiorgi.Statements.NormalizedLpMoment
public import CoarseDeGiorgi.Harnack.Calculus.Moments
public import CoarseDeGiorgi.Harnack.CrossoverFinal.EnnrealAverage

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.WeakHarnack

/-- Convert the source product bound for real volume averages of the `p`th
powers into the product bound for the normalized moments `normalizedLpMoment`. -/
theorem normalized_crossover_product_bound {d : ℕ}
    (V : Set (Vec d)) (f g : Vec d → ℝ) (p K : ℝ)
    (hp : 0 < p)
    (hVpos : 0 < volume V) (hVtop : volume V < ⊤)
    (hf_nonneg : 0 ≤ᵐ[volume.restrict V] f)
    (hg_nonneg : 0 ≤ᵐ[volume.restrict V] g)
    (hf_int : IntegrableOn (fun x => f x ^ p) V)
    (hg_int : IntegrableOn (fun x => g x ^ p) V)
    (havg : volumeAverage V (fun x => f x ^ p) *
        volumeAverage V (fun x => g x ^ p) ≤ Real.exp K) :
    normalizedLpMoment p hp V f * normalizedLpMoment p hp V g ≤
      ENNReal.ofReal (Real.exp (K / p)) := by
  let A : ℝ≥0∞ := (volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (f x ^ p)
  let B : ℝ≥0∞ := (volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (g x ^ p)
  have hf_pow_nonneg : 0 ≤ᵐ[volume.restrict V] (fun x => f x ^ p) := by
    filter_upwards [hf_nonneg] with x hx
    exact Real.rpow_nonneg hx p
  have hg_pow_nonneg : 0 ≤ᵐ[volume.restrict V] (fun x => g x ^ p) := by
    filter_upwards [hg_nonneg] with x hx
    exact Real.rpow_nonneg hx p
  have hA : A = ENNReal.ofReal (volumeAverage V (fun x => f x ^ p)) := by
    dsimp [A]
    exact CoarseDeGiorgi.Harnack.CrossoverFinal.ennrealAverage_eq_ofReal_volumeAverage
      V hVtop hVpos (fun x => f x ^ p) hf_int hf_pow_nonneg
  have hB : B = ENNReal.ofReal (volumeAverage V (fun x => g x ^ p)) := by
    dsimp [B]
    exact CoarseDeGiorgi.Harnack.CrossoverFinal.ennrealAverage_eq_ofReal_volumeAverage
      V hVtop hVpos (fun x => g x ^ p) hg_int hg_pow_nonneg
  have havgA : 0 ≤ volumeAverage V (fun x => f x ^ p) := by
    rw [volumeAverage]
    exact mul_nonneg (inv_nonneg.mpr (ENNReal.toReal_nonneg))
      (integral_nonneg_of_ae hf_pow_nonneg)
  have hprodAB : A * B ≤ ENNReal.ofReal (Real.exp K) := by
    rw [hA, hB]
    have hmul :
        ENNReal.ofReal (volumeAverage V (fun x => f x ^ p)) *
            ENNReal.ofReal (volumeAverage V (fun x => g x ^ p)) =
          ENNReal.ofReal
            (volumeAverage V (fun x => f x ^ p) *
              volumeAverage V (fun x => g x ^ p)) :=
      (ENNReal.ofReal_mul havgA).symm
    calc
      ENNReal.ofReal (volumeAverage V (fun x => f x ^ p)) *
          ENNReal.ofReal (volumeAverage V (fun x => g x ^ p))
          = ENNReal.ofReal
              (volumeAverage V (fun x => f x ^ p) *
                volumeAverage V (fun x => g x ^ p)) := hmul
      _ ≤ ENNReal.ofReal (Real.exp K) :=
        ENNReal.ofReal_le_ofReal havg
  have hf_pointwise : ∀ᵐ x ∂volume.restrict V,
      (ENNReal.ofReal |f x|) ^ p = ENNReal.ofReal (f x ^ p) := by
    filter_upwards [hf_nonneg] with x hx
    rw [abs_of_nonneg hx, ENNReal.ofReal_rpow_of_nonneg hx hp.le]
  have hg_pointwise : ∀ᵐ x ∂volume.restrict V,
      (ENNReal.ofReal |g x|) ^ p = ENNReal.ofReal (g x ^ p) := by
    filter_upwards [hg_nonneg] with x hx
    rw [abs_of_nonneg hx, ENNReal.ofReal_rpow_of_nonneg hx hp.le]
  have hf_lintegral :
      ∫⁻ x in V, (ENNReal.ofReal |f x|) ^ p =
        ∫⁻ x in V, ENNReal.ofReal (f x ^ p) :=
    lintegral_congr_ae hf_pointwise
  have hg_lintegral :
      ∫⁻ x in V, (ENNReal.ofReal |g x|) ^ p =
        ∫⁻ x in V, ENNReal.ofReal (g x ^ p) :=
    lintegral_congr_ae hg_pointwise
  have hmomentF : normalizedLpMoment p hp V f = A ^ (1 / p) := by
    rw [CoarseDeGiorgi.Harnack.Calculus.normalizedLpMoment_eq_literal_integral,
      hf_lintegral]
  have hmomentG : normalizedLpMoment p hp V g = B ^ (1 / p) := by
    rw [CoarseDeGiorgi.Harnack.Calculus.normalizedLpMoment_eq_literal_integral,
      hg_lintegral]
  have hroot_nonneg : 0 ≤ 1 / p := by positivity
  have hexp_nonneg : 0 ≤ Real.exp K := (Real.exp_pos K).le
  calc
    normalizedLpMoment p hp V f * normalizedLpMoment p hp V g =
        (A * B) ^ (1 / p) := by
          rw [hmomentF, hmomentG, ENNReal.mul_rpow_of_nonneg A B hroot_nonneg]
    _ ≤ (ENNReal.ofReal (Real.exp K)) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hprodAB hroot_nonneg
    _ = ENNReal.ofReal ((Real.exp K) ^ (1 / p)) :=
      ENNReal.ofReal_rpow_of_nonneg hexp_nonneg hroot_nonneg
    _ = ENNReal.ofReal (Real.exp (K / p)) := by
      congr 1
      rw [Real.rpow_def_of_pos (Real.exp_pos K)]
      simp only [Real.log_exp]
      ring_nf

end CoarseDeGiorgi.Harnack.WeakHarnack
