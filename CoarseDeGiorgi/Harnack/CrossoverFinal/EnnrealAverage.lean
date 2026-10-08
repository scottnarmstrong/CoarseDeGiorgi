import CoarseDeGiorgi.Harnack.Crossover.Integrability
import CoarseDeGiorgi.Harnack.Crossover.ScalarPremises
import CoarseDeGiorgi.Harnack.Scalar.Bombieri
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ChiParam
import CoarseDeGiorgi.Statements.IsWeightedSupersolution

namespace CoarseDeGiorgi.Harnack.CrossoverFinal

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- Convert a normalized real integral to the normalized ENNReal integral used by
the crossover statement. -/
theorem ennrealAverage_eq_ofReal_volumeAverage {d : ℕ}
    (V : Set (Vec d)) (hVfin : volume V < ⊤) (hVpos : 0 < volume V)
    (f : Vec d → ℝ) (hf : IntegrableOn f V)
    (hfn : 0 ≤ᵐ[volume.restrict V] f) :
    (volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (f x) =
      ENNReal.ofReal (volumeAverage V f) := by
  have hrealVolumePos : 0 < (volume V).toReal :=
    ENNReal.toReal_pos hVpos.ne' hVfin.ne
  have hvolume : ENNReal.ofReal ((volume V).toReal) = volume V :=
    ENNReal.ofReal_toReal hVfin.ne
  have hcoeff : (volume V)⁻¹ = ENNReal.ofReal ((volume V).toReal⁻¹) := by
    calc
      (volume V)⁻¹ = (ENNReal.ofReal ((volume V).toReal))⁻¹ := by rw [hvolume]
      _ = ENNReal.ofReal ((volume V).toReal⁻¹) :=
        (ENNReal.ofReal_inv_of_pos hrealVolumePos).symm
  have hlintegral : ENNReal.ofReal (∫ x in V, f x) =
      ∫⁻ x in V, ENNReal.ofReal (f x) :=
    ofReal_integral_eq_lintegral_ofReal hf hfn
  calc
    (volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (f x) =
        ENNReal.ofReal ((volume V).toReal⁻¹) *
          ENNReal.ofReal (∫ x in V, f x) := by rw [hcoeff, ← hlintegral]
    _ = ENNReal.ofReal ((volume V).toReal⁻¹ * ∫ x in V, f x) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hrealVolumePos.le)]
    _ = ENNReal.ofReal (volumeAverage V f) := by rw [volumeAverage]

/-- Lift a product bound for two real averages to the normalized ENNReal moments
appearing in the crossover conclusion. -/
theorem ennrealAverage_product_le_of_volumeAverage_product {d : ℕ}
    (V : Set (Vec d)) (hVfin : volume V < ⊤) (hVpos : 0 < volume V)
    (f g : Vec d → ℝ) (hf : IntegrableOn f V) (hg : IntegrableOn g V)
    (hfn : 0 ≤ᵐ[volume.restrict V] f)
    (hgn : 0 ≤ᵐ[volume.restrict V] g) (C : ℝ) (_hC : 0 ≤ C)
    (hproduct : volumeAverage V f * volumeAverage V g ≤ C) :
    ((volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (f x)) *
      ((volume V)⁻¹ * ∫⁻ x in V, ENNReal.ofReal (g x)) ≤ ENNReal.ofReal C := by
  rw [ennrealAverage_eq_ofReal_volumeAverage V hVfin hVpos f hf hfn,
    ennrealAverage_eq_ofReal_volumeAverage V hVfin hVpos g hg hgn]
  have hrealVolumePos : 0 < (volume V).toReal :=
    ENNReal.toReal_pos hVpos.ne' hVfin.ne
  have hIntf : 0 ≤ ∫ x in V, f x := integral_nonneg_of_ae hfn
  have hIntg : 0 ≤ ∫ x in V, g x := integral_nonneg_of_ae hgn
  have havgf : 0 ≤ volumeAverage V f := by
    rw [volumeAverage]
    exact mul_nonneg (inv_nonneg.mpr hrealVolumePos.le) hIntf
  calc
    ENNReal.ofReal (volumeAverage V f) * ENNReal.ofReal (volumeAverage V g) =
        ENNReal.ofReal (volumeAverage V f * volumeAverage V g) :=
      (ENNReal.ofReal_mul havgf).symm
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hproduct

end

end CoarseDeGiorgi.Harnack.CrossoverFinal
