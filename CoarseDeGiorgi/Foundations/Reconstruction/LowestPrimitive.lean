module

public import CoarseDeGiorgi.Foundations.Reconstruction.FineKernelBounds
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # Normalized periodic density and its mean-zero primitive -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The one-dimensional density of the lowest smoothing block. -/
def lowestDensity (m : ℤ) (t : ℝ) : ℝ :=
  periodicRho (d := 1) m (auxSide m) (fun _ => t)

theorem lowestDensity_eq (m : ℤ) (t : ℝ) :
    lowestDensity m t = scaledEta (auxSide m) (wrapCoordinate m t) := by
  simp only [lowestDensity, periodicRho, scaledRho_eq_prod, wrapBox, Fin.prod_univ_one]

theorem contDiff_lowestDensity (m : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (lowestDensity m) := by
  exact (contDiff_periodicRho (d := 1) (auxSide_pos m) le_rfl).comp
    (contDiff_pi.mpr fun _ => contDiff_id)

theorem periodic_lowestDensity (m : ℤ) : Function.Periodic (lowestDensity m) (2 * auxSide m) := by
  intro t
  simp only [lowestDensity_eq, wrapCoordinate_add_period]

/-- Integral one on the ordinary, unnormalized period interval. -/
theorem integral_lowestDensity (m : ℤ) :
    ∫ t in Set.Icc (-auxSide m) (auxSide m), lowestDensity m t ∂volume = 1 := by
  have hηzero (t : ℝ) (ht : auxSide m / 2 < |t|) : scaledEta (auxSide m) t = 0 := by
    have hzero := scaledRho_eq_zero_of_norm_gt (d := 1) (auxSide_pos m)
      (x := fun _ => t) (by
        have hn : |t| ≤ ‖(fun _ : Fin 1 => t)‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun _ : Fin 1 => t) 0
        exact ht.trans_le hn)
    simpa only [scaledRho_eq_prod, Fin.prod_univ_one] using hzero
  have heq : (∫ t in Set.Icc (-auxSide m) (auxSide m), lowestDensity m t ∂volume) =
      ∫ t in Set.Icc (-auxSide m) (auxSide m), scaledEta (auxSide m) t ∂volume := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    rw [lowestDensity_eq, wrapCoordinate_eq_self m (abs_lt.mpr ht)]
  rw [heq, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_scaledEta (auxSide_pos m)
  · intro t ht
    apply hηzero
    have hn : auxSide m < |t| := by
      contrapose! ht
      exact ⟨(abs_le.mp ht).1, (abs_le.mp ht).2⟩
    exact lt_trans (by linarith [auxSide_pos m]) hn

/-- The constant density with the same period integral. -/
def lowestMeanDensity (m : ℤ) : ℝ := (2 * auxSide m)⁻¹

/-- The primitive is defined on the entire line; periodicity follows from zero mean. -/
def lowestPrimitive (m : ℤ) (t : ℝ) : ℝ :=
  ∫ s in (-auxSide m)..t, (lowestDensity m s - lowestMeanDensity m)

theorem hasDerivAt_lowestPrimitive (m : ℤ) (t : ℝ) :
    HasDerivAt (lowestPrimitive m) (lowestDensity m t - lowestMeanDensity m) t := by
  have hc : Continuous (fun s => lowestDensity m s - lowestMeanDensity m) :=
    (contDiff_lowestDensity m).continuous.sub continuous_const
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem contDiff_lowestPrimitive (m : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (lowestPrimitive m) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨?_, ?_⟩
  · exact fun t => (hasDerivAt_lowestPrimitive m t).differentiableAt
  · have heq : deriv (lowestPrimitive m) = fun t => lowestDensity m t - lowestMeanDensity m :=
      funext fun t => (hasDerivAt_lowestPrimitive m t).deriv
    rw [heq]
    exact (contDiff_lowestDensity m).sub contDiff_const

/-- The primitive closes exactly at the period endpoints. -/
theorem periodic_lowestPrimitive (m : ℤ) :
    Function.Periodic (lowestPrimitive m) (2 * auxSide m) := by
  have hc : Continuous (fun t => lowestDensity m t - lowestMeanDensity m) :=
    (contDiff_lowestDensity m).continuous.sub continuous_const
  have hp : Function.Periodic (fun t => lowestDensity m t - lowestMeanDensity m)
      (2 * auxSide m) := fun t => by
        change lowestDensity m (t + 2 * auxSide m) - _ = lowestDensity m t - _
        rw [(periodic_lowestDensity m) t]
  have hzero : (∫ t in (-auxSide m)..(-auxSide m + 2 * auxSide m),
      (lowestDensity m t - lowestMeanDensity m)) = 0 := by
    rw [show -auxSide m + 2 * auxSide m = auxSide m by ring,
      intervalIntegral.integral_sub ((contDiff_lowestDensity m).continuous.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const]
    rw [intervalIntegral.integral_of_le (by linarith [auxSide_pos m]),
      Measure.restrict_congr_set Ioc_ae_eq_Icc, integral_lowestDensity]
    simp only [lowestMeanDensity, smul_eq_mul]
    have hn : 2 * auxSide m ≠ 0 := (mul_pos (by norm_num) (auxSide_pos m)).ne'
    rw [show auxSide m - -auxSide m = 2 * auxSide m by ring, mul_inv_cancel₀ hn, sub_self]
  intro t
  change (∫ s in (-auxSide m)..(t + 2 * auxSide m), _) = _
  rw [hp.intervalIntegral_add_eq_add (-auxSide m) t (fun a b => hc.intervalIntegrable a b),
    hzero, add_zero]
  rfl

end

end CoarseDeGiorgi.Foundations.Reconstruction
