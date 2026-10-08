module

public import CoarseDeGiorgi.Foundations.Reconstruction.KernelWeakIdentity

/-! # Exact smooth-block reconstruction identities -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Smoothing uses ordinary integration over the reflected fundamental box. -/
def smoothAverage (m : ℤ) (t : ℝ) (z : Fin d → ℤ) (w : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ y in reflectionBox m, reflectedScalar m z w y * periodicRho m t (x - y) ∂volume

/-- Vector kernel pairing with the reflected weak gradient. -/
def kernelPairing (m : ℤ) (z : Fin d → ℤ) (K : Vec d → Vec d)
    (Dw : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∫ y in reflectionBox m, vecDot (K (x - y)) (reflectedGradient m z Dw y) ∂volume

/-- The fine block is reconstructed exactly from its explicit divergence inverse. -/
theorem smoothAverage_sub_eq_fineKernelPairing {m : ℤ} {h : ℝ} (hh : 0 < h)
    (hsmall : 3 * h ≤ auxSide m) {z : Fin d → ℤ} {w : Vec d → ℝ} {Dw : Vec d → Vec d}
    (hweak : HasWeakGradientOn (auxCube m z) w Dw)
    (hw : IntegrableOn w (auxCube m z) volume)
    (hDw : IntegrableOn Dw (auxCube m z) volume) (x : Vec d) :
    smoothAverage m h z w x - smoothAverage m (3 * h) z w x =
      kernelPairing m z (periodicFineKernel m h) Dw x := by
  have hi (t : ℝ) (ht : 0 < t) (htsmall : t ≤ auxSide m) : IntegrableOn
      (fun y => reflectedScalar m z w y * periodicRho m t (x - y)) (reflectionBox m) volume :=
    integrableOn_reflectionBox_mul_continuous (integrableOn_reflectedScalar hw)
      ((contDiff_periodicRho ht htsmall).continuous.comp (continuous_const.sub continuous_id))
  have heq := kernel_weak_identity hweak hw hDw (periodicFineKernel m h)
    (contDiff_periodicFineKernel hh hsmall) (periodicFineKernel_add_period m h) x
  simp only [vectorDivergence_periodicFineKernel hh hsmall, mul_sub] at heq
  rw [integral_sub (hi h hh (by linarith))
    (hi (3 * h) (by linarith) hsmall)] at heq
  exact heq

/-- The lowest block subtracts the true global mean, rather than a coarse mollifier. -/
theorem smoothAverage_sub_mean_eq_lowestKernelPairing {m : ℤ} {z : Fin d → ℤ}
    {w : Vec d → ℝ} {Dw : Vec d → Vec d}
    (hweak : HasWeakGradientOn (auxCube m z) w Dw)
    (hw : IntegrableOn w (auxCube m z) volume)
    (hDw : IntegrableOn Dw (auxCube m z) volume) (x : Vec d) :
    smoothAverage m (auxSide m) z w x - ((2 * auxSide m) ^ d)⁻¹ *
      (∫ y in reflectionBox m, reflectedScalar m z w y ∂volume) =
        kernelPairing m z (lowestKernel m d) Dw x := by
  have hi : IntegrableOn
      (fun y => reflectedScalar m z w y * periodicRho m (auxSide m) (x - y))
      (reflectionBox m) volume :=
    integrableOn_reflectionBox_mul_continuous (integrableOn_reflectedScalar hw)
      ((contDiff_periodicRho (auxSide_pos m) le_rfl).continuous.comp
        (continuous_const.sub continuous_id))
  have hc := (integrableOn_reflectedScalar hw).mul_const (((2 * auxSide m) ^ d)⁻¹)
  have heq := kernel_weak_identity hweak hw hDw (lowestKernel m d)
    (contDiff_lowestKernel m d) (lowestKernel_add_period m d) x
  simp only [vectorDivergence_lowestKernel_eq_periodicRho, mul_sub] at heq
  rw [integral_sub hi hc, integral_mul_const, mul_comm] at heq
  exact heq

end

end CoarseDeGiorgi.Foundations.Reconstruction
