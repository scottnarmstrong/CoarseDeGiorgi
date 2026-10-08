module

public import CoarseDeGiorgi.Foundations.Reconstruction.TailActions

/-! # The unconditional tail-bound input for the committed fractional assembly -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction
open Homogenization MeasureTheory Filter
open scoped ENNReal BigOperators Topology
noncomputable section
variable {d : ℕ}

private theorem tail_coefficient_le {B C L ρ q : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hcoef : 2 * B * q ≤ C * L) (N : ℝ≥0∞) :
    2 * ENNReal.ofReal ρ * (ENNReal.ofReal B * (ENNReal.ofReal q * N)) ≤
      (ENNReal.ofReal C * ENNReal.ofReal ρ) * (ENNReal.ofReal L * N) := by
  have he := ENNReal.ofReal_le_ofReal hcoef
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hB), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul hC] at he
  norm_num only [ENNReal.ofReal_ofNat] at he
  calc
    _ = (2 * ENNReal.ofReal B * ENNReal.ofReal q) * ENNReal.ofReal ρ * N := by ring
    _ ≤ (ENNReal.ofReal C * ENNReal.ofReal L) * ENNReal.ofReal ρ * N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he bot_le) bot_le
    _ = _ := by ring

/-- Both tail estimates hold in every dimension, with no gradient Lʳ premise. -/
theorem assemblyTailBounds {α r : ℝ} (hr : 1 < r) : AssemblyTailBounds d α r := by
  obtain ⟨A, hA, hjet⟩ := exists_bound_reconstructionKernel_jets (d := d)
  let D := (Real.sqrt (d : ℝ) + 1) * A * (6 : ℝ) ^ d
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hD : 0 < D := mul_pos (mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one hA)) (by positivity)
  have hfactor : 0 ≤ Real.sqrt (d : ℝ) * A * (6 : ℝ) ^ d := by positivity
  have hfactorD : Real.sqrt (d : ℝ) * A * (6 : ℝ) ^ d ≤ D := by
    dsimp only [D]; gcongr; linarith only [Real.sqrt_nonneg (d : ℝ)]
  refine ⟨6 * D, mul_pos (by norm_num) hD, fun m z w Dw hweak hw hDw _hwLp _hseries j => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hjet m j
  have hh := auxSide_pos (m + j)
  have hK := contDiff_reconstructionKernel (d := d) m j
  have hKi := hK.continuous.measurable.comp (measurable_fst.sub measurable_snd)
  let T := fun k => periodicKernelOperator m (fun x y => reconstructionKernel m j (x - y))
    (reflectedAverage m k z Dw)
  have hTm (k : ℕ) : Measurable (T k) :=
    measurable_periodicKernelOperator m _ _ hKi (measurable_reflectedAverage m k z Dw)
  have hTi (k : ℕ) : IntegrableOn (reflectedAverage m k z Dw) (reflectionBox m) volume :=
    integrableOn_reflectedGradient (memLp_one_iff_integrable.mp (memLp_auxAverage m (m + k) z Dw 1))
  have hlim (x : Vec d) : Tendsto (fun k => T k x) atTop
      (𝓝 (kernelPairing m z (reconstructionKernel m j) Dw x)) :=
    (tendstoUniformly_kernelPairing_reflectedAverage Dw hDw _ hK.continuous (by positivity) h0).tendsto_at x
  have hp : 1 ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  have haction (u : Option (Vec d)) :
      eLpNorm (reconstructionAction u (kernelPairing m z (reconstructionKernel m j) Dw)) (ENNReal.ofReal r)
        (volume.restrict (reflectionBox m)) ≤
      (ENNReal.ofReal (6 * D) * ENNReal.ofReal (reconstructionModulus (auxSide (m + j)) u)) *
        assemblyGradientTail m z Dw r j := by
    apply eLpNorm_telescope_tail_le j (fun k => reconstructionAction u (T k)) _ _ hp
      (volume.restrict (reflectionBox m)) (fun k => ENNReal.ofReal (auxSide (m + k)) * assemblyAverageSize m z Dw r k)
      (ENNReal.ofReal (6 * D) * ENNReal.ofReal (reconstructionModulus (auxSide (m + j)) u))
    · obtain ⟨hb, ht⟩ := reconstruction_operator_bounds m j hA0 hr h0 h1 _
        (measurable_reflectedAverage m j z Dw) (hTi j)
      have h := reconstructionAction_bound u (auxSide (m + j)) (T j) _ _ hb ht
      apply h.trans
      simpa only [ENNReal.ofReal_one, one_mul, mul_one, assemblyAverageSize] using
        tail_coefficient_le (ρ := reconstructionModulus (auxSide (m + j)) u) (q := 1)
          (by positivity) (by positivity : 0 ≤ 6 * D)
          (by nlinarith only [hfactorD, hD, hh]) (assemblyAverageSize m z Dw r j)
    · intro k hjk
      have hk := auxSide_pos (m + k)
      have hkj : auxSide (m + k) ≤ auxSide (m + j) := by
        have h := assembly_side_le (m + j) (k - j)
        simpa only [show m + (j : ℤ) + (k - j : ℕ) = m + k by omega] using h
      obtain ⟨hb, ht⟩ := reconstruction_cancellation_operator_bounds m j hA0 (by positivity : 0 ≤ auxSide (m + k) / 2)
        (by gcongr) hr h1 h2 (reflectedParentCenter m z k) (measurable_reflectedParentCenter m z k)
        (norm_sub_reflectedParentCenter_le m z k)
        (fun y => reflectedAverage m (k + 1) z Dw y - reflectedAverage m k z Dw y)
        ((measurable_reflectedAverage m (k + 1) z Dw).sub (measurable_reflectedAverage m k z Dw))
        (integrableOn_reflectedAverage_increment m z k Dw)
      have heq : (fun x => T (k + 1) x - T k x) = periodicKernelOperator m
          (fun x y => kernelCancellation (reconstructionKernel m j) y (reflectedParentCenter m z k y) x)
          (fun y => reflectedAverage m (k + 1) z Dw y - reflectedAverage m k z Dw y) := by
        funext x
        exact (integral_kernel_reflectedAverage_sub m z k Dw _ hK.continuous x).trans
          (integral_increment_eq_cancellation k Dw hDw _ hK.continuous h0 x)
      rw [← reconstructionAction_sub, heq]
      have h := reconstructionAction_bound u (auxSide (m + j)) _ _ _ hb ht
      apply h.trans
      have hinc := eLpNorm_euclidNorm_reflectedAverage_increment_le m k z Dw hDw _ hp ENNReal.ofReal_ne_top
      have hsides : auxSide (m + k) = 3 * auxSide (m + (k + 1 : ℕ)) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using auxSide_eq_three_mul_next (m + k)
      calc
        _ ≤ 2 * ENNReal.ofReal (reconstructionModulus (auxSide (m + j)) u) *
            (ENNReal.ofReal (Real.sqrt (d : ℝ) * A * (auxSide (m + k) / 2) * (6 : ℝ) ^ d) *
              (ENNReal.ofReal 2 * assemblyAverageSize m z Dw r (k + 1))) := by
          gcongr
          simpa only [ENNReal.ofReal_ofNat, assemblyAverageSize] using hinc
        _ ≤ _ := tail_coefficient_le (by positivity) (by positivity : 0 ≤ 6 * D)
          (by rw [hsides]; nlinarith only [hfactorD, hD, auxSide_pos (m + (k + 1 : ℕ))]) _
    · intro k
      exact (reconstructionAction_measurable u (hTm k)).aestronglyMeasurable
    · intro x
      cases u with
      | none => exact hlim x
      | some u => exact (hlim (x + u)).sub (hlim x)
  have heq : assemblyBlock m z w j = kernelPairing m z (reconstructionKernel m j) Dw := by
    funext x; exact assemblyBlock_eq_reconstructionKernel_pairing hweak hw hDw j x
  rw [heq]
  refine ⟨?_, fun u => ?_⟩
  · simpa only [reconstructionAction, reconstructionModulus, ENNReal.ofReal_one, mul_one] using haction none
  · exact haction (some u)

end
end CoarseDeGiorgi.Foundations.Reconstruction
