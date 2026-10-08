import CoarseDeGiorgi.Statements.H1aWeightedNorm
import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.LowerFractional.NormBounds
import CoarseDeGiorgi.LowerFractional.CompactCover
import CoarseDeGiorgi.Weighted.Identification
import CoarseDeGiorgi.Weighted.PairOperations
import CoarseDeGiorgi.Foundations.PoincareW11Mean

namespace CoarseDeGiorgi.Harnack.WeakHarnack

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

private theorem tendsto_toReal_zero {f : ℕ → ℝ≥0∞}
    (hf : Tendsto f atTop (𝓝 (0 : ℝ≥0∞))) :
    Tendsto (fun i => (f i).toReal) atTop (𝓝 (0 : ℝ)) := by
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hf

/-- A vanishing squared-mean-plus-energy norm gives value-L¹ convergence for
represented weighted Sobolev pairs. The mean-zero weighted Poincaré estimate
controls the oscillation; the norm controls the remaining mean. -/
theorem h1aWeightedNorm_tendsto_l1_and_energy {d : ℕ} [NeZero d]
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (w : ℕ → Vec d → ℝ) (G : ℕ → Vec d → Vec d)
    (hw : ∀ i, MemH1a a (originCube 1) (w i) (G i))
    (hN : Tendsto (fun i => h1aWeightedNorm a (originCube 1) (w i) (G i))
      atTop (𝓝 0)) :
    Tendsto (fun i => eLpNorm (w i) 1 (volume.restrict (originCube 1)))
        atTop (𝓝 0) ∧
      Tendsto (fun i => weightedEnergy a (originCube 1) (G i))
        atTop (𝓝 0) := by
  let V := originCube (d := d) 1
  have hV : IsOpenBoundedConvexDomain V := LowerFractional.lower_unitCube_domain
  have hne : V.Nonempty := LowerFractional.lower_unitCube_nonempty
  have : IsFiniteMeasure (volume.restrict V) :=
    hV.isBoundedDomain.isFiniteMeasure_restrict_volume
  obtain ⟨C, hC, hPoincare⟩ := Foundations.exists_mean_zero_poincare_w11 hV hne
  let T := Real.sqrt (∫ x in V, ((a x)⁻¹).trace)
  have hMeanN : Tendsto
      (fun i => ‖volumeAverage V (w i)‖ₑ) atTop (𝓝 (0 : ℝ≥0∞)) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hN
      (fun _ => bot_le)
      (fun i => LowerFractional.lower_weighted_mean_norm_le a V (w i) (G i))
  have hEnergyRoot : Tendsto
      (fun i => (weightedEnergy a V (G i)) ^ (1 / 2 : ℝ)) atTop
        (𝓝 (0 : ℝ≥0∞)) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hN
      (fun _ => bot_le)
      (fun i => LowerFractional.lower_weighted_energy_norm_le a V (w i) (G i))
  have hEnergyRootReal : Tendsto
      (fun i => Real.sqrt (weightedEnergy a V (G i)).toReal) atTop
        (𝓝 (0 : ℝ)) := by
    have h := tendsto_toReal_zero hEnergyRoot
    simpa only [← ENNReal.toReal_rpow, Real.sqrt_eq_rpow] using h
  have hEnergy : Tendsto (fun i => weightedEnergy a V (G i)) atTop
      (𝓝 (0 : ℝ≥0∞)) := by
    have hsq :=
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp
        hEnergyRoot
    have heq : (fun i => ((weightedEnergy a V (G i)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) =
        fun i => weightedEnergy a V (G i) := by
      funext i
      rw [← ENNReal.rpow_mul]
      norm_num
    have hzero : (0 : ℝ≥0∞) ^ (2 : ℝ) = 0 := by norm_num
    simpa only [Function.comp_def, heq, hzero] using hsq
  have hMeanAbs : Tendsto
      (fun i => |volumeAverage V (w i)|) atTop (𝓝 (0 : ℝ)) := by
    have h := tendsto_toReal_zero hMeanN
    simpa only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using h
  have hUpper : Tendsto
      (fun i => C * (T * Real.sqrt (weightedEnergy a V (G i)).toReal) +
        (volume V).toReal * |volumeAverage V (w i)|)
      atTop (𝓝 (0 : ℝ)) := by
    have hfirst : Tendsto
        (fun i => C * (T * Real.sqrt (weightedEnergy a V (G i)).toReal))
        atTop (𝓝 0) := by
      simpa using (hEnergyRootReal.const_mul T).const_mul C
    have hsecond : Tendsto
        (fun i => (volume V).toReal * |volumeAverage V (w i)|)
        atTop (𝓝 0) := by
      simpa using hMeanAbs.const_mul (volume V).toReal
    simpa using hfirst.add hsecond
  have hIntegral : Tendsto (fun i => ∫ x in V, |w i x|) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    · intro i
      exact integral_nonneg fun x => abs_nonneg (w i x)
    · intro i
      have hW := Weighted.memH1a_memW11 hV hne ha (hw i)
      have hEtop := Weighted.MemH1a.energy_lt_top hV.isOpen ha (hw i)
      have hgrad := Weighted.gradient_length_integrable_and_bound ha (hw i).2.1 hEtop
      have hP := hPoincare (w i) (G i) hW.1 hW.2.1 hW.2.2.1
      have hcenter : IntegrableOn (fun x => |w i x - volumeAverage V (w i)|) V :=
        (hW.1.sub (integrable_const _)).abs
      have htriangle : (∫ x in V, |w i x|) ≤
          (∫ x in V, |w i x - volumeAverage V (w i)|) +
            (volume V).toReal * |volumeAverage V (w i)| := by
        rw [← show (∫ x in V, |volumeAverage V (w i)|) =
          (volume V).toReal * |volumeAverage V (w i)| by
            simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
              smul_eq_mul]]
        rw [← integral_add hcenter (integrable_const _)]
        apply integral_mono_ae hW.1.abs (hcenter.add (integrable_const _))
        filter_upwards with x
        simpa only [sub_add_cancel, Pi.add_apply] using
          abs_add_le (w i x - volumeAverage V (w i)) (volumeAverage V (w i))
      calc
        (∫ x in V, |w i x|) ≤
            C * (∫ x in V, Real.sqrt (vecDot (G i x) (G i x))) +
              (volume V).toReal * |volumeAverage V (w i)| :=
          htriangle.trans (add_le_add hP le_rfl)
        _ ≤ C * (T * Real.sqrt (weightedEnergy a V (G i)).toReal) +
              (volume V).toReal * |volumeAverage V (w i)| :=
          add_le_add (mul_le_mul_of_nonneg_left hgrad.2 hC) le_rfl
  have hL1 : Tendsto (fun i => eLpNorm (w i) 1 (volume.restrict V))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    have heq : (fun i => eLpNorm (w i) 1 (volume.restrict V)) =
        fun i => ENNReal.ofReal (∫ x in V, |w i x|) := by
      funext i
      exact Weighted.l1_eq_ofReal_integral_abs
        (Weighted.memH1a_memW11 hV hne ha (hw i)).1
    rw [heq]
    change Tendsto (ENNReal.ofReal ∘ (fun i => ∫ x in V, |w i x|))
      atTop (𝓝 (0 : ℝ≥0∞))
    simpa only [ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hIntegral)
  exact ⟨hL1, hEnergy⟩

end
end CoarseDeGiorgi.Harnack.WeakHarnack
