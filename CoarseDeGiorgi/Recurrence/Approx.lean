import CoarseDeGiorgi.Selection.SourceNonnegative
import CoarseDeGiorgi.Assembly.HybridFractional
import CoarseDeGiorgi.Statements.H1aWeightedNorm
import CoarseDeGiorgi.Statements.IsSmoothCore
import CoarseDeGiorgi.Statements.MemH1a

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.Recurrence

/-- Convergence in `L¹` and in energy gives convergence of the weighted `H¹_a` norm. -/
theorem h1aWeightedNorm_tendsto_of_l1_energy {d : ℕ} (a : CoeffField d)
    (w : ℕ → Vec d → ℝ) (G : ℕ → Vec d → Vec d)
    (hL1 : Tendsto (fun i => eLpNorm (w i) 1 (volume.restrict (originCube (d := d) 1)))
      atTop (𝓝 0))
    (hE : Tendsto (fun i => weightedEnergy a (originCube (d := d) 1) (G i)) atTop (𝓝 0)) :
    Tendsto (fun i => h1aWeightedNorm a (originCube 1) (w i) (G i)) atTop (𝓝 0) := by
  let V := originCube (d := d) 1
  have hmean : Tendsto (fun i => ENNReal.ofReal ((volumeAverage V (w i)) ^ 2)) atTop (𝓝 0) := by
    have hbound : ∀ i, ENNReal.ofReal ((volumeAverage V (w i)) ^ 2) ≤
        (ENNReal.ofReal ((volume V).toReal⁻¹) * eLpNorm (w i) 1 (volume.restrict V)) ^ (2 : ℕ) := by
      intro i
      have h1 : ENNReal.ofReal |volumeAverage V (w i)| ≤
          ENNReal.ofReal ((volume V).toReal⁻¹) * eLpNorm (w i) 1 (volume.restrict V) := by
        unfold volumeAverage
        have hv0 : 0 ≤ (volume V).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
        rw [abs_mul, abs_of_nonneg hv0, ENNReal.ofReal_mul hv0]
        refine mul_le_mul' le_rfl ?_
        by_cases hm : AEStronglyMeasurable (w i) (volume.restrict V)
        swap
        · rw [integral_non_aestronglyMeasurable hm]; simp
        rw [eLpNorm_one_eq_lintegral_enorm hm]
        have h := enorm_integral_le_lintegral_enorm (μ := volume.restrict V) (w i)
        rw [Real.enorm_eq_ofReal_abs] at h
        exact h
      calc ENNReal.ofReal ((volumeAverage V (w i)) ^ 2)
          = ENNReal.ofReal |volumeAverage V (w i)| ^ 2 := by
            rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _)]
        _ ≤ _ := pow_le_pow_left' h1 2
    have hlim : Tendsto (fun i => (ENNReal.ofReal ((volume V).toReal⁻¹) *
        eLpNorm (w i) 1 (volume.restrict V)) ^ (2 : ℕ)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((volume V).toReal⁻¹)) hL1 (Or.inr ENNReal.ofReal_ne_top)
      have h2 := ((ENNReal.continuous_pow 2).tendsto (ENNReal.ofReal ((volume V).toReal⁻¹) * 0)).comp h
      simpa [Function.comp_def] using h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) hbound
  unfold h1aWeightedNorm
  have hsum : Tendsto (fun i => ENNReal.ofReal ((volumeAverage V (w i)) ^ 2) +
      weightedEnergy a V (G i)) atTop (𝓝 0) := by simpa using hmean.add hE
  have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hsum
  simpa [Function.comp_def] using this

/-- Nonnegative smooth approximation in the weighted `H¹_a` norm of the unit cube. -/
theorem smooth_approx {d : ℕ} [NeZero d] (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a (originCube 1) w G)
    (hnn : ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)), 0 ≤ w x) :
    ∃ vi : ℕ → Vec d → ℝ, (∀ i, IsSmoothCore a (originCube 1) (vi i)) ∧
      (∀ i, ∀ x ∈ originCube (d := d) 1, 0 ≤ vi i x) ∧
      Tendsto (fun i => h1aWeightedNorm a (originCube 1)
        (fun x => vi i x - w x) (fun x => smoothGrad (vi i) x - G x)) atTop (𝓝 0) := by
  have hunit := Assembly.hybrid_unitCube_domain (d := d)
  obtain ⟨f, hf, hL1, hE⟩ := Selection.source_nonnegative_approximation hunit.1 hunit.2 ha hw hnn
  exact ⟨f, fun i => (hf i).1, fun i x _ => (hf i).2 x,
    h1aWeightedNorm_tendsto_of_l1_energy a (fun i => f i - w) (fun i => smoothGrad (f i) - G)
      hL1 hE⟩

end CoarseDeGiorgi.Recurrence
