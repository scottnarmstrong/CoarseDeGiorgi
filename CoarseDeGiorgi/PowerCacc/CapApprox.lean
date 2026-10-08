import CoarseDeGiorgi.Assembly.LocalBoundedness
import CoarseDeGiorgi.Harnack.Selection.Cap
import CoarseDeGiorgi.Weighted.Truncation.Chain
import CoarseDeGiorgi.Weighted.Truncation.Continuity
import CoarseDeGiorgi.Weighted.Truncation.Energy
import CoarseDeGiorgi.Weighted.Identification
import CoarseDeGiorgi.GoodRadius.TruncationTransfer
import CoarseDeGiorgi.Statements.PositiveCap
import CoarseDeGiorgi.Statements.H1aWeightedNorm

/-! # Capped smooth approximants converge to the cap in `H¹_a`

If smooth cores `v_i` converge to `v` in `H¹_a(□₀)` then `v_i ∧ N` converges to `v ∧ N`, in `L¹` and
in energy of the gradients (Proposition `p.weighted.calculus`, chain rule), for a finite cap `N`. -/

namespace CoarseDeGiorgi.PowerCacc

open Homogenization MeasureTheory Filter Topology Set
open scoped ENNReal

variable {d : ℕ}

theorem energy_neg_eq {V : Set (Vec d)} (a : CoeffField d) (G : Vec d → Vec d) :
    weightedEnergy a V (-G) = weightedEnergy a V G := by
  unfold weightedEnergy
  congr 1
  funext x
  simp only [Pi.neg_apply, matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]

/-- The finite-cap gradient is the difference of two positive-part gradients, almost everywhere. -/
theorem capGradient_ae_eq [NeZero d] {a : CoeffField d}
    (ha : IsWeightedCoeffOn (originCube 1) a) {f : Vec d → ℝ} {F : Vec d → Vec d}
    (hf : MemH1a a (originCube 1) f F) {N : ℝ≥0∞} (hN : N ≠ 0) (hNtop : N ≠ ⊤) :
    Harnack.Selection.selectionCapGradient 0 N f F =ᵐ[volume.restrict (originCube 1)]
      ({x | 0 < f x}.indicator F - {x | N.toReal < f x}.indicator F) := by
  let hV := Assembly.hybrid_unitCube_domain (d := d)
  have hNr : 0 < N.toReal := ENNReal.toReal_pos hN hNtop
  have hzero := Weighted.MemH1a.gradient_zero_on_level hV.1 hV.2 ha hf N.toReal
  filter_upwards [hzero] with x hx
  have hgd : Harnack.Selection.selectionCapGradient 0 N f F x =
      {x | 0 < f x ∧ f x < 0 + N.toReal}.indicator F x := by
    simp only [Harnack.Selection.selectionCapGradient, ite_eq_right hNtop]
  rw [hgd]
  simp only [Pi.sub_apply, indicator_apply, mem_ofPred_eq, zero_add]
  by_cases hlo : 0 < f x
  · by_cases heq : f x = N.toReal
    · have hz : F x = 0 := by simpa [heq] using hx
      simp [heq, hz]
    · by_cases hhi : N.toReal < f x
      · simp [hlo, hhi, not_lt_of_gt hhi]
      · have hlt : f x < N.toReal := lt_of_le_of_ne (le_of_not_gt hhi) heq
        simp [hlo, hhi, hlt]
  · have : ¬ N.toReal < f x := by linarith [hNr, not_lt.mp hlo]
    simp [hlo, this]

theorem cap_eq_capMap (N : ℝ≥0∞) (hNtop : N ≠ ⊤) (v : Vec d → ℝ) :
    Harnack.Selection.selectionCap 0 N v = fun x => GoodRadius.capMap 0 N (v x) := by
  funext x
  simp [Harnack.Selection.selectionCap, GoodRadius.capMap, hNtop]

theorem capMap_lipschitzWith (N : ℝ≥0∞) : LipschitzWith 1 (GoodRadius.capMap 0 N) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simpa [Real.dist_eq] using GoodRadius.capMap_lipschitz 0 N x y

/-- The capped smooth approximants converge to the cap of the limit, in `L¹` and in energy of the
(finite-cap) gradients. -/
theorem cap_approx_tendsto [NeZero d] {a : CoeffField d}
    (ha : IsWeightedCoeffOn (originCube 1) a) {v : Vec d → ℝ} {H : Vec d → Vec d}
    (hv : MemH1a a (originCube 1) v H)
    (vi : ℕ → Vec d → ℝ) (hvi : ∀ i, IsSmoothCore a (originCube 1) (vi i))
    (hL1 : Tendsto (fun i => eLpNorm (vi i - v) 1 (volume.restrict (originCube 1)))
      atTop (𝓝 0))
    (hE : Tendsto (fun i => weightedEnergy a (originCube 1) (smoothGrad (vi i) - H))
      atTop (𝓝 0))
    {N : ℝ≥0∞} (hN : N ≠ 0) (hNtop : N ≠ ⊤) :
    (∀ i, MemH1a a (originCube 1) (Harnack.Selection.selectionCap 0 N (vi i))
      (Harnack.Selection.selectionCapGradient 0 N (vi i) (smoothGrad (vi i)))) ∧
    Tendsto (fun i => eLpNorm (Harnack.Selection.selectionCap 0 N (vi i) -
      Harnack.Selection.selectionCap 0 N v) 1 (volume.restrict (originCube 1)))
      atTop (𝓝 0) ∧
    Tendsto (fun i => weightedEnergy a (originCube 1)
      (Harnack.Selection.selectionCapGradient 0 N (vi i) (smoothGrad (vi i)) -
        Harnack.Selection.selectionCapGradient 0 N v H)) atTop (𝓝 0) := by
  let hV := Assembly.hybrid_unitCube_domain (d := d)
  have hmem (i : ℕ) : MemH1a a (originCube 1) (vi i) (smoothGrad (vi i)) :=
    Weighted.memH1a_of_isSmoothCore hV.1.isOpen ha (hvi i)
  have hNr : 0 < N.toReal := ENNReal.toReal_pos hN hNtop
  refine ⟨fun i => Harnack.Selection.selectionCap_memH1a a ha (hmem i) 0 N hN, ?_, ?_⟩
  · have hmeas (i : ℕ) : AEStronglyMeasurable (vi i) (volume.restrict (originCube 1)) :=
      (hmem i).1
    have h := Weighted.tendsto_l1_lipschitz_comp hmeas hv.1 hL1 (capMap_lipschitzWith N)
    simp only [cap_eq_capMap N hNtop]
    exact h
  · have hpos := Weighted.tendsto_energy_positivePart hV.1 hV.2 ha hmem hv hL1 hE 0
    have hN' := Weighted.tendsto_energy_positivePart hV.1 hV.2 ha hmem hv hL1 hE N.toReal
    have hmeasF (i : ℕ) : AEStronglyMeasurable
        ({x | N.toReal < vi i x}.indicator (smoothGrad (vi i)) -
          {x | N.toReal < v x}.indicator H) (volume.restrict (originCube 1)) := by
      have hm1 : AEStronglyMeasurable ({x | N.toReal < vi i x}.indicator (smoothGrad (vi i)))
          (volume.restrict (originCube 1)) := by
        have := (hmem i).2.1
        exact this.indicator₀ (nullMeasurableSet_lt aemeasurable_const (hmem i).1.aemeasurable)
      have hm2 : AEStronglyMeasurable ({x | N.toReal < v x}.indicator H)
          (volume.restrict (originCube 1)) :=
        hv.2.1.indicator₀ (nullMeasurableSet_lt aemeasurable_const hv.1.aemeasurable)
      exact hm1.sub hm2
    have hneg : Tendsto (fun i => weightedEnergy a (originCube 1)
        (-({x | N.toReal < vi i x}.indicator (smoothGrad (vi i)) -
          {x | N.toReal < v x}.indicator H))) atTop (𝓝 0) := by
      simpa only [energy_neg_eq] using hN'
    have hmeasA (i : ℕ) : AEStronglyMeasurable
        ({x | 0 < vi i x}.indicator (smoothGrad (vi i)) -
          {x | 0 < v x}.indicator H) (volume.restrict (originCube 1)) := by
      have hm1 : AEStronglyMeasurable ({x | 0 < vi i x}.indicator (smoothGrad (vi i)))
          (volume.restrict (originCube 1)) :=
        (hmem i).2.1.indicator₀ (nullMeasurableSet_lt aemeasurable_const (hmem i).1.aemeasurable)
      have hm2 : AEStronglyMeasurable ({x | 0 < v x}.indicator H)
          (volume.restrict (originCube 1)) :=
        hv.2.1.indicator₀ (nullMeasurableSet_lt aemeasurable_const hv.1.aemeasurable)
      exact hm1.sub hm2
    have hsum := Weighted.tendsto_energy_add_zero ha hmeasA hpos hneg
    have hae (i : ℕ) :
        Harnack.Selection.selectionCapGradient 0 N (vi i) (smoothGrad (vi i)) -
          Harnack.Selection.selectionCapGradient 0 N v H =ᵐ[volume.restrict (originCube 1)]
        ({x | 0 < vi i x}.indicator (smoothGrad (vi i)) -
          {x | 0 < v x}.indicator H) +
        (-({x | N.toReal < vi i x}.indicator (smoothGrad (vi i)) -
          {x | N.toReal < v x}.indicator H)) := by
      filter_upwards [capGradient_ae_eq ha (hmem i) hN hNtop,
        capGradient_ae_eq ha hv hN hNtop] with x h1 h2
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at h1 h2 ⊢
      rw [h1, h2]
      abel
    refine hsum.congr fun i => ?_
    exact (Weighted.energy_congr_ae (hae i)).symm

/-- `L¹` and energy convergence give convergence in the `H¹_a` norm of `p.good.radius`. -/
theorem h1aWeightedNorm_tendsto_zero {a : CoeffField d} {w : ℕ → Vec d → ℝ}
    {G : ℕ → Vec d → Vec d}
    (hmeas : ∀ i, AEStronglyMeasurable (w i) (volume.restrict (originCube 1)))
    (hL1 : Tendsto (fun i => eLpNorm (w i) 1 (volume.restrict (originCube 1))) atTop (𝓝 0))
    (hE : Tendsto (fun i => weightedEnergy a (originCube 1) (G i)) atTop (𝓝 0)) :
    Tendsto (fun i => h1aWeightedNorm a (originCube 1) (w i) (G i)) atTop (𝓝 0) := by
  set c : ℝ≥0∞ := ENNReal.ofReal ((volume (originCube (d := d) 1)).toReal⁻¹) with hc
  have hX : Tendsto (fun i => (c * eLpNorm (w i) 1 (volume.restrict (originCube 1))) ^ 2)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun i => c * eLpNorm (w i) 1 (volume.restrict (originCube 1)))
        atTop (𝓝 (c * 0)) :=
      ENNReal.Tendsto.const_mul hL1 (Or.inr (by simp [hc]))
    have h2 := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp h1
    simpa [Function.comp_def] using h2
  have hsum : Tendsto (fun i => (c * eLpNorm (w i) 1 (volume.restrict (originCube 1))) ^ 2 +
      weightedEnergy a (originCube 1) (G i)) atTop (𝓝 0) := by
    simpa using hX.add hE
  have hrpow : Tendsto (fun i => ((c * eLpNorm (w i) 1 (volume.restrict (originCube 1))) ^ 2 +
      weightedEnergy a (originCube 1) (G i)).rpow (1 / 2)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hsum
    simpa only [Function.comp_def, ENNReal.rpow_eq_pow,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrpow
    (fun _ => bot_le) fun i => ?_
  unfold h1aWeightedNorm
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  refine add_le_add_left ?_ _
  have h1 : ENNReal.ofReal ((volumeAverage (originCube 1) (w i)) ^ 2) =
      ‖volumeAverage (originCube 1) (w i)‖ₑ ^ 2 := by
    rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.enorm_eq_ofReal_abs]
  rw [h1]
  gcongr
  unfold volumeAverage
  rw [enorm_mul]
  refine mul_le_mul' (le_of_eq ?_) ?_
  · rw [hc, Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity)]
  · rw [eLpNorm_one_eq_lintegral_enorm (hmeas i)]
    exact MeasureTheory.enorm_integral_le_lintegral_enorm _

end CoarseDeGiorgi.PowerCacc
