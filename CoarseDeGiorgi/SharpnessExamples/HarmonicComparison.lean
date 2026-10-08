module

public import CoarseDeGiorgi.Weighted.HarmonicProperties
public import CoarseDeGiorgi.Weighted.Testing
public import CoarseDeGiorgi.Weighted.TestingApproximation
public import CoarseDeGiorgi.Weighted.TestingNonnegative

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted
open scoped ENNReal NNReal

namespace CoarseDeGiorgi.SharpnessExamples

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The positive part of a zero-boundary weighted Sobolev function has zero
boundary values, with the strict-positive-set indicator as its gradient. -/
theorem zeroBoundary_posPart (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a0 a V u G) :
    MemH1a0 a V (fun x => max (u x) 0) ({x | 0 < u x}.indicator G) := by
  let μ := volume.restrict V
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  let f : ℕ → Vec d → ℝ := fun n => GApprox 0 (δ n) ∘ u
  let F : ℕ → Vec d → Vec d := fun n x => gStep 0 (δ n) (u x) • G x
  let H : Vec d → Vec d := {x | 0 < u x}.indicator G
  let χ : Vec d → ℝ := fun x => if 0 < u x then 1 else 0
  let Φ : ℝ → ℝ := fun t => max t 0
  let : IsFiniteMeasure μ := hV.isFiniteMeasure_restrict_volume
  have hδpos : ∀ n, 0 < δ n := by intro n; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h2δ : Tendsto (fun n => 2 * δ n) atTop (𝓝 0) := by
    simpa using hδ.const_mul 2
  have hu' : MemH1a a V u G := Weighted.MemH1a0.memH1a ha hu
  have huI : IntegrableOn u V volume := (memH1a_memW11 hV hne ha hu').1
  have hΦlip : LipschitzWith 1 Φ :=
    (show LipschitzWith 1 (fun t : ℝ => t) from by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      rfl).max_const 0
  have hplusI : IntegrableOn (Φ ∘ u) V volume :=
    integrableOn_lipschitz_comp hV huI hΦlip
  have hfmeas (n : ℕ) : AEStronglyMeasurable (f n) μ :=
    (GApprox_contDiff_top 0 (δ n)).continuous.comp_aestronglyMeasurable hu.1
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    ((gStep_continuous 0 (δ n)).comp_aestronglyMeasurable hu.1).smul hu.2.1
  have hGApproxLip (n : ℕ) : LipschitzWith 1 (GApprox 0 (δ n)) :=
    lipschitzWith_of_nnnorm_deriv_le (C := 1)
      ((GApprox_contDiff_top 0 (δ n)).differentiable (by simp)) (fun t =>
        NNReal.coe_le_coe.mp (by
          simpa only [coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one] using
            abs_deriv_GApprox_le 0 (δ n) t))
  have hfint (n : ℕ) : IntegrableOn (f n) V volume :=
    integrableOn_lipschitz_comp hV huI (hGApproxLip n)
  have hfn : ∀ n, MemH1a0 a V (f n) (F n) := by
    intro n
    obtain ⟨fn, hfn, _, hL, hE⟩ := MemH1a0.comp_approximation hV hne ha hu
      (GApprox_contDiff_top 0 (δ n)) (by simp [GApprox])
      (L := 1) (abs_deriv_GApprox_le 0 (δ n))
    have hE' : Tendsto (fun k => weightedEnergy a V
        (smoothGrad (fn k) - F n)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, deriv_GApprox, F] using hE
    exact memH1a0_of_supported_tendsto hV ha hfn (hfint n) (hFmeas n) hL hE'
  have hbase : MemLp u 1 μ := memLp_one_iff_integrable.mpr huI
  have hfuniform : UnifIntegrable f 1 μ := by
    apply (unifIntegrable_const (by norm_num) (by norm_num) hbase).ae_mono hfmeas
    intro n
    filter_upwards with x
    simpa only [f, Real.enorm_eq_ofReal_abs, Function.comp_apply, sub_zero] using
      ENNReal.ofReal_le_ofReal (abs_GApprox_le (c := 0) (δ n) (u x))
  have hflim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (Φ (u x))) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h2δ
    simpa only [f, Φ, Real.norm_eq_abs, Function.comp_apply, sub_zero] using
      abs_GApprox_sub_le (c := 0) (hδpos n) (u x)
  have hvalue : Tendsto (fun n => eLpNorm (f n - Φ ∘ u) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hfmeas
      (memLp_one_iff_integrable.mpr hplusI) hfuniform (Eventually.of_forall hflim)
  have hχM : AEStronglyMeasurable χ μ := by
    exact aestronglyMeasurable_const.indicator₀
      (nullMeasurableSet_lt measurable_const.aemeasurable hu.1.aemeasurable)
  have hHM : AEStronglyMeasurable H μ := hu.2.1.indicator₀
      (nullMeasurableSet_lt measurable_const.aemeasurable hu.1.aemeasurable)
  have hχG : (fun x => χ x • G x) = H := by
    funext x
    by_cases hx : 0 < u x <;> simp [χ, H, hx]
  have henergy : Tendsto (fun n => weightedEnergy a V (F n - H)) atTop (𝓝 0) := by
    have ht := tendsto_energy_mul_zero ha hu.2.1
      (MemH1a.energy_lt_top hV.isOpen ha hu')
      (b := fun n x => gStep 0 (δ n) (u x) - χ x)
      (fun n => ((gStep_continuous 0 (δ n)).comp_aestronglyMeasurable hu.1).sub hχM)
      (M := 1) (fun n => ?_) ?_
    · convert ht using 1
      funext n
      apply energy_congr_ae
      filter_upwards with x
      have hHx : H x = χ x • G x := (congrFun hχG x).symm
      change gStep 0 (δ n) (u x) • G x - H x =
        (gStep 0 (δ n) (u x) - χ x) • G x
      rw [hHx]
      exact (sub_smul _ _ _).symm
    · filter_upwards with x
      have h0 := gStep_nonneg 0 (δ n) (u x)
      have h1 := gStep_le_one 0 (δ n) (u x)
      dsimp [χ]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith only [h0, h1]
    · filter_upwards with x
      simpa [χ] using (tendsto_gStep (c := 0) hδpos hδ (u x)).sub_const (χ x)
  exact memH1a0_of_tendsto hV hne ha hfn hplusI hHM hvalue henergy

/-- A weighted subsolution lies below the harmonic replacement of its own
boundary data. -/
theorem subsolution_le_harmonic_replacement
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : IsWeightedSubsolution a V v G) :
    ∃ U : Vec d → ℝ, ∃ GU : Vec d → Vec d,
      IsWeightedSolution a V U GU ∧
      MemH1a0 a V (U - v) (GU - G) ∧
      v ≤ᵐ[volume.restrict V] U := by
  obtain ⟨U, GU, hU, hU0, _, _, _⟩ :=
    Weighted.harmonic_replacement hV hne ha hv.1
  have hboundary : MemH1a0 a V (v - U) (G - GU) := by
    have hneg := Weighted.MemH1a0.neg hV hne ha hU0
    have huv : -(U - v) = v - U := by
      funext x
      simp only [Pi.neg_apply, Pi.sub_apply]
      ring
    have hgu : -(GU - G) = G - GU := by
      funext x
      simp only [Pi.neg_apply, Pi.sub_apply]
      ring
    simpa only [huv, hgu] using hneg
  have hg := zeroBoundary_posPart hV hne ha hboundary
  have htest := Weighted.IsWeightedSubsolution.testing hV hne ha hv hg
    (Eventually.of_forall fun x => le_max_right (v x - U x) 0)
  have horth := Weighted.IsWeightedSolution.orthogonality hV hne ha hU hg
  let H : Vec d → Vec d := {x | 0 < (v - U) x}.indicator (G - GU)
  have hcross : (∫ x in V, vecDot (H x) (matVecMul (a x) (G x - GU x))) =
      (∫ x in V, vecDot (H x) (matVecMul (a x) (G x))) -
        (∫ x in V, vecDot (H x) (matVecMul (a x) (GU x))) := by
    calc
      _ = ∫ x in V, (vecDot (H x) (matVecMul (a x) (G x)) -
          vecDot (H x) (matVecMul (a x) (GU x))) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg,
          vecDot_add_right, vecDot_neg_right]
      _ = _ := integral_sub htest.1 horth.1
  have henergyCross : (∫ x in V,
      vecDot (H x) (matVecMul (a x) (G x - GU x))) =
        (weightedEnergy a V H).toReal := by
    have hHM : AEStronglyMeasurable H (volume.restrict V) := hg.2.1
    rw [Weighted.energy_toReal ha hHM]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : 0 < v x - U x
    · have hx' : U x < v x := by linarith
      simp [H, hx']
    · have hx' : ¬ U x < v x := by
        intro h
        linarith
      simp [H, hx', matVecMul_zero, vecDot_zero_left]
  have htest' : (∫ x in V, vecDot (H x) (matVecMul (a x) (G x))) ≤ 0 := by
    simpa only [H] using htest.2
  have horth' : (∫ x in V, vecDot (H x) (matVecMul (a x) (GU x))) = 0 := by
    simpa only [H] using horth.2
  have henergyReal : (weightedEnergy a V H).toReal ≤ 0 := by
    calc
      _ = (∫ x in V, vecDot (H x) (matVecMul (a x) (G x))) -
          (∫ x in V, vecDot (H x) (matVecMul (a x) (GU x))) := by
        rw [← henergyCross, hcross]
      _ = _ := by rw [horth']; simp
      _ ≤ 0 := htest'
  have henergyZero : weightedEnergy a V H = 0 := by
    have hwg := Weighted.MemH1a0.memH1a ha hg
    have hfinite := Weighted.MemH1a.energy_lt_top hV.isOpen ha hwg
    have hrealZero : (weightedEnergy a V H).toReal = 0 :=
      le_antisymm henergyReal ENNReal.toReal_nonneg
    rcases (ENNReal.toReal_eq_zero_iff _).mp hrealZero with hzero | htop
    · exact hzero
    · exact (hfinite.ne htop).elim
  have hzero := Weighted.MemH1a0.eq_zero_of_energy_zero hV hne ha hg henergyZero
  have hle : (fun x => v x - U x) ≤ᵐ[volume.restrict V] 0 := by
    filter_upwards [hzero.1] with x hx
    exact (max_eq_right_iff.mp hx)
  refine ⟨U, GU, hU, hU0, ?_⟩
  filter_upwards [hle] with x hx
  exact (sub_nonpos.mp hx)

end CoarseDeGiorgi.SharpnessExamples
