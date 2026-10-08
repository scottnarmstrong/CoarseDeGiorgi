import CoarseDeGiorgi.Weighted.Truncation.Continuity
import CoarseDeGiorgi.Weighted.TestingCompactSupport
import CoarseDeGiorgi.Weighted.HarmonicCore
import CoarseDeGiorgi.Weighted.TestingApproximation

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

theorem truncate_lipschitz (N : ℝ) : LipschitzWith 1 (truncate N) := by
  have h := (LipschitzWith.id.min_const N).max_const (-N)
  convert h using 1
  ext t
  simp only [truncate, id, max_comm]

/-- Energy convergence of strict truncation gradients. -/
theorem tendsto_energy_truncate (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {f : ℕ → Vec d → ℝ} {F : ℕ → Vec d → Vec d}
    (hf : ∀ n, CoarseDeGiorgi.MemH1a a V (f n) (F n))
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : CoarseDeGiorgi.MemH1a a V u G)
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (hE : Tendsto (fun n => weightedEnergy a V (F n - G)) atTop (𝓝 0)) {N : ℝ} (hN : 0 < N) :
    Tendsto (fun n => weightedEnergy a V
      ({x | |f n x| < N}.indicator (F n) - {x | |u x| < N}.indicator G)) atTop (𝓝 0) := by
  have h1 := tendsto_energy_positivePart hV hne ha hf hu ht hE (-N)
  have h2 := tendsto_energy_positivePart hV hne ha hf hu ht hE N
  have hmeas : ∀ (v : Vec d → ℝ) (H : Vec d → Vec d) (c : ℝ),
      AEStronglyMeasurable v (volume.restrict V) →
      AEStronglyMeasurable H (volume.restrict V) →
      AEStronglyMeasurable ({x | c < v x}.indicator H) (volume.restrict V) := by
    intro v H c hv hH
    exact hH.indicator₀ (nullMeasurableSet_lt aemeasurable_const hv.aemeasurable)
  have h2' : Tendsto (fun n => weightedEnergy a V
      (-({x | N < f n x}.indicator (F n) - {x | N < u x}.indicator G))) atTop (𝓝 0) := by
    simpa only [energy_neg] using h2
  have hs := tendsto_energy_add_zero ha
    (fun n => (hmeas _ _ _ (hf n).1 (hf n).2.1).sub (hmeas _ _ _ hu.1 hu.2.1)) h1 h2'
  convert hs using 2 with n
  apply energy_congr_ae
  filter_upwards [truncation_gradient_ae hV hne ha (hf n) hN,
    truncation_gradient_ae hV hne ha hu hN] with x hx1 hx2
  have e1 := hx1
  have e2 := hx2
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at e1 e2 ⊢
  rw [← e1, ← e2]
  abel

/-- Truncation preserves the zero-boundary space, with the strict truncation gradient. -/
theorem MemH1a0.truncation (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a0 a V u G) {N : ℝ} (hN : 0 < N) :
    MemH1a0 a V (fun x => truncate N (u x)) ({x | |u x| < N}.indicator G) := by
  obtain ⟨f, hf, -, hL, hE⟩ := MemH1a0.comp_approximation hV hne ha hu
    (Φ := id) contDiff_id rfl (L := 1) (by simp)
  have hL' : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0) := by
    simpa using hL
  have hE' : Tendsto (fun n => weightedEnergy a V (smoothGrad (f n) - G)) atTop (𝓝 0) := by
    simpa [deriv_id''] using hE
  have hfm : ∀ n, CoarseDeGiorgi.MemH1a a V (f n) (smoothGrad (f n)) := fun n =>
    (memH1a0_of_supported hV.isOpen ha (hf n).1 (hf n).2.1 (hf n).2.2).memH1a ha
  have hpair : ∀ n, MemH1a0 a V (fun x => truncate N (f n x))
      ({x | |f n x| < N}.indicator (smoothGrad (f n))) := by
    intro n
    refine MemH1a.memH1a0_of_compact_support hV hne ha
      (MemH1a.truncation hV hne ha (hfm n) hN) (hf n).2.1.isCompact (hf n).2.2 ?_
    filter_upwards with x hx
    have h0 : f n x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [truncate, h0, hN.le]
  have hwu := hu.memH1a ha
  have hi := (memH1a_memW11 hV hne ha hwu).1
  have hint : IntegrableOn (fun x => truncate N (u x)) V :=
    integrableOn_lipschitz_comp hV hi (truncate_lipschitz N)
  have hGM : AEStronglyMeasurable ({x | |u x| < N}.indicator G) (volume.restrict V) :=
    hu.2.1.indicator₀ (nullMeasurableSet_lt
      (continuous_abs.comp_aestronglyMeasurable hu.1).aemeasurable aemeasurable_const)
  refine memH1a0_of_tendsto hV hne ha hpair hint hGM ?_
    (tendsto_energy_truncate hV hne ha hfm hwu hL' hE' hN)
  simpa only [Function.comp_def] using
    tendsto_l1_lipschitz_comp (fun n => (hfm n).1) hu.1 hL' (truncate_lipschitz N)

end CoarseDeGiorgi.Weighted
