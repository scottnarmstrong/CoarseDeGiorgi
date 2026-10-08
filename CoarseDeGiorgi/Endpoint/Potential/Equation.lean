import CoarseDeGiorgi.Endpoint.Potential.Cutoff
import CoarseDeGiorgi.Endpoint.Potential.Truncation
import CoarseDeGiorgi.Weighted.TestingApproximation
import CoarseDeGiorgi.Weighted.HarmonicCore
import CoarseDeGiorgi.Weighted.TestingNonnegative

namespace CoarseDeGiorgi.Endpoint.Potential

open Homogenization MeasureTheory Filter Topology CoarseDeGiorgi CoarseDeGiorgi.Weighted
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The potential equation, tested against a bounded zero-boundary pair, is bounded by the mass. -/
theorem pairing_le_of_potential (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    {v : Vec d → ℝ} {Gv : Vec d → Vec d} (hv : MemH1a0 a V v Gv)
    (heq : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V →
      ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume = ∫ x, φ x ∂ν)
    {g : Vec d → ℝ} {Gg : Vec d → Vec d} (hg : MemH1a0 a V g Gg) {K : ℝ} (hK : 0 < K)
    (hgK : ∀ x, |g x| ≤ K) :
    |∫ x in V, vecDot (Gg x) (matVecMul (a x) (Gv x))| ≤ 2 * K * ν.real Set.univ := by
  let F := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hv)
  let Kf := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hg)
  obtain ⟨f, hf, hr, hL, hE⟩ := Weighted.MemH1a0.comp_approximation hV hne ha hg
    (phiCut_contDiff K) (phiCut_zero K) (L := 1) (abs_deriv_phiCut_le K)
  have hGg : (fun x => deriv (phiCut K) (g x) • Gg x) = Gg := by
    funext x
    rw [deriv_phiCut, psiCut_eq_one hK (hgK x), one_smul]
  rw [hGg] at hE
  have hE' : Tendsto (fun n => weightedEnergy a V (smoothGrad (f n) - Gg)) atTop (𝓝 0) := hE
  have hcore := fun n => isSmoothCore_of_supported ha (hf n).1 (hf n).2.1
  have htG : Tendsto (fun n => (smoothEnergyField hV.isOpen ha (hcore n) : GradientHilbert ha))
      atTop (𝓝 (Kf : GradientHilbert ha)) := GradientCore.tendsto_coe_of_energy ha
        (F := fun n => smoothEnergyField hV.isOpen ha (hcore n)) (G := Kf) hE'
  have htI := htG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := (F : GradientHilbert ha)))
  have hle (n : ℕ) : |inner ℝ (smoothEnergyField hV.isOpen ha (hcore n) : GradientHilbert ha)
      (F : GradientHilbert ha)| ≤ 2 * K * ν.real Set.univ := by
    rw [gradientHilbert_inner_coe]
    have h1 := heq (f n) (hf n).1 (hf n).2.1 (hf n).2.2
    change |∫ x in V, vecDot (smoothGrad (f n) x) (matVecMul (a x) (Gv x))| ≤ _
    rw [h1]
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := f n) (C := 2 * K)
      (Eventually.of_forall fun x => by
        obtain ⟨t, ht⟩ := hr n x
        rw [ht, Real.norm_eq_abs]; exact phiCut_abs_le hK t)
    simpa [Real.norm_eq_abs] using this
  have hlim : |inner ℝ (Kf : GradientHilbert ha) (F : GradientHilbert ha)| ≤
      2 * K * ν.real Set.univ :=
    le_of_tendsto htI.abs (Eventually.of_forall hle)
  rw [gradientHilbert_inner_coe] at hlim
  exact hlim

/-- The truncation energy bound `ℰ(v ∧ K) ≤ K ν(□₀)`, up to the constant `2`. -/
theorem truncation_energy_le (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (ν : Measure (Vec d)) [IsFiniteMeasure ν] (hν : ν Vᶜ = 0)
    {v : Vec d → ℝ} {Gv : Vec d → Vec d} (hv : MemH1a0 a V v Gv)
    (heq : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V →
      ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume = ∫ x, φ x ∂ν)
    {K : ℝ} (hK : 0 < K) :
    weightedEnergy a V ({x | |v x| < K}.indicator Gv) ≤ ENNReal.ofReal (2 * K) * ν V := by
  have hg := Weighted.MemH1a0.truncation hV hne ha hv hK
  have hgK : ∀ x, |Weighted.truncate K (v x)| ≤ K := by
    intro x
    rw [abs_le]
    unfold Weighted.truncate
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hp := pairing_le_of_potential hV hne ha ν hv heq hg hK hgK
  have hEfin : weightedEnergy a V ({x | |v x| < K}.indicator Gv) < ⊤ :=
    (Weighted.energy_truncate_le ha v Gv K).trans_lt
      (MemH1a.energy_lt_top hV.isOpen ha (Weighted.MemH1a0.memH1a ha hv))
  have hpt : ∀ x, vecDot ({x | |v x| < K}.indicator Gv x)
      (matVecMul (a x) ({x | |v x| < K}.indicator Gv x)) =
      vecDot ({x | |v x| < K}.indicator Gv x) (matVecMul (a x) (Gv x)) := by
    intro x
    by_cases h : |v x| < K
    · simp [Set.indicator_of_mem (show x ∈ {x | |v x| < K} from h)]
    · simp [Set.indicator_of_notMem (show x ∉ {x | |v x| < K} from h), vecDot, matVecMul]
  have hreal : (weightedEnergy a V ({x | |v x| < K}.indicator Gv)).toReal ≤
      2 * K * ν.real Set.univ := by
    rw [Weighted.energy_toReal ha hg.2.1]
    simp_rw [hpt]
    exact (le_abs_self _).trans hp
  have hν1 : ν Set.univ = ν V := by
    have := measure_add_measure_compl (μ := ν) hV.isOpen.measurableSet
    rw [hν, add_zero] at this
    exact this.symm
  calc weightedEnergy a V ({x | |v x| < K}.indicator Gv)
      = ENNReal.ofReal (weightedEnergy a V ({x | |v x| < K}.indicator Gv)).toReal :=
        (ENNReal.ofReal_toReal hEfin.ne).symm
    _ ≤ ENNReal.ofReal (2 * K * ν.real Set.univ) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (2 * K) * ν V := by
        rw [ENNReal.ofReal_mul (by linarith), Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
          hν1]

end CoarseDeGiorgi.Endpoint.Potential
