import CoarseDeGiorgi.Endpoint.Capacitary.Bounds
import CoarseDeGiorgi.Endpoint.Source.Extension
import Mathlib.MeasureTheory.Measure.Regular

/-! A lower bound for the potential functional on the capacitary test. -/

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Set Topology
open CoarseDeGiorgi.Weighted
open scoped ENNReal

variable {d : ℕ} [NeZero d]

/-- A positive interior lower bound on a nonnegative zero-boundary test bounds the
potential functional below by the mass supported in that interior. -/
theorem capacitary_functional_lower (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (hν : ν (originCube (3 / 4))ᶜ = 0)
    {V ψ : Vec d → ℝ} {Gv Gψ : Vec d → Vec d}
    (hV : MemH1a0 a (originCube 1) V Gv)
    (heq : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ originCube 1 →
      ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) = ∫ x, φ x ∂ν)
    (hψ : MemH1a0 a (originCube 1) ψ Gψ)
    (hψ0 : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ ψ x)
    (c : ℝ) (hc : 0 ≤ c)
    (hψW : ∀ᵐ x ∂volume.restrict (originCube (3 / 4)), c ≤ ψ x) :
    ENNReal.ofReal c * ν univ ≤
      ENNReal.ofReal (∫ x in originCube 1, vecDot (Gψ x) (matVecMul (a x) (Gv x))) := by
  have hO := originCube_domain (d := d) one_pos
  have hne := originCube_nonempty (d := d) one_pos
  have hW := originCube_domain (d := d) (by norm_num : (0 : ℝ) < 3 / 4)
  have hWO : originCube (d := d) (3 / 4) ⊆ originCube 1 :=
    originCube_mono' (by norm_num) one_pos (by norm_num)
  have hVm := Weighted.MemH1a0.memH1a ha hV
  have hEV := Weighted.MemH1a.energy_lt_top hO.isOpen ha hVm
  have hpositive {g : Vec d → ℝ} {H : Vec d → Vec d}
      (hg : MemH1a0 a (originCube 1) g H)
      (hg0 : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ g x) :
      0 ≤ ∫ x in originCube 1, vecDot (H x) (matVecMul (a x) (Gv x)) :=
    (nonneg_pairing hO hne ha (μ := ν) le_rfl (fun K _ _ => measure_lt_top ν K)
      hVm.2.1 hEV hVm.2.1 hEV (fun φ h1 h2 h3 => (heq φ h1 h2 h3).symm)
      heq hg hg0).1
  have hcompact (K : Set (Vec d)) (hKW : K ⊆ originCube (3 / 4)) (hK : IsCompact K) :
      ENNReal.ofReal c * ν K ≤
        ENNReal.ofReal (∫ x in originCube 1, vecDot (Gψ x) (matVecMul (a x) (Gv x))) := by
    obtain ⟨φ, hφ, hφc, hφs, hφ01, hφK⟩ := exists_cutoff01 hW.isOpen hK hKW
    have hφm := memH1a0_of_supported hO.isOpen ha hφ hφc (hφs.trans hWO)
    have hdiff := Weighted.MemH1a0.sub hO hne ha hψ
      (capacitary_memH1a0_smul hO hne ha hφm c)
    have hdiff0 : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ (ψ - c • φ) x := by
      have hlow := (ae_restrict_iff' hW.isOpen.measurableSet).mp hψW
      have hlowO : ∀ᵐ x ∂volume.restrict (originCube 1), x ∈ originCube (3 / 4) → c ≤ ψ x :=
        ae_mono Measure.restrict_le_self hlow
      filter_upwards [hψ0, hlowO] with x hx0 hxc
      change 0 ≤ ψ x - c * φ x
      by_cases hxW : x ∈ originCube (3 / 4)
      · have hmul := mul_le_mul_of_nonneg_left (hφ01 x).2 hc
        rw [mul_one] at hmul
        linarith only [hxc hxW, hmul]
      · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hx => hxW (hφs hx)
        rw [hz, mul_zero, sub_zero]
        exact hx0
    have hnonneg := hpositive hdiff hdiff0
    let P := memH1aEnergyField hO.isOpen ha (Weighted.MemH1a0.memH1a ha hψ)
    let T := memH1aEnergyField hO.isOpen ha (Weighted.MemH1a0.memH1a ha hφm)
    let X := memH1aEnergyField hO.isOpen ha hVm
    have hinner : 0 ≤ inner ℝ ((P - c • T : GradientCore ha) : GradientHilbert ha)
        (X : GradientHilbert ha) := by
      rw [gradientHilbert_inner_coe]
      exact hnonneg
    rw [UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_smul,
      inner_sub_left, real_inner_smul_left, gradientHilbert_inner_coe,
      gradientHilbert_inner_coe] at hinner
    change 0 ≤ (∫ x in originCube 1, vecDot (Gψ x) (matVecMul (a x) (Gv x))) -
      c * (∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x))) at hinner
    rw [heq φ hφ hφc (hφs.trans hWO)] at hinner
    have hφint : Integrable φ ν := hφ.continuous.integrable_of_hasCompactSupport hφc
    have hmass : (ν K).toReal ≤ ∫ x, φ x ∂ν := by
      change ν.real K ≤ _
      rw [← integral_indicator_one hK.measurableSet]
      apply integral_mono_ae ((integrable_const (1 : ℝ)).indicator hK.measurableSet) hφint
      filter_upwards with x
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK, hφK x hxK]
      · rw [indicator_of_notMem hxK]
        exact (hφ01 x).1
    calc
      _ = ENNReal.ofReal (c * (ν K).toReal) := by
        rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal (measure_ne_top ν K)]
      _ ≤ ENNReal.ofReal (c * ∫ x, φ x ∂ν) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmass hc)
      _ ≤ _ := ENNReal.ofReal_le_ofReal (sub_nonneg.mp hinner)
  have hmass : ν univ = ν (originCube (3 / 4)) := by
    have h := measure_add_measure_compl hW.isOpen.measurableSet (μ := ν)
    simpa only [hν, add_zero] using h.symm
  rw [hmass, hW.isOpen.measure_eq_iSup_isCompact ν]
  simp only [ENNReal.mul_iSup]
  exact iSup_le fun K => iSup_le fun hKW => iSup_le fun hK => hcompact K hKW hK

end CoarseDeGiorgi.Endpoint
