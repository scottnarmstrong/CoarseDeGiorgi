module

public import CoarseDeGiorgi.Whitney.LiftZeroExtension

/-! # Energy closure of the weighted zero-boundary completion

This is the countable-correction approximation step. Coercivity controls values
as well as gradients; the completion supplies literal `MemH1a0` pairs.
-/

@[expose] public section

namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Uniform scalar L¹ coercivity on all zero-boundary pairs (`MemH1a0`). -/
lemma lift_zero_boundary_l1_bound (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u G, MemH1a0 a V u G →
      (∫ x in V, |u x|) ≤ C * Real.sqrt (weightedEnergy a V G).toReal := by
  obtain ⟨C₀, hC₀, hp⟩ := Foundations.exists_zero_boundary_poincare_w11
    hV.isOpen hV.isBoundedDomain.isBounded
  let T := Real.sqrt (∫ x in V, ((a x)⁻¹).trace)
  refine ⟨C₀ * T, mul_nonneg hC₀ (Real.sqrt_nonneg _), ?_⟩
  intro u G hu
  have hw := Weighted.memH1a_memW11 hV hne ha (Weighted.MemH1a0.memH1a ha hu)
  obtain ⟨huM, hGM, φ, hφ, hc, hl, hE⟩ := hu
  have hcore (n : ℕ) := Weighted.isSmoothCore_of_supported ha (hφ n).1 (hφ n).2.1
  have hL := (Weighted.core_tendsto_l1 hV hne ha hcore hc huM hl).2
  have hcoords := fun i => Weighted.tendsto_coord_l1_of_energy ha
    (fun n => Weighted.smoothGrad_aestronglyMeasurable hV.isOpen (hcore n).1)
    hGM (fun n => (hcore n).2.2) hE i
  have hP := hp u G φ hw.1 hw.2.1 (fun n => (hφ n).1)
    (fun n => (hφ n).2.1) (fun n => (hφ n).2.2) hL hcoords
  have hgrad := Weighted.gradient_length_integrable_and_bound ha hGM hw.2.2.2.2
  calc
    _ ≤ C₀ * (∫ x in V, Real.sqrt (vecDot (G x) (G x))) := hP
    _ ≤ C₀ * (T * Real.sqrt (weightedEnergy a V G).toReal) :=
      mul_le_mul_of_nonneg_left hgrad.2 hC₀
    _ = _ := by ring

/-- Energy convergence of zero-boundary differences implies scalar L¹ convergence. -/
lemma lift_l1_tendsto_of_energy (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : ℕ → Vec d → ℝ} {G : ℕ → Vec d → Vec d}
    {w : Vec d → ℝ} {H : Vec d → Vec d}
    (hu : ∀ n, MemH1a0 a V (u n) (G n)) (hw : MemH1a0 a V w H)
    (hE : Tendsto (fun n => weightedEnergy a V (G n - H)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n - w) 1 (volume.restrict V)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := lift_zero_boundary_l1_bound hV hne ha
  have htR : Tendsto (fun n => (weightedEnergy a V (G n - H)).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hE
  have ht : Tendsto (fun n => ENNReal.ofReal (C * Real.sqrt (weightedEnergy a V (G n - H)).toReal))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((Real.continuous_sqrt.continuousAt.tendsto.comp htR).const_mul C))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
  intro n
  dsimp only
  have hd := Weighted.MemH1a0.sub hV hne ha (hu n) hw
  have hi := (Weighted.memH1a_memW11 hV hne ha (Weighted.MemH1a0.memH1a ha hd)).1
  rw [Weighted.l1_eq_ofReal_integral_abs hi]
  exact ENNReal.ofReal_le_ofReal (hb _ _ hd)

/-- Any energy-Cauchy sequence of boundary pairs has a literal boundary limit.
This theorem proves the approximation step; it does not assume membership of the limit. -/
theorem lift_boundary_limit (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : ℕ → Vec d → ℝ} {G : ℕ → Vec d → Vec d}
    (hu : ∀ n, MemH1a0 a V (u n) (G n))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      weightedEnergy a V (G m - G n) < ENNReal.ofReal ε) :
    ∃ w H, MemH1a0 a V w H ∧
      Tendsto (fun n => weightedEnergy a V (G n - H)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (u n - w) 1 (volume.restrict V)) atTop (𝓝 0) := by
  let F (n : ℕ) : Weighted.GradientCore ha := Weighted.memH1aEnergyField hV.isOpen ha
    (Weighted.MemH1a0.memH1a ha (hu n))
  let Z := Weighted.zeroSubmodule hV.isOpen ha
  let z (n : ℕ) : Z := ⟨(F n : Weighted.GradientHilbert ha),
    Weighted.MemH1a0.gradient_mem hV hne ha (hu n)⟩
  have hsq (m n : ℕ) : ENNReal.ofReal (‖z m - z n‖ ^ 2) = weightedEnergy a V (G m - G n) := by
    change ENNReal.ofReal (‖(F m : Weighted.GradientHilbert ha) - F n‖ ^ 2) = _
    rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
    exact (Weighted.GradientCore.energy_eq_norm_sq ha (F m - F n)).symm
  have hz : CauchySeq z := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hs := hN m n hm hn
    rw [← hsq] at hs
    have hs' : ‖z m - z n‖ ^ 2 < ε ^ 2 := ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hε) |>.mp hs
    nlinarith only [hs', norm_nonneg (z m - z n), hε]
  have : CompleteSpace Z := Weighted.zeroHilbert_complete hV hne ha
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hz
  obtain ⟨w, hw⟩ := Weighted.zeroHilbert_exists_rep hV hne ha q
  let H := Weighted.gradientHilbertRep ha q.val
  have ht : Tendsto (fun n => (F n : Weighted.GradientHilbert ha)) atTop (𝓝 (H : Weighted.GradientHilbert ha)) := by
    rw [Weighted.gradientHilbertRep_coe]
    exact (continuous_subtype_val.tendsto q).comp hq
  have hE := Weighted.GradientCore.tendsto_energy_of_coe ha ht
  refine ⟨w, H.field, hw, hE, ?_⟩
  exact lift_l1_tendsto_of_energy hV hne ha hu hw hE

end
end CoarseDeGiorgi.Whitney
