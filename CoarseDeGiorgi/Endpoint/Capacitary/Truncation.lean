import CoarseDeGiorgi.Endpoint.Capacitary.Obstacle
import CoarseDeGiorgi.Endpoint.Source.PosPart
import CoarseDeGiorgi.Weighted.HarmonicCore
import CoarseDeGiorgi.Weighted.TestingCompactSupport
import CoarseDeGiorgi.Weighted.Truncation.Continuity

/-! Zero-boundary truncations for the capacitary obstacle. -/

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

omit [NeZero d] in
/-- A.e. changes preserve the literal zero-boundary completion. -/
theorem capacitary_memH1a0_congr_ae {u v : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : MemH1a0 a V u G) (huv : u =ᵐ[volume.restrict V] v)
    (hGH : G =ᵐ[volume.restrict V] H) : MemH1a0 a V v H := by
  obtain ⟨huM, hGM, f, hf, hc, ht, hE⟩ := hu
  refine ⟨huM.congr huv, hGM.congr hGH, f, hf, hc, ?_, ?_⟩
  · intro K hK hKV
    have heq := ae_mono (Measure.restrict_mono hKV le_rfl) huv
    convert ht K hK hKV using 1
    funext n
    apply lintegral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  · convert hE using 1
    funext n
    exact energy_congr_ae (EventuallyEq.rfl.sub hGH.symm)

/-- Positive parts above a nonnegative level preserve zero boundary values. -/
theorem capacitary_memH1a0_max_sub_const
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a0 a V u G) {c : ℝ} (hc : 0 ≤ c) :
    MemH1a0 a V (fun x => max (u x - c) 0) ({x | c < u x}.indicator G) := by
  have hgrad : Weighted.smoothGrad (fun _ : Vec d => c) = (0 : Vec d → Vec d) := by
    funext x i
    change (fderiv ℝ (fun _ : Vec d => c) x) (basisVec i) = 0
    exact congrArg (fun T : Vec d →L[ℝ] ℝ => T (basisVec i))
      (hasFDerivAt_const (𝕜 := ℝ) c x).fderiv
  have hs : Weighted.IsSmoothCore a V (fun _ => c) := by
    refine ⟨contDiffOn_const, ?_, ?_⟩
    · exact (continuous_const.continuousOn.integrableOn_compact
        hV.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
    · change Weighted.weightedEnergy a V (Weighted.smoothGrad (fun _ => c)) < ⊤
      rw [hgrad, Weighted.weightedEnergy_zero]
      exact ENNReal.zero_lt_top
  have hm := memH1a_of_isSmoothCore hV.isOpen ha hs
  rw [hgrad] at hm
  have hp := memH1a0_posPart_sub hV hne ha hu hm (Eventually.of_forall fun _ => hc)
  simpa only [sub_zero, sub_pos] using hp

/-- Clipping a zero-boundary pair to `[0,1]` preserves membership and decreases energy. -/
theorem capacitary_clip
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a0 a V u G) :
    ∃ H : Vec d → Vec d, MemH1a0 a V (fun x => min (max (u x) 0) 1) H ∧
      weightedEnergy a V H ≤ weightedEnergy a V G := by
  have hp := capacitary_memH1a0_max_sub_const hV hne ha hu (le_refl 0)
  simp only [sub_zero] at hp
  have hq := capacitary_memH1a0_max_sub_const hV hne ha hp (by norm_num : (0 : ℝ) ≤ 1)
  have hr := Weighted.MemH1a0.sub hV hne ha hp hq
  let H := {x | 0 < u x}.indicator G -
    {x | 1 < max (u x) 0}.indicator ({x | 0 < u x}.indicator G)
  refine ⟨H, capacitary_memH1a0_congr_ae hr ?_ EventuallyEq.rfl, ?_⟩
  · filter_upwards with x
    change max (u x) 0 - max (max (u x) 0 - 1) 0 = min (max (u x) 0) 1
    rcases le_total (max (u x) 0) 1 with hx | hx
    · rw [max_eq_right (sub_nonpos.mpr hx), sub_zero, min_eq_left hx]
    · rw [max_eq_left (sub_nonneg.mpr hx), min_eq_right hx]
      ring
  · have heq : H = fun x => (if 0 < u x ∧ ¬ 1 < max (u x) 0 then (1 : ℝ) else 0) • G x := by
      funext x
      by_cases h0 : 0 < u x <;> by_cases h1 : 1 < max (u x) 0 <;>
        simp only [H, Pi.sub_apply, Set.indicator_apply, Set.mem_ofPred_eq, h0, h1,
          not_true_eq_false, not_false_eq_true, true_and, false_and, ite_true, ite_false, sub_self, sub_zero, one_smul, zero_smul]
    rw [heq]
    have hb := energy_mul_le ha (G := G) (M := 1)
      (Eventually.of_forall fun x => show
        |if 0 < u x ∧ ¬ 1 < max (u x) 0 then (1 : ℝ) else 0| ≤ 1 from by
        split_ifs <;> norm_num)
    simpa only [one_pow, ENNReal.ofReal_one, one_mul] using hb

/-- The least-energy capacitary function can be chosen pointwise between zero and one. -/
theorem exists_bounded_capacitary_minimizer
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (Q : Set (Vec d))
    (hQ : ∃ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a V u G ∧
      (∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ u x)) :
    ∃ (ψ : Vec d → ℝ) (Gψ : Vec d → Vec d), MemH1a0 a V ψ Gψ ∧
      (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) ∧
      (∀ᵐ x ∂volume.restrict V, x ∈ Q → ψ x = 1) ∧
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a V u G →
        (∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ u x) →
        weightedEnergy a V Gψ ≤ weightedEnergy a V G := by
  obtain ⟨u, G, hu, huQ, hmin⟩ := exists_capacitary_minimizer hV hne ha Q hQ
  obtain ⟨H, hH, hE⟩ := capacitary_clip hV hne ha hu
  refine ⟨fun x => min (max (u x) 0) 1, H, hH, ?_, ?_, ?_⟩
  · intro x
    exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  · filter_upwards [huQ] with x hx hxQ
    exact min_eq_right ((hx hxQ).trans (le_max_left _ _))
  · intro v K hv hvQ
    exact hE.trans (hmin v K hv hvQ)

end CoarseDeGiorgi.Endpoint
