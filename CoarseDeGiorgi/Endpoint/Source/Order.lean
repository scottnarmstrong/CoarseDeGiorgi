module

public import CoarseDeGiorgi.Endpoint.Source.Extension
public import CoarseDeGiorgi.Endpoint.Source.PosPart
public import CoarseDeGiorgi.Weighted.PairSeparation

/-! Comparison `0 ≤ V ≤ u` for the potential `V` of the restricted source measure. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- A zero-boundary pair whose gradient is an indicator of a finite-energy field `Y` and whose
pairing with `Y` is nonpositive vanishes. -/
theorem eq_zero_of_indicator_pairing [NeZero d] (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) {g : Vec d → ℝ} {H : Vec d → Vec d}
    (hg : MemH1a0 a V g H) {A : Set (Vec d)} {Y : Vec d → Vec d}
    (hH : ∀ x, H x = A.indicator Y x)
    (hle : ∫ x in V, vecDot (H x) (matVecMul (a x) (Y x)) ≤ 0) :
    g =ᵐ[volume.restrict V] 0 := by
  have hEH := MemH1a.energy_lt_top hV.isOpen ha (Weighted.MemH1a0.memH1a ha hg)
  have hpt : ∀ x, vecDot (H x) (matVecMul (a x) (H x)) = vecDot (H x) (matVecMul (a x) (Y x)) := by
    intro x
    by_cases hx : x ∈ A
    · rw [hH x, Set.indicator_of_mem hx]
    · rw [hH x, Set.indicator_of_notMem hx]
      simp [vecDot, matVecMul]
  have hreal : (weightedEnergy a V H).toReal ≤ 0 := by
    rw [energy_toReal ha hg.2.1]
    simp only [hpt]
    exact hle
  have hzero : weightedEnergy a V H = 0 := by
    have := ENNReal.toReal_nonneg (a := weightedEnergy a V H)
    exact (ENNReal.toReal_eq_zero_iff _).mp (le_antisymm hreal this) |>.resolve_right hEH.ne
  exact (MemH1a0.eq_zero_of_energy_zero hV hne ha hg hzero).1

/-- Standing hypotheses of the comparison: a source measure and the potential of its restriction. -/
structure PotentialData (a : CoeffField d) (V : Set (Vec d)) (μ ν : Measure (Vec d))
    (G Gv : Vec d → Vec d) : Prop where
  hμν : ν ≤ μ
  hμ : ∀ K : Set (Vec d), IsCompact K → K ⊆ V → μ K < ⊤
  hG : AEStronglyMeasurable G (volume.restrict V)
  hEG : weightedEnergy a V G < ⊤
  hGv : AEStronglyMeasurable Gv (volume.restrict V)
  hEGv : weightedEnergy a V Gv < ⊤
  hrep : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ V → ∫ x, φ x ∂μ = fluxPairing a V G φ
  heq : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ V → fluxPairing a V Gv φ = ∫ x, φ x ∂ν

theorem potential_nonneg [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {μ ν : Measure (Vec d)} [IsFiniteMeasure ν]
    {G Gv : Vec d → Vec d} (hP : PotentialData a V μ ν G Gv) {v : Vec d → ℝ}
    (hv : MemH1a0 a V v Gv) : ∀ᵐ x ∂volume.restrict V, 0 ≤ v x := by
  have hneg := Weighted.MemH1a0.neg hV hne ha hv
  have hzero : CoarseDeGiorgi.MemH1a a V (fun _ => (0 : ℝ)) (fun _ => (0 : Vec d)) := by
    have hg0 : Weighted.smoothGrad (0 : Vec d → ℝ) = fun _ => 0 := by
      funext x i; simp [Weighted.smoothGrad, CoarseDeGiorgi.smoothGrad]
    have h0 : IsSmoothCore a V (0 : Vec d → ℝ) := by
      refine ⟨contDiffOn_const, integrableOn_zero, ?_⟩
      simp [CoarseDeGiorgi.weightedEnergy, vecDot, matVecMul, hg0]
    have := memH1a_of_isSmoothCore hV.isOpen ha h0
    rw [hg0] at this
    exact this
  have hp := memH1a0_posPart_sub hV hne ha hneg hzero (ae_of_all _ fun _ => le_rfl)
  have h1 := (nonneg_pairing hV hne ha hP.hμν hP.hμ hP.hG hP.hEG hP.hGv hP.hEGv hP.hrep hP.heq
    hp (ae_of_all _ fun x => le_max_right _ _)).1
  have hz := eq_zero_of_indicator_pairing hV hne ha hp (fun x => rfl) (Y := ((-Gv - fun _ => (0 : Vec d)) : Vec d → Vec d))
    (by
      have : ∀ x, vecDot ({x | 0 < (-v) x - 0}.indicator (-Gv - fun _ => (0 : Vec d)) x)
          (matVecMul (a x) (((-Gv - fun _ => (0 : Vec d)) : Vec d → Vec d) x)) =
          -vecDot ({x | 0 < (-v) x - 0}.indicator (-Gv - fun _ => (0 : Vec d)) x)
            (matVecMul (a x) (Gv x)) := by
        intro x
        simp only [Pi.sub_apply, Pi.neg_apply, sub_zero, matVecMul_neg, vecDot_neg_right]
      simp only [this, integral_neg]
      linarith)
  filter_upwards [hz] with x hx
  have : max (-v x - 0) 0 = 0 := hx
  have := le_max_left (-v x - 0) 0
  simp only [Pi.neg_apply] at *
  linarith

theorem potential_le [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {μ ν : Measure (Vec d)} [IsFiniteMeasure ν]
    {G Gv : Vec d → Vec d} (hP : PotentialData a V μ ν G Gv) {v u : Vec d → ℝ}
    (hv : MemH1a0 a V v Gv) (hu : CoarseDeGiorgi.MemH1a a V u G)
    (hu0 : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x) : ∀ᵐ x ∂volume.restrict V, v x ≤ u x := by
  have hp := memH1a0_posPart_sub hV hne ha hv hu hu0
  have h1 := (nonneg_pairing hV hne ha hP.hμν hP.hμ hP.hG hP.hEG hP.hGv hP.hEGv hP.hrep hP.heq
    hp (ae_of_all _ fun x => le_max_right _ _)).2
  have hHm : AEStronglyMeasurable ({x | 0 < v x - u x}.indicator (Gv - G))
      (volume.restrict V) := hp.2.1
  have hEH := MemH1a.energy_lt_top hV.isOpen ha (Weighted.MemH1a0.memH1a ha hp)
  have i1 := (pairing_integrable_and_bound ha hHm hP.hGv hEH hP.hEGv).1
  have i2 := (pairing_integrable_and_bound ha hHm hP.hG hEH hP.hEG).1
  have hz := eq_zero_of_indicator_pairing hV hne ha hp (fun x => rfl) (Y := Gv - G)
    (by
      have : ∀ x, vecDot ({x | 0 < v x - u x}.indicator (Gv - G) x) (matVecMul (a x) ((Gv - G) x)) =
          vecDot ({x | 0 < v x - u x}.indicator (Gv - G) x) (matVecMul (a x) (Gv x)) -
          vecDot ({x | 0 < v x - u x}.indicator (Gv - G) x) (matVecMul (a x) (G x)) := by
        intro x
        simp only [Pi.sub_apply, sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right,
          vecDot_neg_right]
      simp only [this]
      rw [integral_sub i1 i2]
      linarith)
  filter_upwards [hz] with x hx
  have : max (v x - u x) 0 = 0 := hx
  have := le_max_left (v x - u x) 0
  linarith

end CoarseDeGiorgi.Endpoint
