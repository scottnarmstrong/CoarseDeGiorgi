module

public import CoarseDeGiorgi.Weighted.HarmonicReplacement
public import CoarseDeGiorgi.Weighted.PairSeparation

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Energy identity for a harmonic pair and every competitor in its boundary class. -/
theorem IsWeightedSolution.energy_identity (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {h w : Vec d → ℝ} {Gh Gw : Vec d → Vec d}
    (hh : CoarseDeGiorgi.IsWeightedSolution a V h Gh)
    (hw : MemH1a0 a V (w - h) (Gw - Gh)) :
    weightedEnergy a V Gw = weightedEnergy a V Gh + weightedEnergy a V (Gw - Gh) := by
  let F := memH1aEnergyField hV.isOpen ha hh.1
  let D := memH1aEnergyField hV.isOpen ha (hw.memH1a ha)
  have hd : inner ℝ D F = 0 :=
    (IsWeightedSolution.orthogonality hV hne ha hh hw).2
  have hn : ‖F + D‖ ^ 2 = ‖F‖ ^ 2 + ‖D‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_comm D F, hd, mul_zero, add_zero]
  have hraw : (F + D).field = Gw := by
    change Gh + (Gw - Gh) = Gw
    abel
  calc
    weightedEnergy a V Gw = weightedEnergy a V (F + D).field := by rw [hraw]
    _ = ENNReal.ofReal (‖F + D‖ ^ 2) := GradientCore.energy_eq_norm_sq ha _
    _ = ENNReal.ofReal (‖F‖ ^ 2) + ENNReal.ofReal (‖D‖ ^ 2) := by
      rw [hn, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    _ = weightedEnergy a V Gh + weightedEnergy a V (Gw - Gh) := by
      rw [← GradientCore.energy_eq_norm_sq ha, ← GradientCore.energy_eq_norm_sq ha]
      rfl

/-- Two harmonic representatives in the same boundary class agree almost everywhere. -/
theorem harmonic_replacement_unique (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {g h k : Vec d → ℝ} {Gg Gh Gk : Vec d → Vec d}
    (hh : CoarseDeGiorgi.IsWeightedSolution a V h Gh)
    (hk : CoarseDeGiorgi.IsWeightedSolution a V k Gk)
    (hhg : MemH1a0 a V (h - g) (Gh - Gg))
    (hkg : MemH1a0 a V (k - g) (Gk - Gg)) :
    h =ᵐ[volume.restrict V] k ∧ Gh =ᵐ[volume.restrict V] Gk := by
  have hdiff : MemH1a0 a V (h - k) (Gh - Gk) := by
    have hd := hhg.sub hV hne ha hkg
    simpa only [show h - g - (k - g) = h - k by abel,
      show Gh - Gg - (Gk - Gg) = Gh - Gk by abel] using hd
  let F := memH1aEnergyField hV.isOpen ha hh.1
  let K := memH1aEnergyField hV.isOpen ha hk.1
  let D := memH1aEnergyField hV.isOpen ha (hdiff.memH1a ha)
  have h1 : inner ℝ D F = 0 := (IsWeightedSolution.orthogonality hV hne ha hh hdiff).2
  have h2 : inner ℝ D K = 0 := (IsWeightedSolution.orthogonality hV hne ha hk hdiff).2
  have hD : (D : GradientHilbert ha) = ((F - K : GradientCore ha) : GradientHilbert ha) := by
    apply (GradientCore.coe_eq_iff ha _ _).mpr
    exact Filter.EventuallyEq.rfl
  have hn : ‖D‖ ^ 2 = 0 := by
    rw [← UniformSpace.Completion.norm_coe, ← real_inner_self_eq_norm_sq]
    conv_rhs => rw [← sub_self (0 : ℝ)]
    have hi1 : inner ℝ (D : GradientHilbert ha) (F : GradientHilbert ha) = 0 := by
      rw [gradientHilbert_inner_coe]
      exact h1
    have hi2 : inner ℝ (D : GradientHilbert ha) (K : GradientHilbert ha) = 0 := by
      rw [gradientHilbert_inner_coe]
      exact h2
    calc
      inner ℝ (D : GradientHilbert ha) (D : GradientHilbert ha) =
          inner ℝ (D : GradientHilbert ha)
            ((F : GradientHilbert ha) - (K : GradientHilbert ha)) := by
        rw [← UniformSpace.Completion.coe_sub, ← hD]
      _ = 0 - 0 := by rw [inner_sub_right, hi1, hi2]
  have hE : weightedEnergy a V (Gh - Gk) = 0 := by
    change weightedEnergy a V D.field = 0
    rw [GradientCore.energy_eq_norm_sq ha, hn, ENNReal.ofReal_zero]
  have hz := hdiff.eq_zero_of_energy_zero hV hne ha hE
  exact ⟨hz.1.mono fun x hx => sub_eq_zero.mp hx,
    hz.2.mono fun x hx => sub_eq_zero.mp hx⟩

/-- Harmonic replacement, orthogonality, exact minimization, and a.e. uniqueness together. -/
theorem harmonic_replacement (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {g : Vec d → ℝ} {Gg : Vec d → Vec d}
    (hg : MemH1a a V g Gg) :
    ∃ h : Vec d → ℝ, ∃ Gh : Vec d → Vec d,
      CoarseDeGiorgi.IsWeightedSolution a V h Gh ∧
      MemH1a0 a V (h - g) (Gh - Gg) ∧
      (∀ w H, MemH1a0 a V w H →
        IntegrableOn (fun x => vecDot (H x) (matVecMul (a x) (Gh x))) V ∧
        (∫ x in V, vecDot (H x) (matVecMul (a x) (Gh x))) = 0) ∧
      (∀ w Gw, MemH1a0 a V (w - g) (Gw - Gg) →
        weightedEnergy a V Gw = weightedEnergy a V Gh + weightedEnergy a V (Gw - Gh)) ∧
      (∀ k Gk, CoarseDeGiorgi.IsWeightedSolution a V k Gk →
        MemH1a0 a V (k - g) (Gk - Gg) →
        h =ᵐ[volume.restrict V] k ∧ Gh =ᵐ[volume.restrict V] Gk) := by
  obtain ⟨h, Gh, hh, h0, hortho⟩ := exists_harmonic_replacement hV hne ha hg
  refine ⟨h, Gh, hh, h0, hortho, ?_, ?_⟩
  · intro w Gw hw
    have hd : MemH1a0 a V (w - h) (Gw - Gh) := by
      have hsub := hw.sub hV hne ha h0
      simpa only [show w - g - (h - g) = w - h by abel,
        show Gw - Gg - (Gh - Gg) = Gw - Gh by abel] using hsub
    exact IsWeightedSolution.energy_identity hV hne ha hh hd
  · intro k Gk hk hk0
    exact harmonic_replacement_unique hV hne ha hh hk h0 hk0

end CoarseDeGiorgi.Weighted
