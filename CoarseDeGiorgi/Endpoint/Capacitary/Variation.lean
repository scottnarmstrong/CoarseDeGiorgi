import CoarseDeGiorgi.Endpoint.Capacitary.Truncation
import CoarseDeGiorgi.Statements.IsWeightedSupersolution

/-! Variational inequalities for the capacitary function. -/

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

/-- The one-sided first variation of a squared Hilbert norm. -/
theorem capacitary_inner_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E)
    (h : ∀ ε : ℝ, 0 < ε → ‖x‖ ^ 2 ≤ ‖x + ε • y‖ ^ 2) :
    0 ≤ inner ℝ y x := by
  let ε : ℕ → ℝ := fun n => 1 / (n + 1)
  have hε : ∀ n, 0 < ε n := by intro n; positivity
  have hstep (n : ℕ) : 0 ≤ 2 * inner ℝ x y + ε n * ‖y‖ ^ 2 := by
    have hh := h (ε n) (hε n)
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hε n), mul_pow] at hh
    have hp : 0 ≤ ε n * (2 * inner ℝ x y + ε n * ‖y‖ ^ 2) := by
      nlinarith only [hh]
    exact (mul_nonneg_iff_of_pos_left (hε n)).mp hp
  have hl : Tendsto (fun n => 2 * inner ℝ x y + ε n * ‖y‖ ^ 2) atTop
      (𝓝 (2 * inner ℝ x y)) := by
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (‖y‖ ^ 2))
  have hp := isClosed_Ici.mem_of_tendsto hl (Eventually.of_forall hstep)
  change 0 ≤ 2 * inner ℝ x y at hp
  rw [real_inner_comm] at hp
  linarith only [hp]

variable {d : ℕ} [NeZero d] {V Q : Set (Vec d)} {a : CoeffField d}

/-- Any nonnegative obstacle direction has nonnegative first variation. -/
theorem capacitary_variation_nonneg
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {ψ g : Vec d → ℝ} {Gψ H : Vec d → Vec d}
    (hψ : MemH1a0 a V ψ Gψ)
    (hψQ : ∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ ψ x)
    (hmin : ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a V u G →
      (∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ u x) →
      weightedEnergy a V Gψ ≤ weightedEnergy a V G)
    (hg : MemH1a0 a V g H)
    (hgQ : ∀ᵐ x ∂volume.restrict V, x ∈ Q → 0 ≤ g x) :
    0 ≤ ∫ x in V, vecDot (H x) (matVecMul (a x) (Gψ x)) := by
  let F := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hψ)
  let K := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hg)
  have hi := capacitary_inner_nonneg (F : GradientHilbert ha) (K : GradientHilbert ha) ?_
  · rw [gradientHilbert_inner_coe] at hi
    exact hi
  · intro ε hε
    have he := capacitary_memH1a0_smul hV hne ha hg ε
    have ht := Weighted.MemH1a0.add hV hne ha hψ he
    have hQ : ∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ (ψ + ε • g) x := by
      filter_upwards [hψQ, hgQ] with x hx hx' hxQ
      exact (hx hxQ).trans (le_add_of_nonneg_right (mul_nonneg hε.le (hx' hxQ)))
    have hE := ENNReal.toReal_mono
      (Weighted.MemH1a.energy_lt_top hV.isOpen ha (Weighted.MemH1a0.memH1a ha ht)).ne
      (hmin _ _ ht hQ)
    rw [← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_add,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe,
      GradientCore.norm_sq ha, GradientCore.norm_sq ha]
    exact hE

/-- Directions vanishing on the obstacle have zero first variation. -/
theorem capacitary_variation_eq_zero
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {ψ g : Vec d → ℝ} {Gψ H : Vec d → Vec d}
    (hψ : MemH1a0 a V ψ Gψ)
    (hψQ : ∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ ψ x)
    (hmin : ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a V u G →
      (∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ u x) →
      weightedEnergy a V Gψ ≤ weightedEnergy a V G)
    (hg : MemH1a0 a V g H)
    (hgQ : ∀ᵐ x ∂volume.restrict V, x ∈ Q → g x = 0) :
    (∫ x in V, vecDot (H x) (matVecMul (a x) (Gψ x))) = 0 := by
  have hp := capacitary_variation_nonneg hV hne ha hψ hψQ hmin hg
    (hgQ.mono fun x hx hxQ => (hx hxQ).ge)
  have hn := capacitary_variation_nonneg hV hne ha hψ hψQ hmin
    (Weighted.MemH1a0.neg hV hne ha hg)
    (hgQ.mono fun x hx hxQ => by simp only [Pi.neg_apply, hx hxQ, neg_zero, le_refl])
  simp only [Pi.neg_apply, vecDot_neg_left, integral_neg] at hn
  exact le_antisymm (neg_nonneg.mp hn) hp

/-- A nonnegative capacitary minimizer is a weighted supersolution. -/
theorem capacitary_isWeightedSupersolution
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {ψ : Vec d → ℝ} {Gψ : Vec d → Vec d}
    (hψ : MemH1a0 a V ψ Gψ)
    (hψQ : ∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ ψ x)
    (hmin : ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a V u G →
      (∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ u x) →
      weightedEnergy a V Gψ ≤ weightedEnergy a V G) :
    IsWeightedSupersolution a V ψ Gψ := by
  refine ⟨Weighted.MemH1a.neg hV hne ha (Weighted.MemH1a0.memH1a ha hψ), ?_⟩
  intro φ hφ hc hs hφnn
  have ht := memH1a0_of_supported hV.isOpen ha hφ hc hs
  have hp := capacitary_variation_nonneg hV hne ha hψ hψQ hmin ht
    (Eventually.of_forall fun x _ => hφnn x)
  have hi := (pairing_integrable_and_bound ha ht.2.1 hψ.2.1
    (Weighted.MemH1a.energy_lt_top hV.isOpen ha (Weighted.MemH1a0.memH1a ha ht))
    (Weighted.MemH1a.energy_lt_top hV.isOpen ha (Weighted.MemH1a0.memH1a ha hψ))).1
  simp only [matVecMul_neg, vecDot_neg_right, integral_neg]
  exact ⟨hi.neg, neg_nonpos.mpr hp⟩

end CoarseDeGiorgi.Endpoint
