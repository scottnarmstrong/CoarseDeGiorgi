module

public import CoarseDeGiorgi.Endpoint.Capacitary.Variation

/-! The capacitary test inequality `e.capacitary.test`. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

variable {d : ℕ} [NeZero d] {V Q : Set (Vec d)} {a : CoeffField d}

/-- Equation `e.capacitary.test`: a nonnegative zero-boundary test bounded by `L` on the
obstacle has capacitary pairing between zero and `L` times the capacity. -/
theorem capacitary_test
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {ψ z : Vec d → ℝ} {Gψ H : Vec d → Vec d}
    (hψ : MemH1a0 a V ψ Gψ)
    (hψQ : ∀ᵐ x ∂volume.restrict V, x ∈ Q → ψ x = 1)
    (hmin : ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a V u G →
      (∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ u x) →
      weightedEnergy a V Gψ ≤ weightedEnergy a V G)
    (hz : MemH1a0 a V z H) (hz0 : ∀ᵐ x ∂volume.restrict V, 0 ≤ z x)
    (L : ℝ) (_hL : 0 ≤ L) (hzQ : ∀ᵐ x ∂volume.restrict V, x ∈ Q → z x ≤ L) :
    0 ≤ (∫ x in V, vecDot (H x) (matVecMul (a x) (Gψ x))) ∧
      (∫ x in V, vecDot (H x) (matVecMul (a x) (Gψ x))) ≤
        L * (weightedEnergy a V Gψ).toReal := by
  have hψQ' : ∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ ψ x :=
    hψQ.mono fun x hx hxQ => (hx hxQ).ge
  refine ⟨capacitary_variation_nonneg hV hne ha hψ hψQ' hmin hz
    (hz0.mono fun _ hx _ => hx), ?_⟩
  have hLψ := capacitary_memH1a0_smul hV hne ha hψ L
  have hdiff := Weighted.MemH1a0.sub hV hne ha hz hLψ
  have hw := capacitary_memH1a0_max_sub_const hV hne ha hdiff (le_refl 0)
  simp only [sub_zero] at hw
  let w : Vec d → ℝ := fun x => max ((z - L • ψ) x) 0
  let W : Vec d → Vec d := {x | 0 < (z - L • ψ) x}.indicator (H - L • Gψ)
  have hwQ : ∀ᵐ x ∂volume.restrict V, x ∈ Q → w x = 0 := by
    filter_upwards [hψQ, hzQ] with x hx hx' hxQ
    dsimp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hx hxQ, mul_one]
    exact max_eq_right (sub_nonpos.mpr (hx' hxQ))
  have hwzero := capacitary_variation_eq_zero hV hne ha hψ hψQ' hmin hw hwQ
  have hv := Weighted.MemH1a0.add hV hne ha
    (Weighted.MemH1a0.sub hV hne ha hLψ hz) hw
  have hv0 : ∀ᵐ x ∂volume.restrict V, 0 ≤ ((L • ψ - z) + w) x := by
    filter_upwards with x
    change 0 ≤ L * ψ x - z x + max (z x - L * ψ x) 0
    have h := le_max_left (z x - L * ψ x) 0
    linarith only [h]
  have hvpos := capacitary_variation_nonneg hV hne ha hψ hψQ' hmin hv
    (hv0.mono fun _ hx _ => hx)
  let P := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hψ)
  let Z := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hz)
  let B := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hw)
  have hB : inner ℝ (B : GradientHilbert ha) (P : GradientHilbert ha) = 0 := by
    rw [gradientHilbert_inner_coe]
    exact hwzero
  have hZ : inner ℝ (Z : GradientHilbert ha) (P : GradientHilbert ha) =
      ∫ x in V, vecDot (H x) (matVecMul (a x) (Gψ x)) :=
    gradientHilbert_inner_coe ha Z P
  have hP : inner ℝ (P : GradientHilbert ha) (P : GradientHilbert ha) =
      (weightedEnergy a V Gψ).toReal := by
    rw [real_inner_self_eq_norm_sq, UniformSpace.Completion.norm_coe, GradientCore.norm_sq ha]
    rfl
  have hvinner : 0 ≤ inner ℝ ((L • P - Z + B : GradientCore ha) : GradientHilbert ha)
      (P : GradientHilbert ha) := by
    rw [gradientHilbert_inner_coe]
    exact hvpos
  rw [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_sub,
    UniformSpace.Completion.coe_smul, inner_add_left, inner_sub_left, real_inner_smul_left,
    hP, hZ, hB, add_zero] at hvinner
  exact sub_nonneg.mp hvinner

end CoarseDeGiorgi.Endpoint
