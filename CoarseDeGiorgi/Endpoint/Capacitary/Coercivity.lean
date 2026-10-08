module

public import CoarseDeGiorgi.Weighted.TestingApproximation
public import CoarseDeGiorgi.Weighted.PairSeparation
public import CoarseDeGiorgi.Foundations.PoincareW11Zero

/-! The value L¹ bound needed to close the capacitary obstacle in the energy carrier. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The zero-boundary value is bounded in L¹ by its energy norm.
The geometric constant is chosen before the coefficient field. -/
theorem exists_zero_boundary_l1_energy_bound
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : CoeffField d) (_ha : IsWeightedCoeffOn V a)
      (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a V u G →
      ∫ x in V, |u x| ≤ C * Real.sqrt (∫ x in V, ((a x)⁻¹).trace) *
        Real.sqrt (weightedEnergy a V G).toReal := by
  obtain ⟨C, hC, hp⟩ := Foundations.exists_zero_boundary_poincare_w11
    hV.isOpen hV.isBoundedDomain.isBounded
  refine ⟨C, hC, ?_⟩
  intro a ha u G hu
  have hw := memH1a_memW11 hV hne ha (Weighted.MemH1a0.memH1a ha hu)
  have hGM := hu.2.1
  obtain ⟨_, _, f, hf, hc, hl, ht⟩ := hu
  have hcore := fun n => isSmoothCore_of_supported ha (hf n).1 (hf n).2.1
  have hFM := fun n => smoothGrad_aestronglyMeasurable hV.isOpen (hcore n).1
  have hL := (core_tendsto_l1 hV hne ha hcore hc hw.1.1 hl).2
  have hgrad := fun i => tendsto_coord_l1_of_energy ha hFM hGM
    (fun n => (hcore n).2.2) ht i
  have hP := hp u G f hw.1 hw.2.1 (fun n => (hf n).1)
    (fun n => (hf n).2.1) (fun n => (hf n).2.2) hL hgrad
  have hlen := gradient_length_integrable_and_bound ha hGM hw.2.2.2.2
  exact hP.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlen.2 hC)

/-- Energy convergence of zero-boundary differences implies convergence of their values in L¹. -/
theorem zero_boundary_tendsto_l1_of_energy
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {f : ℕ → Vec d → ℝ} {F : ℕ → Vec d → Vec d}
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hf : ∀ n, MemH1a0 a V (f n) (F n)) (hu : MemH1a0 a V u G)
    (ht : Tendsto (fun n => weightedEnergy a V (F n - G)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_zero_boundary_l1_energy_bound hV hne
  have hi := fun n => (memH1a_memW11 hV hne ha (Weighted.MemH1a0.memH1a ha (hf n))).1
  have hui := (memH1a_memW11 hV hne ha (Weighted.MemH1a0.memH1a ha hu)).1
  have hlim : Tendsto
      (fun n => ENNReal.ofReal (C * Real.sqrt (∫ x in V, ((a x)⁻¹).trace) *
        Real.sqrt (weightedEnergy a V (F n - G)).toReal)) atTop (𝓝 0) := by
    have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp ht
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hreal
    simpa only [Function.comp_def, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (hs.const_mul (C * Real.sqrt (∫ x in V, ((a x)⁻¹).trace)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro n
  dsimp only
  rw [l1_eq_ofReal_integral_abs ((hi n).sub hui)]
  exact ENNReal.ofReal_le_ofReal (hC a ha _ _ (Weighted.MemH1a0.sub hV hne ha (hf n) hu))

/-- Scalar multiplication preserves a literal zero-boundary pair. -/
theorem capacitary_memH1a0_smul
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a0 a V u G) (c : ℝ) : MemH1a0 a V (c • u) (c • G) := by
  obtain ⟨f, hf, _, hL, hE⟩ := Weighted.MemH1a0.comp_approximation hV hne ha hu
    (Φ := fun t : ℝ => c * t) (contDiff_const.mul contDiff_id) (mul_zero c)
    (L := ‖c‖₊) (by intro t; simp only [deriv_const_mul_id, coe_nnnorm, Real.norm_eq_abs]; exact le_rfl)
  have hi := (memH1a_memW11 hV hne ha (Weighted.MemH1a0.memH1a ha hu)).1
  apply memH1a0_of_supported_tendsto hV ha hf (hi.const_mul c) (hu.2.1.const_smul c)
  · exact hL
  · convert hE using 1
    funext n
    congr 1
    funext x
    simp only [Pi.sub_apply, Pi.smul_apply, deriv_const_mul_id]

end CoarseDeGiorgi.Endpoint
