module

public import CoarseDeGiorgi.Endpoint.Capacitary.Coercivity
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-! The closed convex obstacle set for a capacitary function. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The source admissibility condition, represented in the energy Hilbert carrier.
It constrains the value of the represented zero-boundary function on `Q`. -/
def capacitaryAdmissible (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    (Q : Set (Vec d)) (x : zeroSubmodule hV ha) : Prop :=
  ∃ (u : Vec d → ℝ) (G : Vec d → Vec d) (hu : MemH1a0 a V u G),
    (∀ᵐ y ∂volume.restrict V, y ∈ Q → 1 ≤ u y) ∧
    (memH1aEnergyField hV ha (Weighted.MemH1a0.memH1a ha hu) : GradientHilbert ha) = x.val

/-- The obstacle set is convex in the energy carrier. -/
theorem capacitaryAdmissible_convex
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (Q : Set (Vec d)) :
    Convex ℝ {x : zeroSubmodule hV.isOpen ha | capacitaryAdmissible hV.isOpen ha Q x} := by
  rintro x ⟨u, G, hu, huQ, hG⟩ y ⟨v, H, hv, hvQ, hH⟩ b c hb hc hbc
  have hbu := capacitary_memH1a0_smul hV hne ha hu b
  have hcv := capacitary_memH1a0_smul hV hne ha hv c
  have hsum := Weighted.MemH1a0.add hV hne ha hbu hcv
  refine ⟨b • u + c • v, b • G + c • H, hsum, ?_, ?_⟩
  · filter_upwards [huQ, hvQ] with z hz hz'
    intro hzQ
    change 1 ≤ b * u z + c * v z
    calc
      1 = b * 1 + c * 1 := by rw [mul_one, mul_one, hbc]
      _ ≤ b * u z + c * v z := add_le_add
        (mul_le_mul_of_nonneg_left (hz hzQ) hb)
        (mul_le_mul_of_nonneg_left (hz' hzQ) hc)
  · let F := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hu)
    let K := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hv)
    have heq : memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hsum) =
        b • F + c • K := rfl
    rw [heq, UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul,
      UniformSpace.Completion.coe_smul, hG, hH]
    rfl

/-- The obstacle set is closed in the energy norm, using zero-boundary L¹ coercivity. -/
theorem capacitaryAdmissible_isClosed
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (Q : Set (Vec d)) :
    IsClosed {x : zeroSubmodule hV.isOpen ha | capacitaryAdmissible hV.isOpen ha Q x} := by
  apply isSeqClosed_iff_isClosed.mp
  intro f x hf ht
  choose u G hu huQ hG using hf
  obtain ⟨v, hv⟩ := zeroHilbert_exists_rep hV hne ha x
  let H := gradientHilbertRep ha x.val
  let F : ℕ → GradientCore ha := fun n =>
    memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha (hu n))
  have hgrad : Tendsto (fun n => (F n : GradientHilbert ha)) atTop
      (𝓝 (H : GradientHilbert ha)) := by
    rw [gradientHilbertRep_coe]
    exact (continuous_subtype_val.tendsto x).comp ht |>.congr (fun n => (hG n).symm)
  have hE := GradientCore.tendsto_energy_of_coe ha hgrad
  have hL := zero_boundary_tendsto_l1_of_energy hV hne ha hu hv hE
  obtain ⟨ns, _, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ENNReal) ≠ 0) hL).exists_seq_tendsto_ae
  refine ⟨v, H.field, hv, ?_, ?_⟩
  · filter_upwards [hae, ae_all_iff.mpr huQ] with z hz hzQ
    intro hzQ'
    exact isClosed_Ici.mem_of_tendsto hz (Eventually.of_forall fun n => hzQ (ns n) hzQ')
  · have heq : (memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hv) :
        GradientCore ha) = H := rfl
    rw [heq, gradientHilbertRep_coe]

/-- A nonempty capacitary obstacle has a least-energy literal zero-boundary representative. -/
theorem exists_capacitary_minimizer
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (Q : Set (Vec d))
    (hQ : ∃ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a V u G ∧
      (∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ u x)) :
    ∃ (ψ : Vec d → ℝ) (Gψ : Vec d → Vec d), MemH1a0 a V ψ Gψ ∧
      (∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ ψ x) ∧
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a V u G →
        (∀ᵐ x ∂volume.restrict V, x ∈ Q → 1 ≤ u x) →
        weightedEnergy a V Gψ ≤ weightedEnergy a V G := by
  let Z := zeroSubmodule hV.isOpen ha
  have : CompleteSpace Z := zeroHilbert_complete hV hne ha
  let K : Set Z := {x | capacitaryAdmissible hV.isOpen ha Q x}
  have hK : K.Nonempty := by
    obtain ⟨u, G, hu, huQ⟩ := hQ
    exact ⟨⟨_, Weighted.MemH1a0.gradient_mem hV hne ha hu⟩, u, G, hu, huQ, rfl⟩
  have hclosed : IsClosed K := capacitaryAdmissible_isClosed hV hne ha Q
  have hconvex : Convex ℝ K := capacitaryAdmissible_convex hV hne ha Q
  obtain ⟨x, hx, hxmin⟩ := exists_norm_eq_iInf_of_complete_convex hK hclosed.isComplete hconvex 0
  obtain ⟨ψ, Gψ, hψ, hψQ, hGψ⟩ := hx
  refine ⟨ψ, Gψ, hψ, hψQ, ?_⟩
  intro u G hu huQ
  let y : Z := ⟨_, Weighted.MemH1a0.gradient_mem hV hne ha hu⟩
  have hy : y ∈ K := ⟨u, G, hu, huQ, rfl⟩
  have hn : ‖x‖ ≤ ‖y‖ := by
    have hb : BddBelow (Set.range (fun w : K => ‖(0 : Z) - w.val‖)) :=
      ⟨0, by rintro z ⟨w, rfl⟩; exact norm_nonneg _⟩
    have h := ciInf_le hb (⟨y, hy⟩ : K)
    rw [← hxmin] at h
    simpa only [zero_sub, norm_neg] using h
  have he1 := GradientCore.norm_sq ha
    (memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hψ))
  have he2 := GradientCore.norm_sq ha
    (memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hu))
  simp only [memH1aEnergyField_field] at he1 he2
  have hn1 : ‖x‖ ^ 2 = (weightedEnergy a V Gψ).toReal := by
    change ‖x.val‖ ^ 2 = _
    rw [← hGψ, UniformSpace.Completion.norm_coe]
    exact he1
  have hn2 : ‖y‖ ^ 2 = (weightedEnergy a V G).toReal := by
    change ‖(memH1aEnergyField hV.isOpen ha
      (Weighted.MemH1a0.memH1a ha hu) : GradientHilbert ha)‖ ^ 2 = _
    rw [UniformSpace.Completion.norm_coe]
    exact he2
  apply (ENNReal.toReal_le_toReal
    (Weighted.MemH1a.energy_lt_top hV.isOpen ha (Weighted.MemH1a0.memH1a ha hψ)).ne
    (Weighted.MemH1a.energy_lt_top hV.isOpen ha (Weighted.MemH1a0.memH1a ha hu)).ne).mp
  rw [← hn1, ← hn2]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

end CoarseDeGiorgi.Endpoint
