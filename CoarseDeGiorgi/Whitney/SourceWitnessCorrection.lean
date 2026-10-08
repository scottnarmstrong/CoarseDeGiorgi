module

public import CoarseDeGiorgi.Whitney.LiftCountable
public import CoarseDeGiorgi.Whitney.LiftIdentification
public import Mathlib.Logic.Encodable.Basic

/-! # Countable corrections with finite and empty families included -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators
noncomputable section
variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Countable actual cell corrections converge, without assuming an infinite
family or introducing repeated dummy cells. Empty enumeration slots carry
zero pairs on the empty set. -/
theorem source_correction_exists {ι : Type*} [Countable ι]
    (hV : IsOpenBoundedConvexDomain V) (hneV : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    (U : ι → Set (Vec d)) (hU : ∀ i, IsOpenBoundedConvexDomain (U i))
    (hne : ∀ i, (U i).Nonempty) (hUV : ∀ i, U i ⊆ V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (e : ι → Vec d) (Gseed : Vec d → Vec d)
    (hseed : ∀ i x, x ∈ U i → Gseed x = e i)
    (hfinite : weightedEnergy a V Gseed < ⊤) :
    ∃ ξ H, MemH1a0 a V ξ H ∧
      (∀ i, ξ =ᵐ[volume.restrict (U i)]
        ((liftCellPair (hU i) (hne i) (lift_coeff_mono ha (hUV i)) (e i)).1 -
          Weighted.responseAffine (e i))) ∧
      ξ =ᵐ[volume.restrict (V \ ⋃ i, U i)] 0 := by
  classical
  let : Encodable ι := Encodable.ofCountable ι
  let Un : ℕ → Set (Vec d) := fun k => (Encodable.decode₂ ι k).elim ∅ U
  let u : ℕ → Vec d → ℝ := fun k => (Encodable.decode₂ ι k).elim 0
    (fun i => (U i).indicator
      ((liftCellPair (hU i) (hne i) (lift_coeff_mono ha (hUV i)) (e i)).1 -
        Weighted.responseAffine (e i)))
  let G : ℕ → Vec d → Vec d := fun k => (Encodable.decode₂ ι k).elim 0
    (fun i => (U i).indicator
      ((liftCellPair (hU i) (hne i) (lift_coeff_mono ha (hUV i)) (e i)).2 - fun _ => e i))
  have hUn (k : ℕ) : MeasurableSet (Un k) := by
    dsimp [Un]
    cases Encodable.decode₂ ι k with
    | none => exact MeasurableSet.empty
    | some i => exact (hU i).isOpen.measurableSet
  have hUnV (k : ℕ) : Un k ⊆ V := by
    dsimp [Un]
    cases Encodable.decode₂ ι k with
    | none => exact empty_subset V
    | some i => exact hUV i
  have hd : Pairwise (fun k l => Disjoint (Un k) (Un l)) := by
    intro k l hkl
    dsimp [Un]
    cases hk : Encodable.decode₂ ι k with
    | none => exact empty_disjoint _
    | some i =>
      cases hl : Encodable.decode₂ ι l with
      | none => exact disjoint_empty _
      | some j =>
        apply hdisj
        intro hij
        apply hkl
        have hi := Encodable.decode₂_eq_some.mp hk
        have hj := Encodable.decode₂_eq_some.mp hl
        rw [hij] at hi
        exact hi.symm.trans hj
  have hu (k : ℕ) : MemH1a0 a V (u k) (G k) := by
    dsimp [u, G]
    cases hk : Encodable.decode₂ ι k with
    | none =>
      have hz := Weighted.memH1a0_of_supported hV.isOpen ha
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (0 : Vec d → ℝ))
        HasCompactSupport.zero (by
          change tsupport (0 : Vec d → ℝ) ⊆ V
          rw [tsupport_zero]
          exact empty_subset V)
      change MemH1a0 a V (0 : Vec d → ℝ) (smoothGrad (0 : Vec d → ℝ)) at hz
      have hg : smoothGrad (0 : Vec d → ℝ) = (0 : Vec d → Vec d) := by
        funext x i
        change (fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x) (basisVec i) = 0
        exact congrArg (fun T : Vec d →L[ℝ] ℝ => T (basisVec i))
          (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).fderiv
      rw [hg] at hz
      exact hz
    | some i =>
      exact lift_zero_extension (hU i) (hne i) hV.isOpen (hUV i) ha
        (liftCellPair_spec (hU i) (hne i) (lift_coeff_mono ha (hUV i)) (e i)).2
  have hgs (k : ℕ) (x : Vec d) (hx : x ∉ Un k) : G k x = 0 := by
    dsimp [Un] at hx
    dsimp [G]
    cases hk : Encodable.decode₂ ι k with
    | none => rfl
    | some i =>
      rw [hk] at hx
      simp only [Option.elim_some] at hx ⊢
      exact indicator_of_notMem hx _
  have hus (k : ℕ) (x : Vec d) (hx : x ∉ Un k) : u k x = 0 := by
    dsimp [Un] at hx
    dsimp [u]
    cases hk : Encodable.decode₂ ι k with
    | none => rfl
    | some i =>
      rw [hk] at hx
      simp only [Option.elim_some] at hx ⊢
      exact indicator_of_notMem hx _
  have hcell (k : ℕ) : weightedEnergy a V (G k) ≤ weightedEnergy a (Un k) Gseed := by
    dsimp [G, Un]
    cases hk : Encodable.decode₂ ι k with
    | none =>
      simp only [Option.elim_none]
      change Weighted.weightedEnergy a V 0 ≤ _
      rw [Weighted.weightedEnergy_zero]
      exact bot_le
    | some i =>
      simp only [Option.elim_some]
      rw [lift_energy_indicator (hU i).isOpen.measurableSet (hUV i)]
      have he := liftCellPair_correction_energy (hU i) (hne i) (lift_coeff_mono ha (hUV i)) (e i)
      have hgrad : weightedEnergy a (U i) Gseed = weightedEnergy a (U i) (fun _ => e i) := by
        apply Weighted.energy_congr_ae
        filter_upwards [ae_restrict_mem (hU i).isOpen.measurableSet] with x hx
        exact hseed i x hx
      rw [hgrad, he]
      exact le_add_left le_rfl
  have hsum : (∑' k, weightedEnergy a V (G k)) ≠ ⊤ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' k, weightedEnergy a (Un k) Gseed := ENNReal.tsum_le_tsum hcell
      _ = ∫⁻ x in ⋃ k, Un k, ENNReal.ofReal
          (vecDot (Gseed x) (matVecMul (a x) (Gseed x))) :=
        (lintegral_iUnion hUn hd _).symm
      _ ≤ weightedEnergy a V Gseed := lintegral_mono_set (iUnion_subset hUnV)
      _ < ⊤ := hfinite
  obtain ⟨ξ, H, hξ, _, hL⟩ := lift_countable_boundary_limit hV hneV ha Un u G hu hd hgs hsum
  refine ⟨ξ, H, hξ, ?_, ?_⟩
  · intro i
    have he := lift_limit_eq_on_cell Un u hUn hUnV hd hus hL (Encodable.encode i)
    simp only [Un, u, Encodable.decode₂_encode, Option.elim_some] at he
    filter_upwards [he, ae_restrict_mem (hU i).isOpen.measurableSet] with x hx hxU
    simpa only [indicator_of_mem hxU] using hx
  · apply lift_limit_zero_on_set
      (hV.isOpen.measurableSet.diff (MeasurableSet.iUnion (fun i => (hU i).isOpen.measurableSet)))
      sdiff_subset u ?_ hL
    intro k x hx
    apply hus
    dsimp [Un]
    cases hk : Encodable.decode₂ ι k with
    | none => exact notMem_empty x
    | some i => exact fun hxi => hx.2 (mem_iUnion.mpr ⟨i, hxi⟩)

end
end CoarseDeGiorgi.Whitney
