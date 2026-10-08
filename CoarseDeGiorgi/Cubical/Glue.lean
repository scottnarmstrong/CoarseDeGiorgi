import CoarseDeGiorgi.Whitney.SourceWitnessCorrection
import CoarseDeGiorgi.LowerFractional.Restriction

/-! # Countable gluing of cellwise corrections, with the gradient identified on every cell -/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory Set Filter Topology CoarseDeGiorgi.Whitney
open scoped ENNReal BigOperators
noncomputable section
variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Countably many disjoint open cells in `V` with constant affine data: the cellwise harmonic
corrections glue to a zero-boundary pair whose gradient is the cellwise one on each cell. -/
theorem glue_exists {ι : Type*} [Countable ι]
    (hV : IsOpenBoundedConvexDomain V) (hneV : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    (U : ι → Set (Vec d)) (hU : ∀ i, IsOpenBoundedConvexDomain (U i))
    (hne : ∀ i, (U i).Nonempty) (hUV : ∀ i, U i ⊆ V)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (e : ι → Vec d) (Gseed : Vec d → Vec d)
    (hseed : ∀ i x, x ∈ U i → Gseed x = e i)
    (hfinite : weightedEnergy a V Gseed < ⊤) :
    ∃ ξ H, MemH1a0 a V ξ H ∧
      (∀ i, H =ᵐ[volume.restrict (U i)]
        ((liftCellPair (hU i) (hne i) (lift_coeff_mono ha (hUV i)) (e i)).2 - fun _ => e i)) := by
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
  obtain ⟨ξ, H, hξ, hE, _⟩ := lift_countable_boundary_limit hV hneV ha Un u G hu hd hgs hsum
  refine ⟨ξ, H, hξ, ?_⟩
  intro i
  set k := Encodable.encode i with hkdef
  have hUk : Un k = U i := by simp [Un, k, Encodable.decode₂_encode]
  have hGk : G k = (U i).indicator
      ((liftCellPair (hU i) (hne i) (lift_coeff_mono ha (hUV i)) (e i)).2 - fun _ => e i) := by
    simp [G, k, Encodable.decode₂_encode]
  have hz : weightedEnergy a (U i) (G k - H) = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto hE
    filter_upwards [eventually_gt_atTop k] with n hn
    refine le_trans (le_of_eq ?_) (LowerFractional.weightedEnergy_mono (hUV i) _)
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (hU i).isOpen.measurableSet] with x hx
    have hxs : (∑ j ∈ Finset.range n, G j) x = G k x := by
      rw [Finset.sum_apply]
      apply Finset.sum_eq_single k
      · intro j _ hj
        exact hgs j x (fun hy => (Set.disjoint_left.mp (hd hj)) hy (hUk ▸ hx))
      · intro hk'; exact absurd (Finset.mem_range.mpr hn) hk'
    simp only [Pi.sub_apply, hxs]
  have hpd : ∀ᵐ x ∂(volume.restrict (U i)), (a x).PosDef :=
    (lift_coeff_mono ha (hUV i)).2.1
  have h0 : ∀ᵐ x ∂(volume.restrict (U i)), G k x - H x = 0 := by
    have hl := (lintegral_eq_zero_iff' (by
      exact (Weighted.quadratic_aestronglyMeasurable (lift_coeff_mono ha (hUV i))
        (((hu k).2.1.mono_measure (Measure.restrict_mono (hUV i) le_rfl)).sub
          (hξ.2.1.mono_measure (Measure.restrict_mono (hUV i) le_rfl)))).aemeasurable.ennreal_ofReal)).mp hz
    filter_upwards [hl, hpd] with x hx hp
    by_contra hne0
    have := hp.dotProduct_mulVec_pos hne0
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero, Pi.sub_apply] at hx
    simp only [vecDot, matVecMul, dotProduct, Matrix.mulVec, star_trivial] at hx this
    linarith
  filter_upwards [h0, ae_restrict_mem (hU i).isOpen.measurableSet] with x hx hxU
  rw [hGk, indicator_of_mem hxU] at hx
  exact (sub_eq_zero.mp hx).symm

end
end CoarseDeGiorgi.Cubical
