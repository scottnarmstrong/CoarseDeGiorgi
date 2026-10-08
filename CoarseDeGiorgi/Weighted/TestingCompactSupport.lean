module

public import CoarseDeGiorgi.Weighted.TestingScalar
public import Mathlib.Geometry.Manifold.PartitionOfUnity

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal Manifold

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- A compact subset of an open set admits a smooth supported cutoff equal to
one in a neighborhood of every point of the compact subset. -/
theorem testing_exists_cutoff (hV : IsOpen V) {K : Set (Vec d)}
    (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ V ∧ ∀ x ∈ K, φ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨W, hWc, hWclosed, hKW, hWV⟩ := exists_compact_closed_between hK hV hKV
  obtain ⟨φ, hφone, hφzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, Vec d)) (n := (⊤ : ℕ∞)) hK.isClosed hKW
  have hsupport : Function.support φ ⊆ W := by
    intro x hx
    by_contra hxW
    exact hx (hφzero x hxW)
  refine ⟨φ, contMDiff_iff_contDiff.mp φ.contMDiff,
    HasCompactSupport.of_support_subset_isCompact hWc hsupport,
    (closure_minimal hsupport hWclosed).trans hWV, ?_⟩
  intro x hx
  exact hφone.filter_mono (nhds_le_nhdsSet hx)

/-- A pair vanishing outside a compact subset of V belongs to the
zero-boundary completion. This includes the nonnegative assertion in the
testing lemma `l.weighted.testing` and does not require a bound on the function. -/
theorem MemH1a.memH1a0_of_compact_support [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G) {K : Set (Vec d)} (hK : IsCompact K)
    (hKV : K ⊆ V) (hsupport : ∀ᵐ x ∂volume.restrict V, x ∉ K → u x = 0) :
    MemH1a0 a V u G := by
  obtain ⟨φ, hφ, hc, hs, hφone⟩ := testing_exists_cutoff hV.isOpen hK hKV
  obtain ⟨L, Φ, hΦ, hΦzero, hΦderiv, hΦbound, hΦgrowth, hΦlim, hdlim⟩ :=
    exists_testing_scalar_approximation
  have hi := (memH1a_memW11 hV hne ha hu).1
  let : IsFiniteMeasure (volume.restrict V) := hV.isFiniteMeasure_restrict_volume
  have hEG := MemH1a.energy_lt_top hV.isOpen ha hu
  have hφM := hφ.continuous.aestronglyMeasurable (μ := volume.restrict V)
  obtain ⟨C, hC⟩ := hφ.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hc.comp_left norm_zero)
  let B : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hφbound (x : Vec d) : |φ x| ≤ B :=
    (show ‖φ x‖ ≤ C from hC (Set.mem_range_self x)).trans (le_max_left _ _)
  have hφG : (fun x => φ x • G x) =ᵐ[volume.restrict V] G := by
    filter_upwards [hsupport, MemH1a.gradient_zero_on_level hV hne ha hu 0] with x hx hg
    by_cases hxK : x ∈ K
    · have hone := (hφone x hxK).eq_of_nhds
      change φ x = 1 at hone
      rw [hone, one_smul]
    · have hu0 := hx hxK
      have hG0 : G x = 0 := by simpa only [Set.mem_ofPred_eq, hu0, eq_self,
        Set.indicator_of_mem] using hg
      rw [hG0, smul_zero]
  have hφu : (fun x => φ x * u x) =ᵐ[volume.restrict V] u := by
    filter_upwards [hsupport] with x hx
    by_cases hxK : x ∈ K
    · have hone := (hφone x hxK).eq_of_nhds
      change φ x = 1 at hone
      rw [hone, one_mul]
    · rw [hx hxK, mul_zero]
  have hsecond (n : ℕ) : (fun x => Φ n (u x) • smoothGrad φ x) =ᵐ[volume.restrict V]
      (fun _ => 0) := by
    filter_upwards [hsupport] with x hx
    by_cases hxK : x ∈ K
    · have hgradzero : smoothGrad φ x = 0 := by
        funext i
        change fderiv ℝ φ x (basisVec i) = 0
        have hd := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).congr_of_eventuallyEq (hφone x hxK)
        rw [hd.fderiv]
        rfl
      rw [hgradzero, smul_zero]
    · rw [hx hxK, hΦzero n, zero_smul]
  have hpair (n : ℕ) : MemH1a0 a V (fun x => φ x * Φ n (u x))
      (fun x => φ x • (deriv (Φ n) (u x) • G x) + Φ n (u x) • smoothGrad φ x) := by
    obtain ⟨M, hM⟩ := hΦbound n
    exact MemH1a.cutoff_comp hV hne ha hu hφ hc hs (hΦ n) (hΦderiv n) hM
  have hvalueM (n : ℕ) := (hΦ n).continuous.comp_aestronglyMeasurable hu.1
  have hLip (n : ℕ) : LipschitzWith L (Φ n) := lipschitzWith_of_nnnorm_deriv_le (C := L)
    ((hΦ n).differentiable (by simp)) (fun t => NNReal.coe_le_coe.mp
      (by simpa only [coe_nnnorm, Real.norm_eq_abs] using hΦderiv n t))
  have hui : UnifIntegrable (fun n x => Φ n (u x)) 1 (volume.restrict V) := by
    apply (unifIntegrable_const (by norm_num) (by norm_num)
      (memLp_one_iff_integrable.mpr (hi.const_mul (L : ℝ)))).ae_mono hvalueM
    intro n
    filter_upwards with x
    simp only [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg L.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal (hΦgrowth n (u x))
  have hL : Tendsto (fun n => eLpNorm ((fun x => Φ n (u x)) - u) 1
      (volume.restrict V)) atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hvalueM
      (memLp_one_iff_integrable.mpr hi) hui
    exact Eventually.of_forall fun x => hΦlim (u x)
  have hLφ := testing_tendsto_l1_mul hvalueM hu.1 hφM hφbound hL
  have hvalue : Tendsto (fun n => eLpNorm ((fun x => φ x * Φ n (u x)) - u) 1
      (volume.restrict V)) atTop (𝓝 0) := by
    convert hLφ using 1
    funext n
    exact eLpNorm_congr_ae (EventuallyEq.rfl.sub hφu.symm)
  have hE := tendsto_energy_mul_zero ha hu.2.1 hEG
    (b := fun n x => φ x * (deriv (Φ n) (u x) - 1))
    (fun n => hφM.mul (((hΦ n).continuous_deriv (by simp)).comp_aestronglyMeasurable hu.1
      |>.sub aestronglyMeasurable_const))
    (M := (B : ℝ) * ((L : ℝ) + 1)) (fun n => ?_) ?_
  · apply memH1a0_of_tendsto hV hne ha hpair hi hu.2.1 hvalue
    convert hE using 1
    funext n
    apply energy_congr_ae
    filter_upwards [hφG, hsecond n] with x hx hy
    simp only [Pi.sub_apply, hy, add_zero, mul_smul, sub_smul, one_smul]
    rw [smul_sub, hx]
  · filter_upwards with x
    rw [abs_mul]
    exact mul_le_mul (hφbound x)
      ((abs_sub _ _).trans (by simpa only [abs_one] using add_le_add (hΦderiv n (u x)) le_rfl))
      (abs_nonneg _) B.coe_nonneg
  · filter_upwards with x
    simpa only [sub_self, mul_zero] using ((hdlim (u x)).sub_const 1).const_mul (φ x)


end CoarseDeGiorgi.Weighted
