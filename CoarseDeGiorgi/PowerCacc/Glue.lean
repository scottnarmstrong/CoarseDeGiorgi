import CoarseDeGiorgi.PowerCacc.Geometry
import CoarseDeGiorgi.Statements.WhitneyInterpolationDef
import CoarseDeGiorgi.Statements.WhitneyAffineExtensionDef
import CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension
import CoarseDeGiorgi.Harnack.Powers.SignedPower
import CoarseDeGiorgi.Harnack.PowerCaccioppoli.DomainSplit
import CoarseDeGiorgi.Weighted.Identification
import CoarseDeGiorgi.Weighted.ZeroCore
import CoarseDeGiorgi.Weighted.SmoothCore
import CoarseDeGiorgi.Whitney.ExteriorCells
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.MemH1a0

/-! # The signed power test with the glued extension of Proposition `p.whitney.extension`

The test function is `ψ = f` on `τ□̄₀` and `ψ = H_h f` outside (Proposition `p.whitney.extension`,
gluing clause). Weak-gradient uniqueness identifies the gradient `J` of `ψ` with the gradient of `f`
inside and with the gradient `GH` of the extension outside. -/

namespace CoarseDeGiorgi.PowerCacc

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal Classical

variable {d : ℕ}

/-- Weak gradients of functions that agree on an open set agree there almost everywhere. -/
theorem gradient_ae_eq_on_open {V U : Set (Vec d)} (hU : IsOpen U) (hUV : U ⊆ V)
    {ψ f : Vec d → ℝ} {J F : Vec d → Vec d}
    (hJ : HasWeakGradientOn V ψ J) (hJi : ∀ i, IntegrableOn (fun x => J x i) V)
    (hF : HasWeakGradientOn U f F) (hFi : ∀ i, IntegrableOn (fun x => F x i) U)
    (hEq : ∀ x ∈ U, ψ x = f x) :
    J =ᵐ[volume.restrict U] F := by
  have hJU : HasWeakGradientOn U ψ J := HasWeakGradientOn.restrict hU hUV hJ
  have hloc (g : Vec d → ℝ) (hg : IntegrableOn g U volume) :
      LocallyIntegrableOn g U volume := hg.locallyIntegrableOn
  have hc (i : Fin d) : (fun x => J x i) =ᵐ[volume.restrict U] (fun x => F x i) := by
    refine HasWeakPartialDerivOn.ae_eq hU (hloc _ ((hJi i).mono_set hUV)) (hloc _ (hFi i))
      ?_ (hF i)
    intro φ hφ hc hs
    have := hJU i φ hφ hc hs
    rw [← this]
    exact (setIntegral_congr_fun hU.measurableSet fun x hx => by rw [hEq x hx]).symm
  filter_upwards [ae_all_iff.mpr hc] with x hx
  funext i
  exact hx i

/-- The signed power test inequality for an admissible `ψ`, with integrability of both sides. -/
theorem signed_power_test_integrable [NeZero d] {a : CoeffField d}
    (ha : IsWeightedCoeffOn (originCube 1) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a (originCube 1) u G)
    (hsup : IsWeightedSubsolution a (originCube 1) (-u) (-G))
    (hnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x)
    (ε m r : ℝ) (hε : 0 < ε) (hm : m < 1 / 2) (hm0 : m ≠ 0)
    (hr1 : 1 < r) (hr2 : r < 2)
    {ψ : Vec d → ℝ} {J : Vec d → Vec d}
    (hψ : MemH1a0 a (originCube 1) ψ J)
    (hψnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ ψ x)
    (B : ℝ) (hψbound : ∀ᵐ x ∂volume.restrict (originCube 1), |ψ x| ≤ B)
    (K : Set (Vec d)) (hK : IsCompact K) (hKV : K ⊆ originCube 1)
    (hψzero : ∀ᵐ x ∂volume.restrict (originCube 1), x ∉ K → ψ x = 0) :
    m * (∫ x in originCube 1, vecDot (J x)
        (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) ≥
      (1 - m) * (∫ x in originCube 1,
        (ψ x / ((u x + ε) ^ m)) *
          vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
            (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) ∧
    IntegrableOn (fun x => vecDot (J x)
      (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) (originCube 1) ∧
    IntegrableOn (fun x => (ψ x / ((u x + ε) ^ m)) *
      vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
        (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) (originCube 1) := by
  obtain ⟨hV, hne⟩ := Assembly.theoremA_unitCube_domain d
  have hpackage := Harnack.Powers.signedPower_source_package hV hne ha hu hsup
    hnonneg ε m r hε hm hm0 hr1 hr2
  have htest := hpackage.2.2.2.2 (Weighted.MemH1a0.memH1a ha hψ)
    hψnonneg ⟨B, hψbound⟩ hK hKV hψzero
  have hchain := Harnack.Powers.signedPower_chain hV hne ha hu hnonneg ε m hε hm
  have hψmem := Weighted.MemH1a0.memH1a ha hψ
  have hψenergy := Weighted.MemH1a.energy_lt_top hV.isOpen ha hψmem
  have huenergy := Weighted.MemH1a.energy_lt_top hV.isOpen ha hu
  have hpairing := Weighted.pairing_integrable_and_bound ha hψmem.2.1 hu.2.1
    hψenergy huenergy
  have hfactorBound : ∀ᵐ x ∂volume.restrict (originCube 1),
      |m * (u x + ε) ^ (m - 1)| ≤ |m| * ε ^ (m - 1) := by
    filter_upwards [hnonneg, hchain.2.2] with x hx hbound
    have hpowNonneg : 0 ≤ (u x + ε) ^ (m - 1) :=
      Real.rpow_nonneg (by linarith [hε]) _
    rw [abs_mul, abs_of_nonneg hpowNonneg]
    exact mul_le_mul_of_nonneg_left hbound (abs_nonneg m)
  have hfactorMeas : AEStronglyMeasurable
      (fun x => m * (u x + ε) ^ (m - 1))
      (volume.restrict (originCube 1)) := by
    exact aestronglyMeasurable_const.mul hchain.2.1.1
  have hleftIntegrable : IntegrableOn (fun x => vecDot (J x)
      (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) (originCube 1) := by
    have h := hpairing.1.bdd_mul hfactorMeas hfactorBound
    have heq : (fun x => vecDot (J x)
        (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) =ᵐ[
        volume.restrict (originCube 1)]
        (fun x => (m * (u x + ε) ^ (m - 1)) *
          vecDot (J x) (matVecMul (a x) (G x))) := by
      filter_upwards with x
      simp only [matVecMul_smul, vecDot_smul_right]
    exact h.congr heq.symm
  have hsource := hpackage.2.2.1
  have hψfactorBound : ∀ᵐ x ∂volume.restrict (originCube 1), |ψ x| ≤ max B 0 := by
    filter_upwards [hψbound] with x hx
    exact hx.trans (le_max_left _ _)
  have hψsource : IntegrableOn
      (fun x => ψ x * (m ^ 2 * (u x + ε) ^ (m - 2) *
        vecDot (G x) (matVecMul (a x) (G x)))) (originCube 1) := by
    exact hsource.bdd_mul hψ.1 (hψfactorBound.mono fun x hx => by
      simpa only [Real.norm_eq_abs] using hx)
  have hquotientEq : (fun x => (ψ x / ((u x + ε) ^ m)) *
      vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
        (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) =ᵐ[
      volume.restrict (originCube 1)]
      (fun x => ψ x * (m ^ 2 * (u x + ε) ^ (m - 2) *
        vecDot (G x) (matVecMul (a x) (G x)))) := by
    filter_upwards [hnonneg, hpackage.2.2.2.1] with x hx hidentity
    rw [div_eq_mul_inv]
    calc
      ψ x * ((u x + ε) ^ m)⁻¹ *
          vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
            (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x)) =
          ψ x * (((u x + ε) ^ m)⁻¹ *
            vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
              (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) := by ring
      _ = ψ x * (m ^ 2 * (u x + ε) ^ (m - 2) *
          vecDot (G x) (matVecMul (a x) (G x))) := by rw [hidentity]
  exact ⟨htest, hleftIntegrable, hψsource.congr hquotientEq.symm⟩

/-- The conclusion of the signed power test split at radius `τ` for the interior function `f` (with
gradient `Fg`), exterior gradient `GHx` and glued test function `ψ`. -/
def SplitTest (a : CoeffField d) (u : Vec d → ℝ) (G : Vec d → Vec d) (ε m τ : ℝ)
    (f : Vec d → ℝ) (Fg GHx : Vec d → Vec d) (ψ : Vec d → ℝ) : Prop :=
  let v := fun x => (u x + ε) ^ m
  let H := fun x => (m * (u x + ε) ^ (m - 1)) • G x
  ψ =ᵐ[volume.restrict (originCube τ)] f ∧
      IntegrableOn (fun x => (f x / v x) * vecDot (H x) (matVecMul (a x) (H x)))
        (originCube τ) ∧
      IntegrableOn (fun x => (ψ x / v x) * vecDot (H x) (matVecMul (a x) (H x)))
        (originCube 1 \ originCube τ) ∧
      (0 ≤ᵐ[volume.restrict (originCube τ)] fun x =>
        (f x / v x) * vecDot (H x) (matVecMul (a x) (H x))) ∧
      (0 ≤ ∫ x in originCube τ,
        (f x / v x) * vecDot (H x) (matVecMul (a x) (H x))) ∧
      (0 ≤ ∫ x in originCube 1 \ originCube τ,
        (ψ x / v x) * vecDot (H x) (matVecMul (a x) (H x))) ∧
      m * ((∫ x in originCube τ,
          vecDot (Fg x) (matVecMul (a x) (H x))) +
        ∫ x in originCube 1 \ closedReferenceCube τ,
          vecDot (GHx x) (matVecMul (a x) (H x))) ≥
      (1 - m) * ((∫ x in originCube τ,
          (f x / v x) * vecDot (H x) (matVecMul (a x) (H x))) +
        ∫ x in originCube 1 \ originCube τ,
          (ψ x / v x) * vecDot (H x) (matVecMul (a x) (H x)))

/-- The signed test with the glued extension, split into the interior pairing against `∇f` and the
exterior pairing against the gradient `GHx` of the piecewise harmonic extension. -/
theorem signed_test_split [NeZero d] {a : CoeffField d}
    (ha : IsWeightedCoeffOn (originCube 1) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a (originCube 1) u G)
    (hsup : IsWeightedSubsolution a (originCube 1) (-u) (-G))
    (hunonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x)
    (ε m r : ℝ) (hε : 0 < ε) (hm : m < 1 / 2) (hm0 : m ≠ 0)
    (hr1 : 1 < r) (hr2 : r < 2)
    {τ R : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) (hRone : R ≤ 1)
    {M : ℝ} {f : Vec d → ℝ} {Fg : Vec d → Vec d}
    (hf : MemH1a a (originCube 1) f Fg)
    (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ M)
    (hfL : ∃ K : ℝ≥0, LipschitzOnWith K f (closedReferenceCube τ))
    {Hx : Vec d → ℝ} {GHx : Vec d → Vec d}
    (hrange : ∀ᵐ x ∂volume.restrict (closedReferenceCube (d := d) τ)ᶜ,
      0 ≤ Hx x ∧ Hx x ≤ M)
    (hGHint : Integrable GHx
      (volume.restrict (originCube (d := d) 1 \ closedReferenceCube τ)))
    (hHw : HasWeakGradientOn (originCube (d := d) 1 \ closedReferenceCube τ) Hx GHx)
    (hglue : ∀ w : Vec d → ℝ,
      (∃ K : ℝ≥0, LipschitzOnWith K w (closedReferenceCube (d := d) τ)) →
      (∀ y ∈ cubeSurface (d := d) τ, w y = f y) →
      ∃ G' : Vec d → Vec d,
        MemH1a0 a (originCube (d := d) 1)
          (fun x => if x ∈ closedReferenceCube (d := d) τ then w x else Hx x) G' ∧
        (∃ K : Set (Vec d), IsCompact K ∧ K ⊆ originCube (d := d) R ∧
          ∀ᵐ x ∂volume, x ∉ K →
            (if x ∈ closedReferenceCube (d := d) τ then w x else Hx x) = 0) ∧
        ((∀ x ∈ closedReferenceCube (d := d) τ, 0 ≤ w x) →
          ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)),
            0 ≤ (if x ∈ closedReferenceCube (d := d) τ then w x else Hx x))) :
    ∃ ψ : Vec d → ℝ, SplitTest a u G ε m τ f Fg GHx ψ := by
  obtain ⟨hV, hne⟩ := Assembly.theoremA_unitCube_domain d
  let H : Vec d → Vec d := fun x => (m * (u x + ε) ^ (m - 1)) • G x
  let v : Vec d → ℝ := fun x => (u x + ε) ^ m
  have hsub : originCube (d := d) τ ⊆ originCube 1 := by
    intro x hx i
    have := hx i
    constructor <;> linarith [this.1, this.2]
  have hU : IsOpenBoundedConvexDomain (originCube (d := d) τ) :=
    Whitney.source_cube_domain hτ0
  obtain ⟨G', hψ, ⟨K, hKc, hKR, hKzero⟩, hnn⟩ := hglue f hfL (fun _ _ => rfl)
  set ψ : Vec d → ℝ := fun x => if x ∈ closedReferenceCube (d := d) τ then f x else Hx x
    with hψdef
  have hψnn := hnn (fun x _ => hf0 x)
  have hM : 0 ≤ M := (hf0 0).trans (hfM 0)
  have hKV : K ⊆ originCube 1 := hKR.trans (Assembly.caccioppoli_cube_mono hRone)
  have hrange' : ∀ᵐ x ∂volume, x ∈ (closedReferenceCube (d := d) τ)ᶜ →
      0 ≤ Hx x ∧ Hx x ≤ M :=
    (ae_restrict_iff' (WhitneyInterp.isClosed_closedReferenceCube.measurableSet.compl)).mp hrange
  have hbound : ∀ᵐ x ∂volume.restrict (originCube (d := d) 1), |ψ x| ≤ M := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hrange'] with x hx
    by_cases hxc : x ∈ closedReferenceCube (d := d) τ
    · simp only [hψdef, ite_eq_left hxc]
      exact abs_le.mpr ⟨by linarith [hf0 x], hfM x⟩
    · have := hx hxc
      simp only [hψdef, ite_eq_right hxc]
      exact abs_le.mpr ⟨by linarith [this.1], this.2⟩
  have hzero : ∀ᵐ x ∂volume.restrict (originCube (d := d) 1), x ∉ K → ψ x = 0 :=
    ae_restrict_of_ae hKzero
  obtain ⟨htest, hLint, hRint⟩ := signed_power_test_integrable ha hu hsup hunonneg ε m r hε
    hm hm0 hr1 hr2 hψ hψnn M hbound K hKc hKV hzero
  -- identification of the gradient `G'` of `ψ`
  have hψW := Weighted.memH1a_memW11 hV hne ha (Weighted.MemH1a0.memH1a ha hψ)
  have hfW := Weighted.memH1a_memW11 hV hne ha hf
  have hinner : G' =ᵐ[volume.restrict (originCube τ)] Fg := by
    refine gradient_ae_eq_on_open (isOpen_originCube τ) hsub hψW.2.2.1 hψW.2.1
      (HasWeakGradientOn.restrict (isOpen_originCube τ) hsub hfW.2.2.1)
      (fun i => (hfW.2.1 i).mono_set hsub) ?_
    intro x hx
    simp only [hψdef, ite_eq_left (originCube_subset_closedReferenceCube τ hx)]
  have houter : G' =ᵐ[volume.restrict (originCube 1 \ closedReferenceCube τ)] GHx := by
    refine gradient_ae_eq_on_open isOpen_exterior sdiff_subset hψW.2.2.1 hψW.2.1 hHw
      (fun i => (hGHint.eval i)) ?_
    intro x hx
    simp only [hψdef, ite_eq_right hx.2]
  have hvpos : ∀ᵐ x ∂volume.restrict (originCube 1), 0 < v x := by
    filter_upwards [hunonneg] with x hx
    exact Real.rpow_pos_of_pos (by linarith only [hx, hε]) _
  have hq := Weighted.quadratic_nonneg ha H
  have hrightEq : (fun x => (ψ x / v x) * vecDot (H x) (matVecMul (a x) (H x)))
      =ᵐ[volume.restrict (originCube τ)]
      (fun x => (f x / v x) * vecDot (H x) (matVecMul (a x) (H x))) := by
    refine (ae_restrict_iff' (isOpen_originCube τ).measurableSet).mpr
      (Filter.Eventually.of_forall fun x hx => ?_)
    simp only [hψdef, ite_eq_left (originCube_subset_closedReferenceCube τ hx)]
  have hrightInner := (hRint.mono_set hsub).congr hrightEq
  have hrightOuter := hRint.mono_set (sdiff_subset :
    originCube 1 \ originCube τ ⊆ originCube (d := d) 1)
  have hrightNonneg : 0 ≤ᵐ[volume.restrict (originCube 1)]
      (fun x => (ψ x / v x) * vecDot (H x) (matVecMul (a x) (H x))) := by
    filter_upwards [hψnn, hvpos, hq] with x hxψ hxv hxq
    exact mul_nonneg (div_nonneg hxψ hxv.le) hxq
  have hinnerNonneg : 0 ≤ᵐ[volume.restrict (originCube τ)]
      (fun x => (f x / v x) * vecDot (H x) (matVecMul (a x) (H x))) := by
    filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hrightNonneg,
      hrightEq] with x hx heq
    rw [← heq]
    exact hx
  have houterNonneg := ae_mono
    (Measure.restrict_mono (sdiff_subset :
      originCube 1 \ originCube τ ⊆ originCube (d := d) 1) le_rfl) hrightNonneg
  have hsplit := Harnack.PowerCaccioppoli.signed_test_inequality_of_inner_outer_split
    (isOpen_originCube τ).measurableSet hsub _ _ hLint hRint m htest
  have hleftInner : (∫ x in originCube τ, vecDot (G' x) (matVecMul (a x) (H x))) =
      ∫ x in originCube τ, vecDot (Fg x) (matVecMul (a x) (H x)) := by
    apply integral_congr_ae
    filter_upwards [hinner] with x hx
    rw [hx]
  have hleftOuter : (∫ x in originCube 1 \ originCube τ,
      vecDot (G' x) (matVecMul (a x) (H x))) =
      ∫ x in originCube 1 \ closedReferenceCube τ,
        vecDot (GHx x) (matVecMul (a x) (H x)) := by
    rw [integral_exterior_closedReferenceCube hτ0 _ hU]
    apply integral_congr_ae
    filter_upwards [houter] with x hx
    rw [hx]
  have hrightInnerEq := integral_congr_ae hrightEq
  rw [hleftInner, hleftOuter, hrightInnerEq] at hsplit
  refine ⟨ψ, ?_⟩
  unfold SplitTest
  exact ⟨(ae_restrict_iff' (isOpen_originCube τ).measurableSet).mpr
      (Filter.Eventually.of_forall fun x hx => by
        simp only [hψdef, ite_eq_left (originCube_subset_closedReferenceCube τ hx)]),
    hrightInner, hrightOuter, hinnerNonneg, integral_nonneg_of_ae hinnerNonneg,
    integral_nonneg_of_ae houterNonneg, hsplit⟩

end CoarseDeGiorgi.PowerCacc
