import CoarseDeGiorgi.PowerCacc.Glue
import CoarseDeGiorgi.Harnack.PowerCaccioppoli.CapFacts
import CoarseDeGiorgi.Harnack.PowerCaccioppoli.InteriorFatou
import CoarseDeGiorgi.Harnack.PowerCaccioppoli.InteriorLimit
import CoarseDeGiorgi.Harnack.PowerCaccioppoli.SignedLiminf
import CoarseDeGiorgi.Harnack.PowerCaccioppoli.ExteriorTraceBound
import CoarseDeGiorgi.Harnack.PowerCaccioppoli.SurfaceTraceLimits
import CoarseDeGiorgi.Harnack.Selection.Cap
import CoarseDeGiorgi.Statements.PowerFactor
import CoarseDeGiorgi.Statements.SurfaceFracNorm

/-! # The signed cap limit on one selected surface

The approximants are the caps `ṽ_i = v_i ∧ N` of one fixed smooth sequence `v_i → v`.  Each has an
extension test (`SplitTest`) and an exterior pairing bound; the limit `i → ∞` is taken as in the
proof of Proposition `p.power.caccioppoli`, Step 1. -/

namespace CoarseDeGiorgi.PowerCacc

open Homogenization MeasureTheory Set Filter Topology
open scoped ENNReal

open Harnack.PowerCaccioppoli

theorem selected_cap_energy_of_tests
    {d : ℕ} [NeZero d] {ρ τ : ℝ} (hτpos : 0 < τ) (hτone : τ < 1) (hρτ : ρ ≤ τ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a (originCube 1) u G)
    (hsup : IsWeightedSubsolution a (originCube 1) (-u) (-G))
    (hunonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x)
    (ε m r α : ℝ) (hε : 0 < ε) (hm : m < 1 / 2) (hm0 : m ≠ 0)
    (hr1 : 1 < r) (hr2 : r < 2) (N : ℝ≥0∞) (hN : N ≠ 0) (hNtop : N ≠ ⊤)
    (w : ℕ → Vec d → ℝ) (Fgr : ℕ → Vec d → Vec d)
    (hw : ∀ i, MemH1a a (originCube 1) (w i) (Fgr i))
    (hL1 : Tendsto (fun i => eLpNorm
      (w i - Harnack.Selection.selectionCap 0 N (fun x => (u x + ε) ^ m)) 1
      (volume.restrict (originCube 1))) atTop (𝓝 0))
    (hEnergy : Tendsto (fun i => weightedEnergy a (originCube 1)
      (Fgr i - Harnack.Selection.selectionCapGradient 0 N
        (fun x => (u x + ε) ^ m)
        (fun x => (m * (u x + ε) ^ (m - 1)) • G x))) atTop (𝓝 0))
    (hTrace : Tendsto (fun i => surfaceFracNorm τ α r
      (w i - Harnack.Selection.selectionCap 0 N (fun x => (u x + ε) ^ m)))
      atTop (𝓝 0))
    (hwSurf : ∀ i, AEStronglyMeasurable (w i) (surfaceMeasure τ))
    (C c₁ c₂ : ℝ≥0∞) (hC : C < ⊤) (hc₁ : c₁ < ⊤) (hc₂ : c₂ < ⊤)
    (hsemi : surfaceFracSeminorm τ α r (fun x => (u x + ε) ^ m) < ⊤)
    (hlr : eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal r)
      (surfaceMeasure τ) < ⊤)
    (htests : ∀ i, ∃ (GHx : Vec d → Vec d) (ψ : Vec d → ℝ),
      SplitTest a u G ε m τ (w i) (Fgr i) GHx ψ ∧
      ENNReal.ofReal |∫ x in originCube 1 \ closedReferenceCube τ,
        vecDot (GHx x) (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))| ≤
      C * (c₁ * surfaceFracSeminorm τ α r (w i) +
        c₂ * eLpNorm (w i) (ENNReal.ofReal r) (surfaceMeasure τ))) :
    weightedEnergy a (originCube ρ)
      (Harnack.Selection.selectionCapGradient 0 N (fun x => (u x + ε) ^ m)
        (fun x => (m * (u x + ε) ^ (m - 1)) • G x)) ≤
      ENNReal.ofReal (powerFactor m) * C *
        (c₁ * surfaceFracSeminorm τ α r (fun x => (u x + ε) ^ m) +
          c₂ * eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal r)
            (surfaceMeasure τ)) := by
  classical
  let v : Vec d → ℝ := fun x => (u x + ε) ^ m
  let H : Vec d → Vec d := fun x => (m * (u x + ε) ^ (m - 1)) • G x
  let cap := Harnack.Selection.selectionCap 0 N v
  let capGrad := Harnack.Selection.selectionCapGradient 0 N v H
  obtain ⟨hV, hne⟩ := Assembly.theoremA_unitCube_domain d
  have hpkg := Harnack.Powers.signedPower_source_package hV hne ha hu hsup
    hunonneg ε m r hε hm hm0 hr1 hr2
  have hv : MemH1a a (originCube 1) v H := hpkg.1
  have hvpos : ∀ᵐ x ∂volume.restrict (originCube 1), 0 < v x := by
    filter_upwards [hunonneg] with x hx
    exact Real.rpow_pos_of_pos (by linarith only [hx, hε]) _
  have hcap : MemH1a a (originCube 1) cap capGrad :=
    Harnack.Selection.selectionCap_memH1a a ha hv 0 N hN
  have hU := Whitney.source_cube_domain (d := d) hτpos
  have hsub : originCube (d := d) τ ⊆ originCube 1 := by
    intro x hx i
    have := hx i
    constructor <;> linarith [this.1, this.2]
  have haU := LowerFractional.weightedCoeffOn_mono ha hsub
  have hcapU := LowerFractional.memH1a_restrict hV hne ha hU hsub hcap
  have hE := Weighted.MemH1a.energy_lt_top hU.isOpen haU hcapU
  have hvU := LowerFractional.memH1a_restrict hV hne ha hU hsub hv
  have hvposU := ae_mono (Measure.restrict_mono hsub le_rfl) hvpos
  have hratio := positive_cap_ratio_integrable_nonneg a haU hvU.1 hvU.2.1
    (Weighted.MemH1a.energy_lt_top hU.isOpen haU hvU) hvposU N
  choose GHx ψ hsplit hpair using htests
  obtain ⟨ns, hns, hpoint⟩ := exists_subsequence_ae_of_L1_tendsto
    (volume.restrict (originCube 1)) w cap hL1
  have hpointU := ae_mono (Measure.restrict_mono hsub le_rfl) hpoint
  have hFatou := positive_cap_energy_le_liminf_ratio_integrals hU.isOpen a haU
    hcapU hvposU hNtop hratio.1 hratio.2 (fun i => w (ns i))
    (fun i => (hsplit (ns i)).2.1) (fun i => (hsplit (ns i)).2.2.2.1) hpointU
  have hpairingEnergy := positive_cap_pairing_eq_energy a haU v H N hcapU.2.1
  have hA : Tendsto (fun i => ∫ x in originCube τ,
      vecDot (Fgr (ns i) x) (matVecMul (a x) (H x))) atTop
      (𝓝 (∫ x in originCube τ, vecDot (capGrad x) (matVecMul (a x) (H x)))) := by
    have hbase := pairing_tendsto_on_subset_of_energy_approximation
      hU.isOpen.measurableSet hsub a ha
      (fun n => (hw n).2.1) hcap.2.1 hv.2.1
      (fun n => Weighted.MemH1a.energy_lt_top hV.isOpen ha (hw n))
      (Weighted.MemH1a.energy_lt_top hV.isOpen ha hcap)
      (Weighted.MemH1a.energy_lt_top hV.isOpen ha hv)
      hEnergy
    simpa only [Function.comp_def] using hbase.comp hns.tendsto_atTop
  rw [hpairingEnergy] at hA
  have hvSurf : AEStronglyMeasurable v (surfaceMeasure τ) :=
    aestronglyMeasurable_of_eLpNorm_ne_top hlr.ne
  have hcapSurf := positive_cap_aestronglyMeasurable hvSurf N
  have hsemiCap := positive_cap_surface_seminorm_le τ α r (zero_lt_one.trans hr1) v N
  have hlrCap := positive_cap_eLpNorm_le v N (ENNReal.ofReal r)
    (surfaceMeasure τ) hcapSurf
  have htraceCap := selected_trace_components_eventually_close hr1 cap w
    hcapSurf hwSurf (hsemiCap.trans_lt hsemi) hTrace
  have htracePower : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop,
      surfaceFracSeminorm τ α r (w i) ≤ surfaceFracSeminorm τ α r v +
        ENNReal.ofReal δ ∧
      eLpNorm (w i) (ENNReal.ofReal r) (surfaceMeasure τ) ≤
        eLpNorm v (ENNReal.ofReal r) (surfaceMeasure τ) + ENNReal.ofReal δ := by
    intro δ hδ
    filter_upwards [htraceCap δ hδ] with i hi
    exact ⟨hi.1.trans (add_le_add hsemiCap le_rfl),
      hi.2.trans (add_le_add hlrCap le_rfl)⟩
  let B : ℕ → ℝ := fun i => ∫ x in originCube 1 \ closedReferenceCube τ,
    vecDot (GHx i x) (matVecMul (a x) (H x))
  let B₀ : ℝ≥0∞ := C * (c₁ * surfaceFracSeminorm τ α r v +
    c₂ * eLpNorm v (ENNReal.ofReal r) (surfaceMeasure τ))
  have hB₀ : B₀ < ⊤ := ENNReal.mul_lt_top hC
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hc₁ hsemi,
      ENNReal.mul_lt_top hc₂ hlr⟩)
  have hB := pairing_abs_eventually_close_of_ennreal_trace_bounds C c₁ c₂ _ _
    hC hc₁ hc₂ hsemi hlr _ _ htracePower B hpair
  have hBsub : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop, |B (ns i)| ≤ B₀.toReal + δ := by
    intro δ hδ
    exact hns.tendsto_atTop.eventually (hB δ hδ)
  have hFatouReal : ENNReal.ofReal (weightedEnergy a (originCube τ) capGrad).toReal ≤
      liminf (fun i => ENNReal.ofReal (∫ x in originCube τ,
        (w (ns i) x / v x) * vecDot (H x) (matVecMul (a x) (H x)))) atTop := by
    rw [ENNReal.ofReal_toReal hE.ne]
    exact hFatou
  have hlimit := signed_surface_bound_of_liminf hm hm0 ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg
    (fun i => ∫ x in originCube τ,
      vecDot (Fgr (ns i) x) (matVecMul (a x) (H x)))
    (fun i => B (ns i))
    (fun i => ∫ x in originCube τ,
      (w (ns i) x / v x) * vecDot (H x) (matVecMul (a x) (H x)))
    (fun i => ∫ x in originCube 1 \ originCube τ,
      (ψ (ns i) x / v x) * vecDot (H x) (matVecMul (a x) (H x)))
    hA hFatouReal hBsub (fun i => (hsplit (ns i)).2.2.2.2.1)
    (fun i => (hsplit (ns i)).2.2.2.2.2.1) (fun i => (hsplit (ns i)).2.2.2.2.2.2)
  have hcm : 0 ≤ powerFactor m := by
    unfold powerFactor
    exact div_nonneg (abs_nonneg _) (by linarith only [hm])
  calc
    weightedEnergy a (originCube ρ) capGrad ≤ weightedEnergy a (originCube τ) capGrad := by
      apply lintegral_mono_set
      intro x hx i
      have hx' := hx i
      have : ρ / 2 ≤ τ / 2 := by linarith
      constructor <;> linarith [hx'.1, hx'.2]
    _ = ENNReal.ofReal (weightedEnergy a (originCube τ) capGrad).toReal :=
      (ENNReal.ofReal_toReal hE.ne).symm
    _ ≤ ENNReal.ofReal (powerFactor m * B₀.toReal) := ENNReal.ofReal_le_ofReal hlimit
    _ = ENNReal.ofReal (powerFactor m) * B₀ := by
      rw [ENNReal.ofReal_mul hcm, ENNReal.ofReal_toReal hB₀.ne]
    _ = _ := by rw [mul_assoc]

end CoarseDeGiorgi.PowerCacc
