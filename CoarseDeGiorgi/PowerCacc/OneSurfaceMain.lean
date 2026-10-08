module

public import CoarseDeGiorgi.Statements.GoodRadiusExists
public import CoarseDeGiorgi.PowerCacc.OneSurface
public import CoarseDeGiorgi.Assembly.HybridEmbedding

/-! # The one-surface estimate for powers, from the three extension statements -/

@[expose] public section

namespace CoarseDeGiorgi.PowerCacc

open Homogenization MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Classical

open Harnack.PowerCaccioppoli

theorem power_one_surface_of_extension
    (h71 : ExteriorIntegralHyp) (h62 : WhitneyHarmonicExtensionHyp)
    (hex : PiecewiseHarmonicExtensionExistsHyp) :
    ∀ n : ℕ, 3 ≤ n + 1 → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta (n + 1) p q s t →
      ∃ Csurf : ℝ≥0∞, Csurf < ⊤ ∧
        ∀ (a : CoeffField (n + 1)) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (u : Vec (n + 1) → ℝ) (G : Vec (n + 1) → Vec (n + 1)),
            (∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x) →
            IsWeightedSupersolution a (originCube 1) u G →
            ∀ ε : ℝ, 0 < ε → ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
              ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                ∀ h : ℝ, IsTriadicWidth h → 0 < h →
                  h ≤ (R - ρ) / (20000 * ((n + 1 : ℕ) : ℝ)) →
                  weightedEnergy a (originCube ρ)
                    (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ≤
                    Csurf * (ENNReal.ofReal (R - ρ)).rpow
                      (-gammaLoc p q t) *
                    (((ENNReal.ofReal (powerFactor m ^ 2) *
                        contrast a ha s t p q hs ht hp.le hq.le).rpow (1 / 2)) *
                        (ENNReal.ofReal h).rpow (paramTheta (n + 1) p q s t) *
                        weightedEnergy a (originCube R)
                          (fun x => (m * (u x + ε) ^ (m - 1)) • G x) +
                      ((ENNReal.ofReal (powerFactor m ^ 2) *
                        upperMoment a ha s p hs hp.le).rpow (1 / 2)) *
                        (ENNReal.ofReal h).rpow
                          (-(sigmaUpper (n + 1) p s + sigmaLower (n + 1) q t - t)) *
                        eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
                          (volume.restrict (originCube R)) *
                        (weightedEnergy a (originCube R)
                          (fun x => (m * (u x + ε) ^ (m - 1)) • G x)).rpow (1 / 2)) := by
  intro n hd p q s t hp hq hs ht hθ
  obtain ⟨hα0, hα1, hσ0, hθσ⟩ := power_surface_parameters hd hp hq hs ht hθ
  have hr := Assembly.theoremA_paramR_range hq
  obtain ⟨Cext, hCext, hext⟩ := h71 (n + 1) hd p q s t hp hq hs ht hθ
  obtain ⟨_, _, h62a⟩ := h62 (n + 1) hd (alphaParam t) (paramR q) hα0 hα1 hr.1.le hr.2.le
  obtain ⟨K, hK, hgr⟩ := CoarseDeGiorgi.good_radius_exists (n + 1) hd p q s t hp hq hs ht hθ
  let Csurf : ℝ≥0∞ := 2 * Cext * K * K ^ (1 / 2 : ℝ) * K
  have hCsurf : Csurf < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) hCext) hK)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.ne)) hK
  refine ⟨Csurf, hCsurf, ?_⟩
  intro a ha hrange u G hunonneg hsup ε hε m hm hm0 ρ R hρ hρR hR h htri hh hwidth
  let v : Vec (n + 1) → ℝ := fun x => (u x + ε) ^ m
  let H : Vec (n + 1) → Vec (n + 1) := fun x => (m * (u x + ε) ^ (m - 1)) • G x
  obtain ⟨hV, hne⟩ := Assembly.theoremA_unitCube_domain (n + 1)
  change IsWeightedSubsolution a (originCube 1) (-u) (-G) at hsup
  have hu : MemH1a a (originCube 1) u G := by
    have hneg := Weighted.MemH1a.neg hV hne ha hsup.1
    simpa only [neg_neg] using hneg
  have hpkg := Harnack.Powers.signedPower_source_package hV hne ha hu hsup hunonneg
    ε m (paramR q) hε hm hm0 hr.1 hr.2
  have hv : MemH1a a (originCube 1) v H := hpkg.1
  have hvnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ v x := by
    filter_upwards [hunonneg] with x hx
    exact Real.rpow_nonneg (by linarith only [hx, hε]) _
  have hER : weightedEnergy a (originCube R) H < ⊤ :=
    (Assembly.caccioppoli_energy_mono a H hR).trans_lt
      (Weighted.MemH1a.energy_lt_top hV.isOpen ha hv)
  have hY : eLpNorm v (ENNReal.ofReal (paramR q))
      (volume.restrict (originCube R)) < ⊤ :=
    (eLpNorm_mono_measure v
      (Measure.restrict_mono (Assembly.caccioppoli_cube_mono hR) le_rfl)).trans_lt
        hpkg.2.1.eLpNorm_lt_top
  have hmom := Assembly.caccioppoli_moments_finite hp hq hs ht hrange
  have hδ : 0 < R - ρ := sub_pos.mpr hρR
  have hδ1 : R - ρ ≤ 1 := by linarith only [hρ, hR]
  have hdim : (3 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hd
  have hden : 1 ≤ 20000 * ((n + 1 : ℕ) : ℝ) := by linarith only [hdim]
  have hh1 : h ≤ 1 := hwidth.trans
    ((div_le_one (by linarith only [hden])).mpr (hδ1.trans hden))
  have hcm : 0 ≤ powerFactor m := by
    unfold powerFactor
    exact div_nonneg (abs_nonneg _) (by linarith only [hm])
  -- one smooth sequence and one good radius, independent of the cap
  obtain ⟨vi, hvi, hL1, hEn⟩ := CoarseDeGiorgi.Selection.source_nonnegative_approximation
    hV hne ha hv hvnonneg
  have hmeasd (i : ℕ) : AEStronglyMeasurable (fun x => vi i x - v x)
      (volume.restrict (originCube 1)) :=
    (Weighted.memH1a_of_isSmoothCore hV.isOpen ha (hvi i).1).1.sub hv.1
  have hnorm := h1aWeightedNorm_tendsto_zero (a := a) (w := fun i x => vi i x - v x)
    (G := fun i x => smoothGrad (vi i) x - H x) hmeasd hL1 hEn
  obtain ⟨τ, hτ, ns, hns, hconv, hS, hD, hF, hLr, -, -⟩ := hgr a ha hrange v H hv
    hvnonneg ρ R hρ hρR hR hY vi (fun i => (hvi i).1) (fun i x _ => (hvi i).2 x) hnorm
  have hτI := CoarseDeGiorgi.Selection.selectionInterval_subset hρR hτ
  have hw := Whitney.source_width_at_selected_radius hd hρ hρR hR hτ hh hwidth
  have hτpos : 0 < τ := by linarith only [hw.1]
  have hτone : τ < 1 := hτI.2.trans_le hR
  have hρτ : ρ ≤ τ := hτI.1.le
  have hrp (y : ℝ) : (ENNReal.ofReal (R - ρ)).rpow y < ⊤ := by
    simp only [ENNReal.rpow_eq_pow]
    rw [ENNReal.ofReal_rpow_of_pos hδ]
    exact ENNReal.ofReal_lt_top
  have hLinv : (lowerMoment a ha t q ht hq.le).rpow (-(1 / 2)) < ⊤ :=
    ennreal_rpow_lt_top_of_nonpos (by norm_num) hmom.2.1.ne'
  have hSfin : sampledResponseSeries a ha s p τ < ⊤ := hS.trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK (hrp _))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hmom.1.ne))
  have hDfin : surfaceEnergyMaximal ρ R a ha H τ < ⊤ := hD.trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hδ))) hER)
  have hFfin : surfaceFracNorm τ (alphaParam t) (paramR q) v < ⊤ := hF.trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK (hrp _))
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hLinv
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hER.ne), hY⟩))
  have hZfin : eLpNorm v (ENNReal.ofReal (paramR q)) (surfaceMeasure τ) < ⊤ :=
    hLr.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hK (hrp _)) hY)
  have hsemiLe := Assembly.hybrid_surface_seminorm_le_norm τ (alphaParam t)
    (zero_lt_one.trans hr.1) v
  have hsemifin := hsemiLe.trans_lt hFfin
  have hCpair : Cext * sampledResponseSeries a ha s p τ *
      (surfaceEnergyMaximal ρ R a ha H τ) ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hCext hSfin)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hDfin.ne)
  -- the arithmetic inputs, in the form of `selected_surface_arithmetic`
  have hS' : sampledResponseSeries a ha s p τ ≤
      K * ENNReal.ofReal (R - ρ) ^ (-(1 / (2 * p))) *
        (upperMoment a ha s p hs hp.le) ^ (1 / 2 : ℝ) := by
    simpa only [ENNReal.rpow_eq_pow] using hS
  have hD' : surfaceEnergyMaximal ρ R a ha H τ ≤
      K * ENNReal.ofReal (R - ρ) ^ (-1 : ℝ) * weightedEnergy a (originCube R) H := by
    rw [ENNReal.rpow_neg_one]
    exact hD
  have hF' : surfaceFracSeminorm τ (alphaParam t) (paramR q) v ≤
      K * ENNReal.ofReal (R - ρ) ^ (-(alphaParam t + 1 / paramR q)) *
        ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
          (weightedEnergy a (originCube R) H) ^ (1 / 2 : ℝ) +
        eLpNorm v (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R))) := by
    have hexp : -alphaParam t - 1 / paramR q = -(alphaParam t + 1 / paramR q) := by ring
    have hexp2 : (-(1 / 2 : ℝ)) = -1 / 2 := by norm_num
    have := hsemiLe.trans hF
    simpa only [ENNReal.rpow_eq_pow, hexp, hexp2] using this
  have hZ' : eLpNorm v (ENNReal.ofReal (paramR q)) (surfaceMeasure τ) ≤
      K * ENNReal.ofReal (R - ρ) ^ (-(1 / paramR q)) *
        eLpNorm v (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R)) := by
    simpa only [ENNReal.rpow_eq_pow] using hLr
  have hcb : 1 / paramR q ≤ alphaParam t + 1 / paramR q := by linarith only [hα0]
  have hZpos : (0 : ℝ≥0∞) < 1 := one_pos
  -- the caps, for every finite level
  have hcapEq : ∀ (N : ℝ≥0∞) (f : Vec (n + 1) → ℝ), positiveCap f 0 N =
      Harnack.Selection.selectionCap 0 N f := fun N f => positiveCap_eq_cap f N
  apply uncapped_positive_cap_energy_bound a ha hv hvnonneg
    (Assembly.caccioppoli_cube_mono (hρR.le.trans hR))
  intro Nnat
  let N : ℝ≥0∞ := ((Nnat + 1 : ℕ) : ℝ≥0∞)
  have hN : N ≠ 0 := by simp only [N, Nat.cast_add, Nat.cast_one]; positivity
  have hNtop : N ≠ ⊤ := by dsimp only [N]; finiteness
  obtain ⟨hcapmem, hcapL1, hcapE⟩ := cap_approx_tendsto ha hv vi
    (fun i => (hvi i).1) hL1 hEn hN hNtop
  have hTraceFrac := hconv 0 N (pos_iff_ne_zero.mpr hN)
  have hTrace : Tendsto (fun i => surfaceFracNorm τ (alphaParam t) (paramR q)
      (Harnack.Selection.selectionCap 0 N (vi (ns i)) -
        Harnack.Selection.selectionCap 0 N v)) atTop (𝓝 0) := by
    refine hTraceFrac.congr fun i => ?_
    simp only [hcapEq]
    rfl
  have hLip (i : ℕ) : ∃ K' : ℝ≥0, LipschitzOnWith K'
      (Harnack.Selection.selectionCap 0 N (vi (ns i))) (closedReferenceCube τ) := by
    obtain ⟨K1, hK1⟩ := lipschitzOn_closedReferenceCube_of_isSmoothCore hτone (hvi (ns i)).1
    refine ⟨1 * K1, ?_⟩
    rw [cap_eq_capMap N hNtop]
    exact (capMap_lipschitzWith N).comp_lipschitzOnWith hK1
  have hLipSurf (i : ℕ) : ∃ K' : ℝ≥0, LipschitzOnWith K'
      (Harnack.Selection.selectionCap 0 N (vi (ns i))) (cubeSurface τ) := by
    obtain ⟨K', hK'⟩ := hLip i
    exact ⟨K', hK'.mono (cubeSurface_subset_closedReferenceCube τ)⟩
  have hwSurf (i : ℕ) : AEStronglyMeasurable
      (Harnack.Selection.selectionCap 0 N (vi (ns i))) (surfaceMeasure τ) := by
    obtain ⟨K', hK'⟩ := hLipSurf i
    exact (Whitney.seedSurface_integrable_of_continuousOn hτpos.le
      hK'.continuousOn).aestronglyMeasurable
  have htests : ∀ i, ∃ (GHx : Vec (n + 1) → Vec (n + 1)) (ψ : Vec (n + 1) → ℝ),
      SplitTest a u G ε m τ (Harnack.Selection.selectionCap 0 N (vi (ns i)))
        (Harnack.Selection.selectionCapGradient 0 N (vi (ns i))
          (smoothGrad (vi (ns i)))) GHx ψ ∧
      ENNReal.ofReal |∫ x in originCube 1 \ closedReferenceCube τ,
        vecDot (GHx x) (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))| ≤
      (Cext * sampledResponseSeries a ha s p τ *
        (surfaceEnergyMaximal ρ R a ha H τ) ^ (1 / 2 : ℝ)) *
        ((ENNReal.ofReal h ^ paramTheta (n + 1) p q s t) *
          surfaceFracSeminorm τ (alphaParam t) (paramR q)
            (Harnack.Selection.selectionCap 0 N (vi (ns i))) +
          (ENNReal.ofReal h ^ (-(sigmaUpper (n + 1) p s + sigmaLower (n + 1) q t - t))) *
            eLpNorm (Harnack.Selection.selectionCap 0 N (vi (ns i)))
              (ENNReal.ofReal (paramR q)) (surfaceMeasure τ)) := by
    intro i
    obtain ⟨Hx, GHx, hrep⟩ := hex (n + 1) hd a ha ρ R hρ hρR hR τ hτ h htri hw.2.2.1
      _ (hLipSurf i)
    have h71i := hext a ha hrange ρ R hρ hρR hR τ hτ h htri hwidth _ (hLipSurf i)
      v H hv Hx GHx hrep
    have h62i := (h62a a ha ρ R hρ hρR hR τ hτ h htri hw.2.2.1).2 _ (hLipSurf i)
      Hx GHx hrep
    obtain ⟨-, hrange0, -, hW11, -, -, -, hglue⟩ := h62i
    have hcb' := cap_bounds N hNtop (vi (ns i))
    have hrangeN := hrange0 0 N.toReal le_rfl ENNReal.toReal_nonneg
      (fun y _ => ⟨hcb' y |>.1, hcb' y |>.2⟩)
    obtain ⟨ψ, hψ⟩ := signed_test_split ha hu hsup hunonneg ε m (paramR q) hε hm hm0 hr.1 hr.2
      hτpos hτone hR (hcapmem (ns i)) (fun x => (hcb' x).1) (fun x => (hcb' x).2)
      (hLip i) hrangeN hW11.2.1 hW11.2.2.1 hglue
    exact ⟨GHx, ψ, hψ, by simpa only [ENNReal.rpow_eq_pow] using h71i.2.2⟩
  have hcapbound := selected_cap_energy_of_tests hτpos hτone hρτ a ha hu hsup hunonneg
    ε m (paramR q) (alphaParam t) hε hm hm0 hr.1 hr.2 N hN hNtop
    (fun i => Harnack.Selection.selectionCap 0 N (vi (ns i)))
    (fun i => Harnack.Selection.selectionCapGradient 0 N (vi (ns i))
      (smoothGrad (vi (ns i))))
    (fun i => hcapmem (ns i))
    (hcapL1.comp hns.tendsto_atTop) (hcapE.comp hns.tendsto_atTop) hTrace hwSurf
    _ _ _ hCpair
    (ENNReal.rpow_lt_top_of_nonneg hθ.le ENNReal.ofReal_ne_top)
    (ennreal_rpow_lt_top_of_nonpos (neg_nonpos.mpr hσ0)
      (ENNReal.ofReal_pos.mpr hh).ne')
    hsemifin hZfin htests
  have hcapbound' : weightedEnergy a (originCube ρ)
      (Harnack.Selection.selectionCapGradient 0 N v H) ≤
      ENNReal.ofReal (powerFactor m) * Cext * sampledResponseSeries a ha s p τ *
        (surfaceEnergyMaximal ρ R a ha H τ) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal h ^ paramTheta (n + 1) p q s t *
          surfaceFracSeminorm τ (alphaParam t) (paramR q) v +
          ENNReal.ofReal h ^ (-(sigmaUpper (n + 1) p s + sigmaLower (n + 1) q t - t)) *
            eLpNorm v (ENNReal.ofReal (paramR q)) (surfaceMeasure τ)) := by
    simpa only [mul_assoc, ENNReal.rpow_eq_pow] using hcapbound
  have hcollect := selected_surface_arithmetic hδ hδ1 hh1 hcb hθσ
    (ENNReal.ofReal (powerFactor m)) Cext K
    (upperMoment a ha s p hs hp.le) (lowerMoment a ha t q ht hq.le)
    (weightedEnergy a (originCube R) H)
    (eLpNorm v (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R)))
    _ _ _ _ _ hS' hD' hF' hZ' hcapbound'
  rw [exponent_identity_loc hq] at hcollect
  rw [← scaled_moment_half_power hcm, ← scaled_moment_half_power hcm] at hcollect
  exact hcollect

end CoarseDeGiorgi.PowerCacc
