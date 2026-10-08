import CoarseDeGiorgi.Assembly.HybridFractional
import CoarseDeGiorgi.Assembly.HybridInner
import CoarseDeGiorgi.Assembly.HybridParameters
import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.LowerFractional.Final
import CoarseDeGiorgi.Harnack.Powers.SignedPower
import CoarseDeGiorgi.Harnack.Iterations.NormalizedMomentOrder

namespace CoarseDeGiorgi.Harnack.ReverseMoments

open Homogenization MeasureTheory Set CoarseDeGiorgi.Localization
open Filter
open scoped ENNReal

noncomputable section

/-- Inner localization followed by the bulk fractional Sobolev embedding `dnpv_theorem_6_5`.
The localization input is the lower fractional estimate `lower_fractional_bound`. -/
theorem signed_power_inner_sobolev
    {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε →
            ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
              ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                eLpNorm (fun x => (u x + ε) ^ m)
                    (ENNReal.ofReal (rStarParam (d := d) q t))
                    (volume.restrict (originCube ρ)) ≤
                  C * ENNReal.ofReal (((R - ρ) / 2) ^ (-gammaOneParam (d := d) q t)) *
                    ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
                        weightedEnergy a (originCube ((ρ + R) / 2))
                          (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ^
                          (1 / 2 : ℝ) +
                      eLpNorm (fun x => (u x + ε) ^ m)
                        (ENNReal.ofReal (paramR q))
                        (volume.restrict (originCube ((ρ + R) / 2)))) := by
  obtain ⟨hα, hα1, hr, hr2, _, hcrit, _, hstar⟩ :=
    Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  have hr0 : 0 < paramR q := zero_lt_one.trans hr
  have halphaR : 0 < alphaParam t := hα
  have hunit := Assembly.hybrid_unitCube_domain (d := d)
  have hNe : NeZero d := ⟨by omega⟩
  obtain ⟨B, hB0, hB, hlocal⟩ :=
    Assembly.hybrid_fractional_localization_of_lower_fractional
      CoarseDeGiorgi.lower_fractional_proved d hd p q s t hp hq hs ht hθ
  have ⟨D, hD0, hD, hinner⟩ :=
    Assembly.hybrid_inner_critical_norm hα hα1 hr.le hcrit
  have hcritical : dnpvCriticalExponent d (alphaParam t) (paramR q) =
      rStarParam (d := d) q t := by
    rw [dnpvCriticalExponent]
    rfl
  let C := B * D
  refine ⟨C, ENNReal.mul_pos hB0.ne' hD0.ne',
    ENNReal.mul_lt_top hB hD, ?_⟩
  intro a ha hrange u G hnonneg hsup ε hε m hm hm0 ρ R hρ hρR hR
  let ρ' := (ρ + R) / 2
  have hρ' : ρ < ρ' := by dsimp [ρ']; linarith
  have hρ'R : ρ' < R := by dsimp [ρ']; linarith
  have hρ'1 : ρ' ≤ 1 := hρ'R.le.trans hR
  have hδ : 0 < ρ' - ρ := sub_pos.mpr hρ'
  have hδ1 : ρ' - ρ ≤ 1 := by linarith only [hρ, hρ'1]
  have hαr : 0 < alphaParam t * paramR q := mul_pos hα hr0
  change IsWeightedSubsolution a (originCube 1) (-u) (-G) at hsup
  have hpos : MemH1a a (originCube 1) u G := by
    have h := Weighted.MemH1a.neg hunit.1 hunit.2 ha hsup.1
    simpa only [Pi.neg_apply, neg_neg] using h
  have hpow := CoarseDeGiorgi.Harnack.Powers.signedPower_source_package hunit.1 hunit.2 ha
    hpos hsup hnonneg ε m (paramR q) hε hm hm0
    (by linarith only [hr]) (by linarith only [hr2])
  let v : Vec d → ℝ := fun x => (u x + ε) ^ m
  let Gv : Vec d → Vec d := fun x => (m * (u x + ε) ^ (m - 1)) • G x
  have hv : MemH1a a (originCube 1) v Gv := by
    simpa only [v, Gv] using hpow.1
  let v₀ := hv.1.mk v
  have hv₀M : Measurable v₀ := hv.1.measurable_mk
  have hev : v₀ =ᵐ[volume.restrict (originCube 1)] v := hv.1.ae_eq_mk.symm
  have hmem : MemH1a a (originCube 1) v₀ Gv :=
    Weighted.MemH1a.congr_ae hv hev.symm (Eventually.of_forall fun _ => rfl)
  have hGmeas : AEStronglyMeasurable Gv (volume.restrict (originCube 1)) := hmem.2.1
  have hqmeas := (Weighted.quadratic_aestronglyMeasurable ha hGmeas).aemeasurable.ennreal_ofReal
  let g := hqmeas.mk (fun x => ENNReal.ofReal (vecDot (Gv x) (matVecMul (a x) (Gv x))))
  have hg : Measurable g := hqmeas.measurable_mk
  have hge : g =ᵐ[volume.restrict (originCube 1)]
      (fun x => ENNReal.ofReal (vecDot (Gv x) (matVecMul (a x) (Gv x)))) :=
    hqmeas.ae_eq_mk.symm
  obtain ⟨k, hk0, hkgap, hkhi, hcover⟩ :=
    exists_inner_localization_cover (d := d) hρ hρ' hρ'1
  have hk1 : gridSpacing k ≤ 1 := by
    have hδ' : ρ' - ρ ≤ 1 := hδ1
    linarith only [hkhi, hδ']
  have hmargin : ρ + 4 * gridSpacing k < ρ' := inner_margin hρ' hkhi
  have hK : ∀ y ∈ {x : Vec d | ∀ i, |x i| ≤ ρ / 2}, ∀ i, |y i| ≤ ρ / 2 :=
    fun _ hy i => hy i
  have hloc := hlocal a ha hrange v₀ Gv hmem hv₀M g hg hge
    (ρ' - ρ) ρ' k {x : Vec d | ∀ i, |x i| ≤ ρ / 2} ρ hδ hδ1 hρ'1 hk1 hkgap hcover hK hmargin
  have hsemi : fracSeminorm univ (alphaParam t) (paramR q)
      (localizedFunction k (coverIndices k {x : Vec d | ∀ i, |x i| ≤ ρ / 2}) v₀) ≤
      B * ENNReal.ofReal ((ρ' - ρ) ^ (-gammaOneParam (d := d) q t)) *
        ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
            weightedEnergy a (originCube ρ') Gv ^ (1 / 2 : ℝ) +
          eLpNorm v₀ (ENNReal.ofReal (paramR q)) (volume.restrict (originCube ρ'))) := by
    exact (Foundations.FracGeometry.fracSeminorm_le_fracNorm _ _ hr0 _).trans hloc
  have hin := hinner ρ ρ' (ρ' - ρ) k hcover v₀ hv₀M _ hsemi
  have hEqInner : v₀ =ᵐ[volume.restrict (originCube ρ)] v := by
    have hρ1 : ρ ≤ 1 := hρR.le.trans hR
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Assembly.caccioppoli_cube_mono (d := d) hρ1) hev] with x hx
    exact hx
  have hEqOuter : v₀ =ᵐ[volume.restrict (originCube ρ')] v := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Assembly.caccioppoli_cube_mono (d := d) hρ'1) hev] with x hx
    exact hx
  rw [Assembly.hybrid_radiusCube_eq_originCube] at hin
  rw [eLpNorm_congr_ae hEqInner, eLpNorm_congr_ae hEqOuter] at hin
  have hin' : eLpNorm v (ENNReal.ofReal (rStarParam (d := d) q t))
      (volume.restrict (originCube ρ)) ≤
      D * (B * ENNReal.ofReal ((ρ' - ρ) ^ (-gammaOneParam (d := d) q t)) *
        ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
            weightedEnergy a (originCube ρ') Gv ^ (1 / 2 : ℝ) +
          eLpNorm v (ENNReal.ofReal (paramR q)) (volume.restrict (originCube ρ')))) := by
    simpa only [hcritical] using hin
  have hgapid : ρ' - ρ = (R - ρ) / 2 := by dsimp [ρ']; ring
  have hdelta : (ρ' - ρ) ^ (-gammaOneParam (d := d) q t) =
      ((R - ρ) / 2) ^ (-gammaOneParam (d := d) q t) := by rw [hgapid]
  calc
    _ ≤ D * (B * ENNReal.ofReal (((R - ρ) / 2) ^
          (-gammaOneParam (d := d) q t))) *
          ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
              weightedEnergy a (originCube ρ') Gv ^ (1 / 2 : ℝ) +
            eLpNorm v (ENNReal.ofReal (paramR q)) (volume.restrict (originCube ρ'))) := by
      rw [hdelta] at hin'
      simpa only [Assembly.hybrid_radiusCube_eq_originCube, mul_assoc, mul_comm, mul_left_comm]
        using hin'
    _ = _ := by
      dsimp [C]
      ring

end

end CoarseDeGiorgi.Harnack.ReverseMoments
