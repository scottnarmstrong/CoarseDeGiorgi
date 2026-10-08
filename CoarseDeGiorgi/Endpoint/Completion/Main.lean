import CoarseDeGiorgi.Endpoint.Completion.Algebra
import CoarseDeGiorgi.Endpoint.Completion.Norms
import CoarseDeGiorgi.Endpoint.Source.Measure
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.MemH1a0
import CoarseDeGiorgi.Harnack.Moments.MomentComparison
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.RStarParam
import CoarseDeGiorgi.Statements.NonnegativeEssInf

/-! Completion of the proof of Theorem C (`t.harnack`) at the endpoint `η = r*/2` and below, from
`p.endpoint.potential`, `l.source.mass` and `e.interior.harnack`, taken as hypotheses in their exact form. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Endpoint

theorem weak_harnack_range_of_endpoint (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (h_endpoint_potential :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p s : ℝ) (hp : 1 < p) (hs : 0 < s),
        0 < paramTheta d p q s t →
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (ν : Measure (Vec d)), IsFiniteMeasure ν → ν (originCube 1)ᶜ = 0 →
          (∃ M : ℝ, 0 ≤ M ∧
            ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
              tsupport φ ⊆ originCube 1 →
              ENNReal.ofReal |∫ x, φ x ∂ν| ≤
                ENNReal.ofReal M *
                  (weightedEnergy a (originCube 1) (smoothGrad φ)).rpow (1 / 2)) →
        ∀ (v : Vec d → ℝ) (Gv : Vec d → Vec d),
          MemH1a0 a (originCube 1) v Gv →
          (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
              tsupport φ ⊆ originCube 1 →
              ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume =
                ∫ x, φ x ∂ν) →
          eLpNorm v (ENNReal.ofReal (rStarParam (d := d) q t / 2))
              (volume.restrict (originCube 1)) ≤
            ENNReal.ofReal C * (lowerMoment a ha t q ht hq.le)⁻¹ * ν (originCube 1))
    (h_source_mass_potential :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∃ μ : Measure (Vec d),
            μ (originCube 1)ᶜ = 0 ∧
            (∀ K : Set (Vec d), IsCompact K → K ⊆ originCube 1 → μ K < ⊤) ∧
            (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ originCube 1 →
                ∫ x, φ x ∂μ =
                  ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) ∂volume) ∧
            μ (originCube (3 / 4)) ≤
              ENNReal.ofReal C * upperMoment a ha s p hs hp.le *
                ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
                nonnegativeEssInf (originCube (1 / 2)) u ∧
            IsFiniteMeasure (μ.restrict (originCube (3 / 4))) ∧
            (∃ M : ℝ, 0 ≤ M ∧
              ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ originCube 1 →
                ENNReal.ofReal |∫ x, φ x ∂(μ.restrict (originCube (3 / 4)))| ≤
                  ENNReal.ofReal M *
                    (weightedEnergy a (originCube 1) (smoothGrad φ)).rpow (1 / 2)) ∧
            ∃ (V : Vec d → ℝ) (Gv : Vec d → Vec d),
              MemH1a0 a (originCube 1) V Gv ∧
              (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ originCube 1 →
                ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume =
                  ∫ x, φ x ∂(μ.restrict (originCube (3 / 4)))) ∧
              (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ V x ∧ V x ≤ u x) ∧
              IsWeightedSolution a (originCube (3 / 4)) (fun x => u x - V x)
                (fun x => G x - Gv x))
    (h_interior_harnack :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube (3 / 4))), 0 ≤ u x) →
          IsWeightedSolution a (originCube (3 / 4)) u G →
          eLpNorm u ⊤ (volume.restrict (originCube (5 / 8))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u) :
    ∀ (η : ℝ) (hη : 0 < η), η ≤ rStarParam (d := d) q t / 2 →
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          normalizedLpMoment η hη (originCube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u := by
  intro η hη hηr
  have hr : 0 < rStarParam (d := d) q t / 2 := hη.trans_le hηr
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Cp, hCp, hpotential⟩ := h_endpoint_potential
  obtain ⟨Cm, hCm, hmass⟩ := h_source_mass_potential
  obtain ⟨Ch, hCh, hharnack⟩ := h_interior_harnack
  obtain ⟨A, D, hA, hD, hnorm⟩ := completion_norm_bound d _ hr
  let K := A * Cp * Cm
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg hA hCp) hCm
  refine ⟨K + D + Cm + Ch + 2, by positivity, ?_⟩
  intro a ha hupper hlower u G hu0 hu
  obtain ⟨μ, hμ0, _, _, hμmass, hνfin, hνbd,
    V, Gv, hVmem, hVrep, hVbounds, hwsol⟩ := hmass a ha hupper hlower u G hu0 hu
  let ν := μ.restrict (originCube (3 / 4))
  have hν0 : ν (originCube 1)ᶜ = 0 :=
    le_antisymm ((Measure.restrict_le_self (s := originCube (3 / 4)) (μ := μ) _).trans hμ0.le)
      zero_le
  have hV0 := hVbounds.mono fun _ hx => hx.1
  have hVu := hVbounds.mono fun _ hx => hx.2
  have hVnorm := hpotential p s hp hs _hθ a ha hupper hlower ν hνfin hν0 hνbd V Gv hVmem hVrep
  have hμeq : ν (originCube 1) = μ (originCube (3 / 4)) := by
    rw [Measure.restrict_apply (originCube_domain one_pos).isOpen.measurableSet,
      Set.inter_eq_right.mpr (originCube_mono' (by norm_num) one_pos (by norm_num))]
  rw [hμeq] at hVnorm
  have hVbound := hVnorm.trans (mul_le_mul_of_nonneg_left hμmass zero_le)
  have h31 : originCube (d := d) (3 / 4) ⊆ originCube 1 :=
    originCube_mono' (by norm_num) one_pos (by norm_num)
  have hw0 : ∀ᵐ x ∂(volume.restrict (originCube (3 / 4))), 0 ≤ u x - V x := by
    filter_upwards [ae_mono (Measure.restrict_mono h31 le_rfl) hVu] with x hx
    exact sub_nonneg.mpr hx
  have hwi : nonnegativeEssInf (originCube (1 / 2)) (fun x => u x - V x) ≤
      nonnegativeEssInf (originCube (1 / 2)) u := by
    refine essInf_mono_ae ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [ae_mono (Measure.restrict_mono
      (originCube_mono' (by norm_num) one_pos (by norm_num)) le_rfl) hV0] with x hx
    exact ENNReal.ofReal_le_ofReal (sub_le_self _ hx)
  have hwbound := (hharnack a ha hupper hlower _ _ hw0 hwsol).trans
    (mul_le_mul_of_nonneg_left hwi zero_le)
  have humeas := (supersolution_memH1a (originCube_domain one_pos)
    (originCube_nonempty one_pos) ha hu).1
  have hVmeas := (Weighted.MemH1a0.memH1a ha hVmem).1
  have hE := originCube_domain (d := d) (by norm_num : (0 : ℝ) < 5 / 8)
  let : IsFiniteMeasure (volume.restrict (originCube (d := d) (5 / 8))) :=
    hE.isFiniteMeasure_restrict_volume
  have hEtop : volume (originCube (d := d) (5 / 8)) ≠ ⊤ := by
    simpa only [Measure.restrict_apply_univ] using
      measure_ne_top (volume.restrict (originCube (d := d) (5 / 8))) Set.univ
  have hmono := Harnack.Iterations.normalizedLpMoment_mono
    (originCube (5 / 8)) u hη hηr
    (humeas.mono_measure (Measure.restrict_mono
      (originCube_mono' (by norm_num) one_pos (by norm_num)) le_rfl))
    (hE.isOpen.measure_pos volume (originCube_nonempty (by norm_num))) hEtop
  have hnormbound := (hnorm u V humeas hVmeas).trans
    (add_le_add (mul_le_mul_of_nonneg_left hVbound zero_le) (mul_le_mul_of_nonneg_left hwbound zero_le))
  let Θ := contrast a ha s t p q hs ht hp.le hq.le
  have hΘfin : Θ ≠ ⊤ := ENNReal.div_ne_top hupper.ne hlower.ne'
  have hΘone : 1 ≤ Θ := Harnack.Moments.moment_contrast_ge_one (by omega)
    a ha hs ht hp.le hq.le hupper hlower
  have hΘreal : 1 ≤ Θ.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hΘfin hΘone
  have hnumeric := completion_absorption hK hD hCm hCh hΘreal
  have hcoeff : ENNReal.ofReal A *
      (ENNReal.ofReal Cp * (lowerMoment a ha t q ht hq.le)⁻¹ *
        (ENNReal.ofReal Cm * upperMoment a ha s p hs hp.le *
          ENNReal.ofReal (Real.exp (Cm * Real.sqrt Θ.toReal)) *
          nonnegativeEssInf (originCube (1 / 2)) u)) +
      ENNReal.ofReal D * (ENNReal.ofReal (Real.exp (Ch * Real.sqrt Θ.toReal)) *
        nonnegativeEssInf (originCube (1 / 2)) u) ≤
      ENNReal.ofReal (Real.exp ((K + D + Cm + Ch + 2) * Real.sqrt Θ.toReal)) *
        nonnegativeEssInf (originCube (1 / 2)) u := by
    calc
      _ = (ENNReal.ofReal K * Θ * ENNReal.ofReal (Real.exp (Cm * Real.sqrt Θ.toReal)) +
          ENNReal.ofReal D * ENNReal.ofReal (Real.exp (Ch * Real.sqrt Θ.toReal))) *
          nonnegativeEssInf (originCube (1 / 2)) u := by
        dsimp only [K, Θ, contrast]
        rw [ENNReal.ofReal_mul (mul_nonneg hA hCp), ENNReal.ofReal_mul hA, div_eq_mul_inv,
          add_mul]
        ac_rfl
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ zero_le
        rw [← ENNReal.ofReal_toReal hΘfin, ← ENNReal.ofReal_mul hK,
          ← ENNReal.ofReal_mul (mul_nonneg hK ENNReal.toReal_nonneg),
          ← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_add
            (mul_nonneg (mul_nonneg hK ENNReal.toReal_nonneg) (Real.exp_pos _).le)
            (mul_nonneg hD (Real.exp_pos _).le)]
        simpa only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg] using
          ENNReal.ofReal_le_ofReal hnumeric
  exact hmono.trans (hnormbound.trans hcoeff)

end CoarseDeGiorgi.Endpoint
