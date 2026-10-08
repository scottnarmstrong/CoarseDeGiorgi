import CoarseDeGiorgi.Endpoint.Capacitary.Moments
import CoarseDeGiorgi.Endpoint.Capacitary.FunctionalLower
import CoarseDeGiorgi.Endpoint.Capacitary.Remote
import CoarseDeGiorgi.Endpoint.Capacitary.Scalar

/-! Conditional assembly of `l.source.mass` from the two fixed interior interfaces. -/

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- `l.source.mass` with exactly the two interior estimates as conditional inputs. -/
theorem source_mass_of_interior (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (h914 :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          eLpNorm u (ENNReal.ofReal (harnackEtaParam q))
              (volume.restrict (originCube (15 / 16))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (15 / 16)) u )
    (hrem : RemoteLocalBoundedness d p q s t hp hq hs ht) :
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
                nonnegativeEssInf (originCube (1 / 2)) u := by
  have : NeZero d := ⟨by omega⟩
  have hη : 0 < harnackEtaParam q := by
    unfold harnackEtaParam paramR
    positivity
  obtain ⟨H, hH, hweak⟩ := h914
  obtain ⟨R, hR, hremote⟩ := hrem
  obtain ⟨A, hA, hcompetitor⟩ := capacitary_competitor_energy (d := d) hs hp.le
  let κ : ℝ := (capacitaryNormalization d (harnackEtaParam q)).toReal
  have hκ : 0 < κ := ENNReal.toReal_pos (capacitaryNormalization_pos hη).ne'
    (capacitaryNormalization_ne_top hη)
  let C : ℝ := A * κ⁻¹ + R + 2 * H
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a ha hU hL u G hu0 hus
  obtain ⟨μ, hμ0, hμK, hμ⟩ := source_measure_exists a ha u G hus
  let ν := μ.restrict (originCube (3 / 4))
  obtain ⟨hνfin, _, _, V, Gv, hV, heq, hV0, hVu, _, hVaway⟩ :=
    source_potential a ha u G hu0 hus μ hμ0 hμK hμ ν rfl
  have : IsFiniteMeasure ν := hνfin
  obtain ⟨ψ, Gψ, hψ, hψ01, hψQ, hψsup, hmin⟩ := remote_capacitary_exists a ha
  obtain ⟨f, Gf, hf, hfQ, hfE⟩ := hcompetitor a ha
  have hψE := (hmin f Gf hf (hfQ.mono fun x hx hxQ => (hx hxQ).ge)).trans hfE
  have hψ0 : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ ψ x :=
    Eventually.of_forall fun x => (hψ01 x).1
  let Z : ℝ := Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal
  have hψlower := capacitary_lower_bound hη hψ0 hψQ
    (hweak a ha hU hL ψ Gψ hψ0 hψsup)
  have hνW : ν (originCube (3 / 4))ᶜ = 0 := by
    dsimp only [ν]
    rw [Measure.restrict_apply (originCube_domain (by norm_num : (0 : ℝ) < 3 / 4)).isOpen.measurableSet.compl]
    simp only [compl_inter_self, measure_empty]
  have hlower := capacitary_functional_lower a ha ν hνW hV heq hψ hψ0
    (κ * Real.exp (-(H * Z))) (mul_nonneg hκ.le (Real.exp_pos _).le) hψlower
  have hRI : remoteCube d 1 ⊆ originCube (15 / 16) :=
    fun x hx => closure_remoteCube_subset_interior (subset_closure hx)
  have hRU := hRI.trans (originCube_mono' (by norm_num) one_pos (by norm_num))
  have hremoteV := hremote a ha hU hL V Gv
    (ae_mono (Measure.restrict_mono hRU le_rfl) hV0)
    (hVaway _ (remoteCube_domain one_pos) remoteCube_subset_exterior)
  have hnorm := capacitary_remote_bound a ha hV hu0 hV0 hVu (harnackEtaParam q)
    (H * Z) (R * Z) (hweak a ha hU hL u G hu0 hus) hremoteV
  let I := nonnegativeEssInf (originCube (1 / 2)) u
  have hIf : I ≠ ⊤ := capacitary_essInf_ne_top
    (originCube_domain (by norm_num : (0 : ℝ) < 1 / 2)).isOpen
    (originCube_nonempty (by norm_num : (0 : ℝ) < 1 / 2)) u
  let L : ℝ := Real.exp ((H + R) * Z) * I.toReal
  have hL0 : 0 ≤ L := mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hLnorm : eLpNorm V ⊤ (volume.restrict (remoteCube d (1 / 2))) ≤ ENNReal.ofReal L := by
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hIf]
    simpa only [← add_mul] using hnorm
  have hQsub : remoteCube d (1 / 2) ⊆ originCube 1 := by
    intro x hx
    apply hRU
    rw [remoteCube_eq_ball one_pos]
    rw [remoteCube_eq_ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx
    exact Metric.ball_subset_ball (by norm_num) hx
  have hVmem := Weighted.MemH1a0.memH1a ha hV
  have hVQ := capacitary_ae_le_of_norm_top
    (hVmem.1.mono_measure (Measure.restrict_mono hQsub le_rfl)) hL0 hLnorm
  have hVQ' : ∀ᵐ x ∂volume.restrict (originCube 1), x ∈ remoteCube d (1 / 2) → V x ≤ L :=
    ae_mono Measure.restrict_le_self
      ((ae_restrict_iff' (remoteCube_domain (by norm_num : (0 : ℝ) < 1 / 2)).isOpen.measurableSet).mp hVQ)
  have htest := (capacitary_test (originCube_domain one_pos) (originCube_nonempty one_pos)
    ha hψ hψQ hmin hV hV0 L hL0 hVQ').2
  have hswap : (∫ x in originCube 1, vecDot (Gψ x) (matVecMul (a x) (Gv x))) =
      ∫ x in originCube 1, vecDot (Gv x) (matVecMul (a x) (Gψ x)) := by
    let P := Weighted.memH1aEnergyField (originCube_domain one_pos).isOpen ha
      (Weighted.MemH1a0.memH1a ha hψ)
    let X := Weighted.memH1aEnergyField (originCube_domain one_pos).isOpen ha hVmem
    exact (Weighted.gradientHilbert_inner_coe ha P X).symm.trans
      ((real_inner_comm _ _).trans (Weighted.gradientHilbert_inner_coe ha X P))
  rw [hswap] at hlower
  have hEfin := (Weighted.MemH1a.energy_lt_top (originCube_domain one_pos).isOpen ha
    (Weighted.MemH1a0.memH1a ha hψ)).ne
  have hmass : ENNReal.ofReal (κ * Real.exp (-(H * Z))) * ν univ ≤
      ENNReal.ofReal L * (ENNReal.ofReal A * upperMoment a ha s p hs hp.le) := by
    calc
      _ ≤ ENNReal.ofReal (∫ x in originCube 1, vecDot (Gv x) (matVecMul (a x) (Gψ x))) := hlower
      _ ≤ ENNReal.ofReal (L * (weightedEnergy a (originCube 1) Gψ).toReal) :=
        ENNReal.ofReal_le_ofReal htest
      _ = ENNReal.ofReal L * weightedEnergy a (originCube 1) Gψ := by
        rw [ENNReal.ofReal_mul hL0, ENNReal.ofReal_toReal hEfin]
      _ ≤ _ := mul_le_mul_right hψE _
  refine ⟨μ, hμ0, hμK, hμ, ?_⟩
  have hfinal := capacitary_scalar_mass hκ hA hH hR (Real.sqrt_nonneg _) hIf hmass
  have hmassν : ν univ = μ (originCube (3 / 4)) := Measure.restrict_apply_univ _
  rw [hmassν] at hfinal
  exact hfinal

end CoarseDeGiorgi.Endpoint
