import CoarseDeGiorgi.Harnack.Powers.SourceIntegrability
import CoarseDeGiorgi.Weighted.Testing

namespace CoarseDeGiorgi.Harnack.Powers

open Homogenization MeasureTheory
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Testing the supersolution against the admissible product `U^(m-1) * φ` gives
the sign-safe signed-power inequality. The product pair is supplied explicitly
so this lemma can be used independently of the bounded-product producer.
-/
theorem signedPower_signed_test_of_admissible_product
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a V u G)
    (hsup : IsWeightedSubsolution a V (-u) (-G))
    (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x)
    (ε m : ℝ) (hε : 0 < ε) (hm : m < 1 / 2) (_hm0 : m ≠ 0)
    {φ : Vec d → ℝ} {H : Vec d → Vec d}
    (hφ : MemH1a a V φ H)
    (hφnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ φ x)
    (hφbound : ∃ B : ℝ, ∀ᵐ x ∂volume.restrict V, |φ x| ≤ B)
    {Gψ : Vec d → Vec d}
    (hψ : MemH1a0 a V (fun x => (u x + ε) ^ (m - 1) * φ x) Gψ)
    (hψgrad : Gψ =ᵐ[volume.restrict V]
      (fun x => (u x + ε) ^ (m - 1) • H x +
        φ x • (((m - 1) * (u x + ε) ^ (m - 2)) • G x))) :
    m * (∫ x in V, vecDot (H x)
        (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) ≥
      (1 - m) * (∫ x in V,
        (φ x / ((u x + ε) ^ m)) *
          vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
            (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) := by
  let μ := volume.restrict V
  have hchain := signedPower_chain hV hne ha hu hnonneg ε m hε hm
  have hFbound : ∀ᵐ x ∂μ, |(u x + ε) ^ (m - 1)| ≤ ε ^ (m - 1) := by
    filter_upwards [hnonneg, hchain.2.2] with x hxU hbound
    have hU : 0 < u x + ε := by linarith
    rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hU) _)]
    exact hbound
  have hFmeas : AEStronglyMeasurable (fun x => (u x + ε) ^ (m - 1)) μ :=
    hchain.2.1.1
  obtain ⟨B, hB⟩ := hφbound
  let B' : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hB' : ∀ᵐ x ∂μ, |φ x| ≤ B' := hB.mono fun x hx =>
    hx.trans (le_max_left _ _)
  have hEG := Weighted.MemH1a.energy_lt_top hV.isOpen ha hu
  have hEH := Weighted.MemH1a.energy_lt_top hV.isOpen ha hφ
  have hpairing := Weighted.pairing_integrable_and_bound ha hφ.2.1 hu.2.1 hEH hEG
  have htermA : IntegrableOn
      (fun x => (u x + ε) ^ (m - 1) *
        vecDot (H x) (matVecMul (a x) (G x))) V :=
    hpairing.1.bdd_mul hFmeas hFbound
  have hquad : IntegrableOn
      (fun x => vecDot (G x) (matVecMul (a x) (G x))) V :=
    Weighted.quadratic_integrable ha hu.2.1 hEG
  have hUmeas : AEStronglyMeasurable (fun x => u x + ε) μ :=
    (continuous_id.add continuous_const).comp_aestronglyMeasurable hu.1
  have hPowMeas : AEStronglyMeasurable (fun x => (u x + ε) ^ (m - 2)) μ :=
    hUmeas.aemeasurable.pow_const (m - 2) |>.aestronglyMeasurable
  have hPowBound : ∀ᵐ x ∂μ, |(u x + ε) ^ (m - 2)| ≤ ε ^ (m - 2) := by
    filter_upwards [hnonneg] with x hx
    have hU : ε ≤ u x + ε := by linarith
    have hUpos : 0 < u x + ε := lt_of_lt_of_le hε hU
    have hexp : m - 2 ≤ 0 := by linarith
    rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hUpos) _)]
    exact Real.rpow_le_rpow_of_nonpos hε hU hexp
  have hpowQuad := hquad.bdd_mul hPowMeas hPowBound
  have hphiMeas : AEStronglyMeasurable φ μ := hφ.1
  have hJ : IntegrableOn
      (fun x => φ x * ((u x + ε) ^ (m - 2) *
        vecDot (G x) (matVecMul (a x) (G x)))) V :=
    hpowQuad.bdd_mul hphiMeas (hB'.mono fun x hx => by
      simpa only [Real.norm_eq_abs] using hx)
  have htermB : IntegrableOn
      (fun x => (m - 1) * φ x * (u x + ε) ^ (m - 2) *
        vecDot (G x) (matVecMul (a x) (G x))) V := by
    change Integrable
      (fun x => (m - 1) * φ x * (u x + ε) ^ (m - 2) *
        vecDot (G x) (matVecMul (a x) (G x))) μ
    change Integrable (fun x => φ x * ((u x + ε) ^ (m - 2) *
      vecDot (G x) (matVecMul (a x) (G x)))) μ at hJ
    convert hJ.const_mul (m - 1) using 1
    funext x
    ring
  have hψnonneg : ∀ᵐ x ∂μ, 0 ≤ (u x + ε) ^ (m - 1) * φ x := by
    filter_upwards [hnonneg, hφnonneg] with x hxU hxφ
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) hxφ
  have htest := Weighted.IsWeightedSubsolution.testing hV hne ha hsup hψ hψnonneg
  let P : Vec d → ℝ := fun x => vecDot (Gψ x) (matVecMul (a x) (G x))
  let A : Vec d → ℝ := fun x => (u x + ε) ^ (m - 1) *
      vecDot (H x) (matVecMul (a x) (G x))
  let Jfun : Vec d → ℝ := fun x => φ x *
      ((u x + ε) ^ (m - 2) * vecDot (G x) (matVecMul (a x) (G x)))
  let T : Vec d → ℝ := fun x => (m - 1) * φ x * (u x + ε) ^ (m - 2) *
      vecDot (G x) (matVecMul (a x) (G x))
  have hPdecomp : P =ᵐ[μ] fun x => A x + T x := by
    filter_upwards [hψgrad] with x hx
    dsimp [P, A, T]
    rw [hx]
    simp only [vecDot_add_left, vecDot_smul_left]
    ring
  have hPI : IntegrableOn P V := by
    exact (htermA.add htermB).congr hPdecomp.symm
  have htestNeg : (∫ x in V, -P x) ≤ 0 := by
    convert htest.2 using 1
    congr 1
    funext x
    simp [P, matVecMul_neg, vecDot_neg_right]
  have hPnonneg : 0 ≤ ∫ x in V, P x := by
    have hle : -(∫ x in V, P x) ≤ 0 := by simpa [integral_neg] using htestNeg
    linarith
  have hPint : (∫ x in V, P x) =
      (∫ x in V, A x) + (∫ x in V, T x) := by
    calc
      (∫ x in V, P x) = ∫ x in V, A x + T x := integral_congr_ae hPdecomp
      _ = (∫ x in V, A x) + (∫ x in V, T x) := integral_add htermA htermB
  have hJterm : (∫ x in V, T x) = (m - 1) * (∫ x in V, Jfun x) := by
    dsimp [T, Jfun]
    rw [show (fun x => (m - 1) * φ x * (u x + ε) ^ (m - 2) *
        vecDot (G x) (matVecMul (a x) (G x))) =
        (fun x => (m - 1) * (φ x * ((u x + ε) ^ (m - 2) *
          vecDot (G x) (matVecMul (a x) (G x))))) by
          funext x; ring]
    exact integral_const_mul _ _
  have hcore : (1 - m) * (∫ x in V, Jfun x) ≤ ∫ x in V, A x := by
    rw [hPint, hJterm] at hPnonneg
    linarith
  have hcore2 : m ^ 2 * ((1 - m) * (∫ x in V, Jfun x)) ≤
      m ^ 2 * (∫ x in V, A x) :=
    mul_le_mul_of_nonneg_left hcore (sq_nonneg m)
  have hLHS : m * (∫ x in V, vecDot (H x)
      (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) =
      m ^ 2 * (∫ x in V, A x) := by
    rw [← integral_const_mul]
    rw [integral_congr_ae]
    · rw [integral_const_mul]
    · filter_upwards with x
      simp only [A, matVecMul_smul, vecDot_smul_right]
      ring
  have hUpositive : ∀ᵐ x ∂μ, 0 < u x + ε := by
    filter_upwards [hnonneg] with x hx
    linarith
  have hratio : (fun x => ((u x + ε) ^ (m - 1)) ^ 2 /
      (u x + ε) ^ m) =ᵐ[μ] (fun x => (u x + ε) ^ (m - 2)) := by
    filter_upwards [hUpositive] with x hx
    have hpow : ((u x + ε) ^ (m - 1)) ^ 2 = (u x + ε) ^ (m - 2 + m) := by
      rw [← Real.rpow_natCast ((u x + ε) ^ (m - 1)) 2,
        ← Real.rpow_mul (le_of_lt hx)]
      congr 1
      ring
    rw [hpow, Real.rpow_add hx]
    have hden : (u x + ε) ^ m ≠ 0 := (Real.rpow_pos_of_pos hx m).ne'
    field_simp [hden]
  have hRHSae : (fun x => (φ x / ((u x + ε) ^ m)) *
      vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
        (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) =ᵐ[μ]
      (fun x => m ^ 2 * Jfun x) := by
    filter_upwards [hratio] with x hx
    dsimp [Jfun]
    simp only [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    calc
      φ x / ((u x + ε) ^ m) * ((m * (u x + ε) ^ (m - 1)) *
          ((m * (u x + ε) ^ (m - 1)) * vecDot (G x) (matVecMul (a x) (G x)))) =
          m ^ 2 * φ x * (((u x + ε) ^ (m - 1)) ^ 2 / (u x + ε) ^ m) *
            vecDot (G x) (matVecMul (a x) (G x)) := by ring
      _ = m ^ 2 * (φ x * ((u x + ε) ^ (m - 2) *
            vecDot (G x) (matVecMul (a x) (G x)))) := by rw [hx]; ring
  calc
    m * (∫ x in V, vecDot (H x)
        (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) =
        m ^ 2 * (∫ x in V, A x) := hLHS
    _ ≥ m ^ 2 * ((1 - m) * (∫ x in V, Jfun x)) := hcore2
    _ = (1 - m) * (∫ x in V,
        (φ x / ((u x + ε) ^ m)) *
          vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
            (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) := by
      rw [integral_congr_ae hRHSae, integral_const_mul]
      ring

end CoarseDeGiorgi.Harnack.Powers
