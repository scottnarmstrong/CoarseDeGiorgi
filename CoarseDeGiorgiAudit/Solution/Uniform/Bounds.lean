import Mathlib
import CoarseDeGiorgiAudit.Defs
import CoarseDeGiorgiAudit.Solution.BridgeBesov
import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
import CoarseDeGiorgi.Weighted.UpperSpecNorm

attribute [-instance] Homogenization.instMeasurableSpaceVec

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder

namespace CoarseDeGiorgiAudit.Solution.Uniform

theorem dotProduct_le_euclidean_norm_mul {d : ℕ} (x y : Vec d) :
    dotProduct x y ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ *
        ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))‖ := by
  let X : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 y
  have heq : inner ℝ X Y = dotProduct x y := by
    simp [X, Y, EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]
  rw [← heq]
  exact real_inner_le_norm X Y

theorem euclidean_norm_sq_eq_dotProduct {d : ℕ} (x : Vec d) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 = dotProduct x x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

theorem dotProduct_smul_one_mulVec {d : ℕ} (K : ℝ) (x : Vec d) :
    dotProduct x ((K • (1 : Mat d)) *ᵥ x) = K * dotProduct x x := by
  have hv : (K • (1 : Mat d)).mulVec x = K • x := by
    ext i
    change ∑ j, (K • (1 : Mat d)) i j * x j = K * x i
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Ne.symm hji]
    · simp
  rw [hv]
  change (∑ i, x i * (K * x i)) = K * ∑ i, x i * x i
  calc
    (∑ i, x i * (K * x i)) = ∑ i, K * (x i * x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = K * ∑ i, x i * x i := by rw [Finset.mul_sum]

theorem trace_le_of_quadratic {d : ℕ} (A : Mat d) (K : ℝ)
    (hK : ∀ ξ : Vec d, dotProduct ξ (A *ᵥ ξ) ≤ K * dotProduct ξ ξ) :
    A.trace ≤ (d : ℝ) * K := by
  have hdiag (i : Fin d) : A i i ≤ K := by
    have h := hK (Pi.single i (1 : ℝ))
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using h
  unfold Matrix.trace
  calc
    (∑ i, A i i) ≤ ∑ _i : Fin d, K := Finset.sum_le_sum fun i _ => hdiag i
    _ = (d : ℝ) * K := by simp

theorem norm_smul_one {d : ℕ} (K : ℝ) (hK : 0 ≤ K) :
    ‖K • (1 : Mat d)‖ ≤ K := by
  change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)
    (K • (1 : Mat d))‖ ≤ K
  have hId : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)
      (1 : Mat d)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simp
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hK]
  calc
    K * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (1 : Mat d)‖ ≤ K * 1 :=
      mul_le_mul_of_nonneg_left hId hK
    _ = K := mul_one K

theorem pointwise_uniform_bounds {d : ℕ} {lam Λ : ℝ}
    (hlam : 0 < lam) (hΛ : 0 ≤ Λ) {A : Mat d}
    (hA : A.IsHermitian)
    (hEll : ∀ ξ : Vec d,
      lam * dotProduct ξ ξ ≤ dotProduct ξ (A *ᵥ ξ) ∧
      dotProduct ξ (A *ᵥ ξ) ≤ Λ * dotProduct ξ ξ) :
    A.PosDef ∧ ‖A‖ ≤ Λ ∧ ‖A⁻¹‖ ≤ lam⁻¹ ∧
      0 ≤ A.trace ∧ A.trace ≤ (d : ℝ) * Λ ∧
      0 ≤ (A⁻¹).trace ∧ (A⁻¹).trace ≤ (d : ℝ) * lam⁻¹ := by
  have hpos : A.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
    intro ξ hξ
    have hξ' : 0 < dotProduct ξ ξ := by
      simpa using (Matrix.dotProduct_self_star_pos_iff).2 hξ
    exact lt_of_lt_of_le (mul_pos hlam hξ') (hEll ξ).1
  have hquadA : ∀ ξ : Vec d,
      dotProduct ξ (A *ᵥ ξ) ≤ dotProduct ξ ((Λ • (1 : Mat d)) *ᵥ ξ) := by
    intro ξ
    calc
      dotProduct ξ (A *ᵥ ξ) ≤ Λ * dotProduct ξ ξ := (hEll ξ).2
      _ = dotProduct ξ ((Λ • (1 : Mat d)) *ᵥ ξ) := by
        rw [dotProduct_smul_one_mulVec]
  have hnorm : ‖A‖ ≤ Λ := by
    calc
      ‖A‖ ≤ ‖Λ • (1 : Mat d)‖ :=
        CoarseDeGiorgi.Weighted.UpperResponseImpl.matrix_l2_norm_le_of_quadratic
          hpos.posSemidef hquadA
      _ ≤ Λ := norm_smul_one Λ hΛ
  have hInvPos : (A⁻¹).PosDef := hpos.inv
  have hInvQuadratic : ∀ ξ : Vec d,
      dotProduct ξ (A⁻¹ *ᵥ ξ) ≤ lam⁻¹ * dotProduct ξ ξ := by
    intro ξ
    let y : Vec d := A⁻¹ *ᵥ ξ
    have hmul : A *ᵥ y = ξ := by
      change A.mulVec (A⁻¹.mulVec ξ) = ξ
      calc
        A.mulVec (A⁻¹.mulVec ξ) = (A * A⁻¹).mulVec ξ :=
          Matrix.mulVec_mulVec ξ A A⁻¹
        _ = ξ := by
          have hdet : IsUnit A.det :=
            isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
          have hAI : A * A⁻¹ = (1 : Mat d) := Matrix.mul_nonsing_inv A hdet
          rw [hAI]
          simp
    have hlower := (hEll y).1
    rw [hmul] at hlower
    let Y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 y
    let X : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 ξ
    have hYsq : ‖Y‖ ^ 2 = dotProduct y y := euclidean_norm_sq_eq_dotProduct y
    have hXsq : ‖X‖ ^ 2 = dotProduct ξ ξ := euclidean_norm_sq_eq_dotProduct ξ
    have hCauchy : dotProduct y ξ ≤ ‖Y‖ * ‖X‖ := by
      simpa [Y, X] using dotProduct_le_euclidean_norm_mul y ξ
    have hYbound : ‖Y‖ ≤ lam⁻¹ * ‖X‖ := by
      by_cases hy : ‖Y‖ = 0
      · simpa [hy] using
          (mul_nonneg (le_of_lt (inv_pos.mpr hlam)) (norm_nonneg X))
      · have hypos : 0 < ‖Y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
        have hprod : ‖Y‖ * (lam * ‖Y‖) ≤ ‖Y‖ * ‖X‖ := by
          calc
            ‖Y‖ * (lam * ‖Y‖) = lam * ‖Y‖ ^ 2 := by ring
            _ = lam * dotProduct y y := by rw [hYsq]
            _ ≤ dotProduct y ξ := hlower
            _ ≤ ‖Y‖ * ‖X‖ := hCauchy
        have hcancel := (mul_le_mul_iff_of_pos_left hypos).mp hprod
        have hdiv : ‖Y‖ ≤ ‖X‖ / lam := (le_div_iff₀ hlam).2 (by nlinarith [hcancel])
        calc
          ‖Y‖ ≤ ‖X‖ / lam := hdiv
          _ = lam⁻¹ * ‖X‖ := by rw [div_eq_mul_inv]; ring
    have hCauchy' : dotProduct ξ y ≤ ‖X‖ * ‖Y‖ := by
      simpa [X, Y, dotProduct_comm] using dotProduct_le_euclidean_norm_mul ξ y
    calc
      dotProduct ξ (A⁻¹ *ᵥ ξ) = dotProduct ξ y := by rfl
      _ ≤ ‖X‖ * ‖Y‖ := hCauchy'
      _ ≤ ‖X‖ * (lam⁻¹ * ‖X‖) :=
        mul_le_mul_of_nonneg_left hYbound (norm_nonneg _)
      _ = lam⁻¹ * dotProduct ξ ξ := by rw [← hXsq]; ring
  have hInvQuadratic' : ∀ ξ : Vec d,
      dotProduct ξ ((A⁻¹) *ᵥ ξ) ≤
        dotProduct ξ ((lam⁻¹ • (1 : Mat d)) *ᵥ ξ) := by
    intro ξ
    calc
      dotProduct ξ ((A⁻¹) *ᵥ ξ) ≤ lam⁻¹ * dotProduct ξ ξ := hInvQuadratic ξ
      _ = dotProduct ξ ((lam⁻¹ • (1 : Mat d)) *ᵥ ξ) := by
        rw [dotProduct_smul_one_mulVec]
  have hInvNorm : ‖A⁻¹‖ ≤ lam⁻¹ := by
    calc
      ‖A⁻¹‖ ≤ ‖lam⁻¹ • (1 : Mat d)‖ :=
        CoarseDeGiorgi.Weighted.UpperResponseImpl.matrix_l2_norm_le_of_quadratic
          hInvPos.posSemidef hInvQuadratic'
      _ ≤ lam⁻¹ := by
        exact norm_smul_one _ (le_of_lt (inv_pos.mpr hlam))
  have htrace : 0 ≤ A.trace ∧ A.trace ≤ (d : ℝ) * Λ := by
    constructor
    · exact hpos.posSemidef.trace_nonneg
    · exact trace_le_of_quadratic A Λ (fun ξ => (hEll ξ).2)
  have hInvTrace : 0 ≤ (A⁻¹).trace ∧ (A⁻¹).trace ≤ (d : ℝ) * lam⁻¹ := by
    constructor
    · exact hInvPos.posSemidef.trace_nonneg
    · exact trace_le_of_quadratic (A⁻¹) lam⁻¹ hInvQuadratic
  exact ⟨hpos, hnorm, hInvNorm, htrace.1, htrace.2, hInvTrace.1, hInvTrace.2⟩

theorem trace_continuous {d : ℕ} :
    Continuous (fun A : Mat d => A.trace) := by
  fun_prop

theorem uniformly_elliptic_isWeightedCoeffOn {d : ℕ} {lam Λ : ℝ}
    (a : CoeffField d) (hlam : 0 < lam) (hΛ : lam ≤ Λ)
    (hmeas : AEStronglyMeasurable a (volume.restrict (originCube 1)))
    (hEll : ∀ᵐ x ∂(volume.restrict (originCube 1)),
      (a x).IsHermitian ∧ ∀ ξ : Vec d,
        lam * dotProduct ξ ξ ≤ dotProduct ξ ((a x).mulVec ξ) ∧
        dotProduct ξ ((a x).mulVec ξ) ≤ Λ * dotProduct ξ ξ) :
    IsWeightedCoeffOn (originCube 1) a := by
  let μ := volume.restrict (originCube (d := d) 1)
  have hmass : volume (originCube (d := d) 1) = 1 :=
    CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.originCube_volume_one d
  have hfinite : IsFiniteMeasure μ := ⟨by simp [μ, hmass]⟩
  let := hfinite
  have hΛ0 : 0 ≤ Λ := le_trans (le_of_lt hlam) hΛ
  have hpos : ∀ᵐ x ∂μ, (a x).PosDef := by
    filter_upwards [hEll] with x hx
    exact (pointwise_uniform_bounds hlam hΛ0 hx.1 hx.2).1
  have htraceMeas : AEStronglyMeasurable (fun x => (a x).trace) μ :=
    trace_continuous.comp_aestronglyMeasurable hmeas
  have hinvMeas : AEStronglyMeasurable (fun x => (a x)⁻¹) μ :=
    (CoarseDeGiorgi.Weighted.response_matrix_inverse_measurable.comp_aemeasurable
      hmeas.aemeasurable).aestronglyMeasurable
  have hinvTraceMeas : AEStronglyMeasurable (fun x => ((a x)⁻¹).trace) μ :=
    trace_continuous.comp_aestronglyMeasurable hinvMeas
  have htraceBound : ∀ᵐ x ∂μ,
      ‖(a x).trace‖ ≤ (d : ℝ) * Λ := by
    filter_upwards [hEll] with x hx
    obtain ⟨_, _, _, htr0, htr, _, _⟩ :=
      pointwise_uniform_bounds hlam hΛ0 hx.1 hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg htr0]
    exact htr
  have hinvTraceBound : ∀ᵐ x ∂μ,
      ‖((a x)⁻¹).trace‖ ≤ (d : ℝ) * lam⁻¹ := by
    filter_upwards [hEll] with x hx
    obtain ⟨_, _, _, _, _, htr0, htr⟩ :=
      pointwise_uniform_bounds hlam hΛ0 hx.1 hx.2
    rw [Real.norm_eq_abs, abs_of_nonneg htr0]
    exact htr
  have htraceInt : Integrable (fun x => (a x).trace) μ := by
    apply Integrable.mono' (integrable_const ((d : ℝ) * Λ)).norm htraceMeas
    filter_upwards [htraceBound] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hΛ0)]
      using hx
  have hinvTraceInt : Integrable (fun x => ((a x)⁻¹).trace) μ := by
    apply Integrable.mono' (integrable_const ((d : ℝ) * lam⁻¹)).norm hinvTraceMeas
    filter_upwards [hinvTraceBound] with x hx
    have hscalar : 0 ≤ (d : ℝ) * lam⁻¹ := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hscalar] using hx
  exact ⟨hmeas, hpos, htraceInt, hinvTraceInt⟩

theorem uniform_moment_bounds {d : ℕ} {lam Λ p q : ℝ}
    (a : CoeffField d) (hlam : 0 < lam) (hΛ : lam ≤ Λ)
    (hp : 0 < p) (hq : 0 < q)
    (hmeas : AEStronglyMeasurable a (volume.restrict (originCube 1)))
    (hEll : ∀ᵐ x ∂(volume.restrict (originCube 1)),
      (a x).IsHermitian ∧ ∀ ξ : Vec d,
        lam * dotProduct ξ ξ ≤ dotProduct ξ ((a x).mulVec ξ) ∧
        dotProduct ξ ((a x).mulVec ξ) ≤ Λ * dotProduct ξ ξ) :
    eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
        (volume.restrict (originCube 1)) ≤ ENNReal.ofReal Λ ∧
      eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
        (volume.restrict (originCube 1)) ≤ ENNReal.ofReal (lam⁻¹) := by
  let μ := volume.restrict (originCube (d := d) 1)
  have hmass : volume (originCube (d := d) 1) = 1 :=
    CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.originCube_volume_one d
  have hμ : μ Set.univ = 1 := by simp [μ, hmass]
  have hΛ0 : 0 ≤ Λ := le_trans (le_of_lt hlam) hΛ
  have hInv0 : 0 ≤ lam⁻¹ := le_of_lt (inv_pos.mpr hlam)
  have hnormMeas : AEStronglyMeasurable (fun x => ‖a x‖) μ :=
    continuous_norm.comp_aestronglyMeasurable hmeas
  have hinvMeas : AEStronglyMeasurable (fun x => (a x)⁻¹) μ :=
    (CoarseDeGiorgi.Weighted.response_matrix_inverse_measurable.comp_aemeasurable
      hmeas.aemeasurable).aestronglyMeasurable
  have hinvNormMeas : AEStronglyMeasurable (fun x => ‖(a x)⁻¹‖) μ :=
    continuous_norm.comp_aestronglyMeasurable hinvMeas
  have hnormBound : ∀ᵐ x ∂μ, ‖a x‖ ≤ Λ := by
    filter_upwards [hEll] with x hx
    exact (pointwise_uniform_bounds hlam hΛ0 hx.1 hx.2).2.1
  have hinvNormBound : ∀ᵐ x ∂μ, ‖(a x)⁻¹‖ ≤ lam⁻¹ := by
    filter_upwards [hEll] with x hx
    exact (pointwise_uniform_bounds hlam hΛ0 hx.1 hx.2).2.2.1
  constructor
  · calc
      eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p) μ ≤
          eLpNorm (fun _ : Vec d => Λ) (ENNReal.ofReal p) μ :=
        eLpNorm_mono_ae hnormMeas (hnormBound.mono fun x hx => by
          simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a x)),
            abs_of_nonneg hΛ0] using hx)
      _ = ENNReal.ofReal Λ := by
        rw [eLpNorm_const (Λ : ℝ) (by simp [hp]) (by simp [μ, hmass])]
        simp [hμ, Real.enorm_eq_ofReal_abs, abs_of_nonneg hΛ0,
          ENNReal.toReal_ofReal hp.le]
  · calc
      eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q) μ ≤
          eLpNorm (fun _ : Vec d => lam⁻¹) (ENNReal.ofReal q) μ :=
        eLpNorm_mono_ae hinvNormMeas (hinvNormBound.mono fun x hx => by
          simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg ((a x)⁻¹)),
            abs_of_pos hlam] using hx)
      _ = ENNReal.ofReal (lam⁻¹) := by
        rw [eLpNorm_const (lam⁻¹ : ℝ) (by simp [hq]) (by simp [μ, hmass])]
        simp [hμ, Real.enorm_eq_ofReal_abs, abs_of_nonneg hInv0,
          ENNReal.toReal_ofReal hq.le]

end CoarseDeGiorgiAudit.Solution.Uniform
