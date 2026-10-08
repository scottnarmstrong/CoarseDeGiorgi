import CoarseDeGiorgi.SharpnessExamples.PolynomialDefs
import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationDivergence
import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationMembership
import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationInterface
import CoarseDeGiorgi.SharpnessExamples.ScalarTest
import CoarseDeGiorgi.Sharpness.LineEquation.CutoffLimit
import CoarseDeGiorgi.Sharpness.LineEquation.AxisGeometry
import CoarseDeGiorgi.Statements.IsWeightedSolution

open Homogenization MeasureTheory Set Filter
open CoarseDeGiorgi.Sharpness
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem polynomialFlux_coordinate_integrableOn {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {q t epsilon : ℝ} (he : 0 < epsilon) :
    ∀ i : Fin d, IntegrableOn (fun x => polynomialFlux d q t epsilon x i)
      (originCube (d := d) 1) := by
  let V := originCube (d := d) 1
  have hV : IsOpenBoundedConvexDomain V :=
    Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1)
  have hfinite : volume V ≠ ⊤ := hV.isBoundedDomain.isBounded.measure_lt_top.ne
  intro i
  by_cases hi : i = 0
  · subst i
    let b : Vec d → ℝ := fun x =>
      polynomialAxialFactor d q t epsilon (Sharpness.transverseNorm x)
    have hb : Measurable b := by
      dsimp [b, polynomialAxialFactor]
      exact Measurable.ite
        (isOpen_lt Sharpness.lineRadius_continuous continuous_const).measurableSet
        measurable_const measurable_const
    let M : ℝ := max |polynomialParallel d q t epsilon| 1
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hbnd (x : Vec d) : ‖b x‖ ≤ M := by
      dsimp [b, M, polynomialAxialFactor]
      split_ifs
      · simpa only [Real.norm_eq_abs] using (le_max_left |polynomialParallel d q t epsilon| 1)
      · simpa only [Real.norm_eq_abs, abs_one] using
          (le_max_right |polynomialParallel d q t epsilon| 1)
    have hrepr : (fun x : Vec d => polynomialFlux d q t epsilon x 0) =
        fun x => 2 * x 0 * b x := by
      funext x
      simp [polynomialFlux, polynomialAxialFactor, b]
    have hmeas : Measurable (fun x : Vec d => polynomialFlux d q t epsilon x 0) := by
      rw [hrepr]
      have htmp : Measurable (fun x : Vec d => 2 * (x 0 * b x)) :=
        measurable_const.mul ((continuous_apply (0 : Fin d)).measurable.mul hb)
      convert htmp using 1
      funext x
      ring
    have hbound : ∀ᵐ x ∂(volume.restrict V),
        ‖polynomialFlux d q t epsilon x 0‖ ≤ M := by
      filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
      rw [congrFun hrepr x, Real.norm_eq_abs, abs_mul]
      have hcoord : |2 * x 0| ≤ 1 := by
        have h' := hx 0
        rw [abs_le]
        constructor <;> nlinarith [h'.1, h'.2]
      calc
        |2 * x 0| * |b x| ≤ 1 * M :=
          mul_le_mul hcoord (by simpa only [Real.norm_eq_abs] using hbnd x)
            (abs_nonneg _) (by norm_num)
        _ = M := by ring
    exact IntegrableOn.of_bound hfinite.lt_top hmeas.aestronglyMeasurable M hbound
  · obtain ⟨K, hK⟩ := polynomialFlux_transverse_lipschitzOn hd he hi
    obtain ⟨M, hM, hMb⟩ := lipschitzOn_real_bounded
      hV.isBoundedDomain.isBounded hK
    apply IntegrableOn.of_bound hfinite.lt_top
      (hK.continuousOn.aestronglyMeasurable hV.isOpen.measurableSet) M
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
    rw [Real.norm_eq_abs]
    exact hMb x hx

private theorem polynomialFlux_axial_pairing {d : ℕ} [NeZero d]
    {q t epsilon : ℝ} (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    Integrable (fun x => smoothGrad φ x 0 * polynomialFlux d q t epsilon x 0) volume ∧
    (∫ x, smoothGrad φ x 0 * polynomialFlux d q t epsilon x 0) =
      -2 * ∫ x, polynomialAxialFactor d q t epsilon
        (Sharpness.transverseNorm x) * φ x := by
  let b : Vec d → ℝ := fun x =>
    polynomialAxialFactor d q t epsilon (Sharpness.transverseNorm x)
  let M := max |polynomialParallel d q t epsilon| 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb : Measurable b := by
    dsimp [b, polynomialAxialFactor]
    exact Measurable.ite
      (isOpen_lt Sharpness.lineRadius_continuous continuous_const).measurableSet
      measurable_const measurable_const
  have hbnd (x : Vec d) : ‖b x‖ ≤ M := by
    dsimp [b, M, polynomialAxialFactor]
    split_ifs
    · simpa only [Real.norm_eq_abs] using
        (le_max_left |polynomialParallel d q t epsilon| 1)
    · simpa only [Real.norm_eq_abs, abs_one] using
        (le_max_right |polynomialParallel d q t epsilon| 1)
  have hinv (x : Vec d) (s : ℝ) :
      b (x + s • basisVec (0 : Fin d)) = b x := by
    simp [b, transverseNorm_add_axial]
  let ψ : Vec d → ℝ := fun x => x 0 * φ x
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    dsimp [ψ]
    fun_prop
  have hcψ : HasCompactSupport ψ := by
    exact hc.mul_left
  have hcoordinate (x : Vec d) :
      (fderiv ℝ (fun y : Vec d => y 0) x) (basisVec (0 : Fin d)) = 1 := by
    rw [show fderiv ℝ (fun y : Vec d => y 0) x =
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) 0 by
      exact ContinuousLinearMap.fderiv (𝕜 := ℝ)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) 0)]
    simp [basisVec]
  have hψgrad (x : Vec d) :
      smoothGrad ψ x 0 = φ x + x 0 * smoothGrad φ x 0 := by
    rw [show ψ = fun y : Vec d => y 0 * φ y by rfl]
    rw [smoothGrad_mul (by fun_prop) ((hφ.differentiable (by simp)).differentiableAt)]
    change x 0 * smoothGrad φ x 0 + φ x *
      (fderiv ℝ (fun y : Vec d => y 0) x) (basisVec 0) = _
    rw [hcoordinate]
    ring
  have hφInt : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hc
  have hbφInt : Integrable (fun x => b x * φ x) volume := by
    have h := hφInt.bdd_mul hb.aestronglyMeasurable (ae_of_all _ hbnd)
    exact h.congr (by filter_upwards [] with x; ring)
  have hψgradInt : Integrable (fun x => smoothGrad ψ x 0) volume := by
    have hcont : Continuous (fun x => smoothGrad ψ x 0) :=
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact hcont.integrable_of_hasCompactSupport
      (hcψ.fderiv_apply (𝕜 := ℝ) (basisVec 0))
  have hψpairInt := hψgradInt.bdd_mul hb.aestronglyMeasurable (ae_of_all _ hbnd)
  have hψpairInt' : Integrable (fun x => b x * smoothGrad ψ x 0) volume :=
    hψpairInt.congr (by filter_upwards [] with x; ring)
  have hcoordInt : Integrable
      (fun x => b x * (x 0 * smoothGrad φ x 0)) volume := by
    apply (hψpairInt'.sub hbφInt).congr
    filter_upwards [] with x
    change b x * smoothGrad ψ x 0 - b x * φ x = _
    rw [hψgrad x]
    ring
  have haxInt : Integrable
      (fun x => smoothGrad φ x 0 * polynomialFlux d q t epsilon x 0) volume := by
    have h := hcoordInt.const_mul 2
    apply h.congr
    filter_upwards [] with x
    simp [polynomialFlux, b, smoothGrad]
    ring
  have htest := integral_axial_test_eq_zero hb hbnd hinv hψ hcψ
  have hsplit :
      (∫ x, b x * smoothGrad ψ x 0) =
        (∫ x, b x * φ x) + (∫ x, b x * (x 0 * smoothGrad φ x 0)) := by
    calc
      _ = ∫ x, (b x * φ x + b x * (x 0 * smoothGrad φ x 0)) :=
        integral_congr_ae (Filter.Eventually.of_forall
          (fun x => by rw [hψgrad x]; ring))
      _ = (∫ x, b x * φ x) + (∫ x, b x * (x 0 * smoothGrad φ x 0)) :=
        integral_add hbφInt hcoordInt
  rw [hsplit] at htest
  have haxpoint :
      (fun x => smoothGrad φ x 0 * polynomialFlux d q t epsilon x 0) =
        fun x => 2 * (b x * (x 0 * smoothGrad φ x 0)) := by
    funext x
    simp [polynomialFlux, b, smoothGrad]
    ring
  refine ⟨haxInt, ?_⟩
  calc
    (∫ x, smoothGrad φ x 0 * polynomialFlux d q t epsilon x 0) =
        ∫ x, 2 * (polynomialAxialFactor d q t epsilon
          (Sharpness.transverseNorm x) * (x 0 * smoothGrad φ x 0)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => congrFun haxpoint x))
    _ = -2 * ∫ x, polynomialAxialFactor d q t epsilon
        (Sharpness.transverseNorm x) * φ x := by
      rw [integral_const_mul]
      dsimp [b] at htest
      linear_combination 2 * htest

private theorem polynomialFlux_global_pairing_eq_zero {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {q t epsilon : ℝ} (he : 0 < epsilon)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ originCube (d := d) 1) :
    ∫ x, vecDot (smoothGrad φ x) (polynomialFlux d q t epsilon x) = 0 := by
  let V := originCube (d := d) 1
  let F : Vec d → Vec d := polynomialFlux d q t epsilon
  let b : Vec d → ℝ := fun x =>
    polynomialAxialFactor d q t epsilon (Sharpness.transverseNorm x)
  have hV : IsOpenBoundedConvexDomain V :=
    Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1)
  have hb : Measurable b := by
    dsimp [b, polynomialAxialFactor]
    exact Measurable.ite
      (isOpen_lt Sharpness.lineRadius_continuous continuous_const).measurableSet
      measurable_const measurable_const
  let M := max |polynomialParallel d q t epsilon| 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbnd (x : Vec d) : ‖b x‖ ≤ M := by
    dsimp [b, M, polynomialAxialFactor]
    split_ifs
    · simpa only [Real.norm_eq_abs] using (le_max_left |polynomialParallel d q t epsilon| 1)
    · simpa only [Real.norm_eq_abs, abs_one] using
        (le_max_right |polynomialParallel d q t epsilon| 1)
  have hinv (x : Vec d) (s : ℝ) :
      b (x + s • basisVec (0 : Fin d)) = b x := by
    simp [b, transverseNorm_add_axial]
  let ax : Vec d → ℝ := fun x => smoothGrad φ x 0 * F x 0
  let leftT : Fin d → Vec d → ℝ := fun i x =>
    if i = 0 then 0 else fderiv ℝ φ x (basisVec i) * F x i
  let rightT : Fin d → Vec d → ℝ := fun i x =>
    if i = 0 then 0 else φ x * lineDeriv ℝ (fun y => F y i) x (basisVec i)
  have hparts (i : Fin d) :
      Integrable (leftT i) volume ∧ Integrable (rightT i) volume ∧
      (∫ x, leftT i x) = -(∫ x, rightT i x) := by
    by_cases hi : i = 0
    · subst i
      simp [leftT, rightT]
    · obtain ⟨K, hK⟩ := polynomialFlux_transverse_lipschitzOn hd he hi
      simpa [leftT, rightT, hi] using
        (integral_test_mul_lipschitzOn_flux hV.isOpen hφ hc hs hK (basisVec i))
  have hleftInt : ∀ i, Integrable (leftT i) volume := by
    intro i
    by_cases hi : i = 0
    · simp [leftT, hi]
    · exact (hparts i).1
  have hrightInt : ∀ i, Integrable (rightT i) volume := by
    intro i
    by_cases hi : i = 0
    · simp [rightT, hi]
    · exact (hparts i).2.1
  let transDiv : Vec d → ℝ := fun x =>
    ∑ i : Fin d, if i = 0 then 0 else lineDeriv ℝ (fun y => F y i) x (basisVec i)
  have htransDiv : ∀ᵐ x ∂volume, transDiv x = -2 * b x := by
    have haxis := Sharpness.lineRadius_pos_ae (by omega : 2 ≤ d)
    have hinterface : ∀ᵐ x : Vec d ∂volume,
        Sharpness.transverseNorm x ≠ 2 * epsilon := by
      exact (ae_iff).2 (by
        simpa using polynomialInterface_volume_zero (d := d) hd he)
    filter_upwards [haxis, hinterface] with x hr hne
    have hbranch : Sharpness.transverseNorm x < 2 * epsilon ∨
        2 * epsilon < Sharpness.transverseNorm x := lt_or_gt_of_ne hne
    have htotal := polynomialFlux_divergence_zero (d := d) hd (q := q) (t := t)
      (epsilon := epsilon) he hr hbranch
    have hzeroAxis := polynomialFlux_coordinate_lineDeriv (d := d) hd (q := q) (t := t)
      (epsilon := epsilon) he hr hbranch 0
    have hsplit :
        (∑ i : Fin d, lineDeriv ℝ (fun y => F y i) x (basisVec i)) =
          2 * b x + transDiv x := by
      classical
      calc
        _ = ∑ i : Fin d,
            ((if i = 0 then lineDeriv ℝ (fun y => F y i) x (basisVec i) else 0) +
              (if i = 0 then 0 else lineDeriv ℝ (fun y => F y i) x (basisVec i))) := by
                apply Finset.sum_congr rfl
                intro i hi
                by_cases h : i = 0 <;> simp [h]
        _ = (∑ i : Fin d, if i = 0 then
              lineDeriv ℝ (fun y => F y i) x (basisVec i) else 0) + transDiv x := by
                simp [transDiv, Finset.sum_add_distrib]
        _ = 2 * b x + transDiv x := by
              simp [hzeroAxis, F, b]
    rw [hsplit] at htotal
    linarith
  have hleftSumInt : Integrable (fun x => ∑ i : Fin d, leftT i x) volume := by
    apply integrable_finsetSum
    intro i hi
    exact hleftInt i
  have hrightSumInt : Integrable (fun x => ∑ i : Fin d, rightT i x) volume := by
    apply integrable_finsetSum
    intro i hi
    exact hrightInt i
  have htransPair :
      (∫ x, ∑ i : Fin d, leftT i x) = -(∫ x, ∑ i : Fin d, rightT i x) := by
    rw [integral_finsetSum Finset.univ (fun i hi => hleftInt i),
      integral_finsetSum Finset.univ (fun i hi => hrightInt i)]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiz : i = 0
    · simp [leftT, rightT, hiz]
    · exact (hparts i).2.2
  have hφbInt : Integrable (fun x => b x * φ x) volume := by
    have hφInt : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hc
    exact hφInt.bdd_mul hb.aestronglyMeasurable (ae_of_all _ hbnd) |>.congr
      (by filter_upwards [] with x; ring)
  have hrightSumVal :
      (∫ x, ∑ i : Fin d, rightT i x) = -2 * (∫ x, b x * φ x) := by
    have hpoint (x : Vec d) :
        (∑ i : Fin d, rightT i x) = φ x * transDiv x := by
      simp [rightT, transDiv, Finset.mul_sum]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    have hmul : ∀ᵐ x : Vec d ∂volume,
        φ x * transDiv x = -2 * (b x * φ x) := by
      filter_upwards [htransDiv] with x hx
      rw [hx]
      ring
    rw [integral_congr_ae hmul]
    rw [integral_const_mul]
  have haxData := polynomialFlux_axial_pairing (d := d) (q := q) (t := t)
    (epsilon := epsilon) φ hφ hc
  have haxInt : Integrable ax volume := by
    simpa [ax, F] using haxData.1
  have haxEq : ∫ x, ax x = -2 * ∫ x, b x * φ x := by
    simpa [ax, F, b] using haxData.2
  have hdecomp (x : Vec d) :
      vecDot (smoothGrad φ x) (F x) = ax x + ∑ i : Fin d, leftT i x := by
    classical
    unfold vecDot
    rw [show (∑ i : Fin d, smoothGrad φ x i * F x i) =
        ∑ i : Fin d,
          ((if i = 0 then smoothGrad φ x i * F x i else 0) +
            (if i = 0 then 0 else smoothGrad φ x i * F x i)) by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : i = 0 <;> simp [h]]
    rw [Finset.sum_add_distrib]
    simp [ax, leftT, F, CoarseDeGiorgi.smoothGrad, Finset.sum_ite_eq']
  have hglobalInt : Integrable (fun x => vecDot (smoothGrad φ x) (F x)) volume := by
    apply (haxInt.add hleftSumInt).congr
    filter_upwards [] with x
    exact (hdecomp x).symm
  calc
    ∫ x, vecDot (smoothGrad φ x) (F x) =
        ∫ x, ax x + ∑ i : Fin d, leftT i x := by
          exact integral_congr_ae (Filter.Eventually.of_forall hdecomp)
    _ = (∫ x, ax x) + ∫ x, ∑ i : Fin d, leftT i x := integral_add haxInt hleftSumInt
    _ = 0 := by rw [haxEq, htransPair, hrightSumVal]; ring

/-- The explicit polynomial profile is a weak solution across its radial
interface. The transverse flux factor matches at radius `2 * epsilon`; the
axial flux is constant along axial lines, and the regional divergences cancel. -/
theorem polynomialSolution_isWeightedSolution {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {q t epsilon : ℝ} (he : 0 < epsilon) (he8 : epsilon < 1 / 8) :
    IsWeightedSolution (polynomialCoefficientFamily d q t epsilon)
      (originCube (d := d) 1) (polynomialSolution d q t epsilon)
      (polynomialGradient d q t epsilon) := by
  let V := originCube (d := d) 1
  let a := polynomialCoefficientFamily d q t epsilon
  let F : Vec d → Vec d := polynomialFlux d q t epsilon
  have hmem := polynomialSolution_memH1a (d := d) hd (q := q) (t := t)
    (epsilon := epsilon) he he8
  have hV : IsOpenBoundedConvexDomain V :=
    Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1)
  have hFint := polynomialFlux_coordinate_integrableOn (d := d) hd (q := q)
    (t := t) (epsilon := epsilon) he
  refine ⟨hmem, ?_⟩
  intro φ hφ hc hs
  have hφ1 : ContDiff ℝ (1 : WithTop ℕ∞) φ := hφ.of_le (by simp)
  have hsourceInt := integrable_smoothGrad_dot φ F hφ1 hc hFint
  have ha : a = cylinderCoefficient epsilon
      (polynomialParallel d q t epsilon) (polynomialPerpendicular d q t epsilon) := by
    dsimp [a, polynomialCoefficientFamily]
    rw [ite_eq_left ⟨he, he8⟩]
  have hidentify :
      (fun x => vecDot (smoothGrad φ x) (matVecMul (a x)
        (polynomialGradient d q t epsilon x))) =ᵐ[volume.restrict V]
        (fun x => vecDot (smoothGrad φ x) (F x)) := by
    have haxis := ae_restrict_of_ae (s := V)
      (Sharpness.lineRadius_pos_ae (by omega : 2 ≤ d))
    have hinterface : ∀ᵐ x : Vec d ∂volume,
        Sharpness.transverseNorm x ≠ 2 * epsilon := by
      apply (ae_iff).2
      simpa using polynomialInterface_volume_zero hd he
    filter_upwards [haxis, ae_restrict_of_ae (s := V) hinterface] with x hr hne
    have hbranch : Sharpness.transverseNorm x < 2 * epsilon ∨
        2 * epsilon < Sharpness.transverseNorm x := lt_or_gt_of_ne hne
    have hpoint (i : Fin d) :
        matVecMul (a x) (polynomialGradient d q t epsilon x) i = F x i := by
      rw [ha]
      rcases hbranch with hinner | houter
      · exact polynomialCoefficient_mul_gradient_inside q t epsilon he hr hinner i
      · exact polynomialCoefficient_mul_gradient_outside q t epsilon he hr houter i
    have hv : matVecMul (a x) (polynomialGradient d q t epsilon x) = F x :=
      funext hpoint
    rw [hv]
  refine ⟨hsourceInt.congr hidentify.symm, ?_⟩
  rw [integral_congr_ae hidentify]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact polynomialFlux_global_pairing_eq_zero hd he φ hφ hc hs
  · intro x hx
    have hgrad : smoothGrad φ x = 0 := by
      funext i
      exact image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ φ y (basisVec i))
        (fun hm => hx (hs (tsupport_fderiv_apply_subset (𝕜 := ℝ)
          (f := φ) (basisVec i) hm)))
    rw [hgrad]
    simp [vecDot]

end

end CoarseDeGiorgi.SharpnessExamples
