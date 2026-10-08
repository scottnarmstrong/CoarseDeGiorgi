module

public import CoarseDeGiorgi.Foundations.PoincareW11Mean
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public section

namespace CoarseDeGiorgi.Foundations

open Homogenization MeasureTheory
open scoped ENNReal

private theorem length_le_coord_sum {d : ℕ} (G : Vec d) :
    Real.sqrt (vecDot G G) ≤ ∑ i : Fin d, |G i| := by
  have hs : vecDot G G ≤ (∑ i : Fin d, |G i|) ^ 2 := by
    calc
      vecDot G G = ∑ i : Fin d, |G i| ^ 2 := by simp [vecDot, pow_two]
      _ ≤ (∑ i : Fin d, |G i|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
          (f := fun i => |G i|) (fun i _ => abs_nonneg (G i))
  calc
    Real.sqrt (vecDot G G) ≤ Real.sqrt ((∑ i : Fin d, |G i|) ^ 2) :=
      Real.sqrt_le_sqrt hs
    _ = abs (∑ i : Fin d, |G i|) := Real.sqrt_sq_eq_abs _
    _ = ∑ i : Fin d, |G i| := abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)

private theorem coord_sum_le_dim_length {d : ℕ} (G : Vec d) :
    (∑ i : Fin d, |G i|) ≤ (d : ℝ) * Real.sqrt (vecDot G G) := by
  have hi (i : Fin d) : |G i| ≤ Real.sqrt (vecDot G G) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (sq_apply_le_vecNormSq G i)
  calc
    (∑ i : Fin d, |G i|) ≤ ∑ i : Fin d, Real.sqrt (vecDot G G) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = (d : ℝ) * Real.sqrt (vecDot G G) := by simp

private theorem length_integrable {d : ℕ} {μ : Measure (Vec d)}
    {G : Vec d → Vec d} (hG : ∀ i, Integrable (fun x => G x i) μ) :
    Integrable (fun x => Real.sqrt (vecDot (G x) (G x))) μ := by
  have hs : Integrable (fun x => ∑ i : Fin d, |G x i|) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hG i).norm)
  have hvec : AEStronglyMeasurable G μ := (Integrable.of_eval hG).aestronglyMeasurable
  have hc : Continuous (fun v : Vec d => Real.sqrt (vecDot v v)) := by
    unfold vecDot
    fun_prop
  refine hs.mono' (hc.comp_aestronglyMeasurable hvec) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact length_le_coord_sum (G x)

private theorem tendsto_abs_integral_of_l1
    {d : ℕ} {μ : Measure (Vec d)} {F : ℕ → Vec d → ℝ} {f : Vec d → ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hf : Integrable f μ)
    (h : Filter.Tendsto (fun n => eLpNorm (fun x => F n x - f x) 1 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, |F n x| ∂μ)
      Filter.atTop (nhds (∫ x, |f x| ∂μ)) := by
  have hnorm : Filter.Tendsto
      (fun n => eLpNorm (fun x => |F n x| - |f x|) 1 μ)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => bot_le)
    intro n
    apply eLpNorm_mono_ae ((hF n).norm.sub hf.norm).aestronglyMeasurable
    filter_upwards with x
    simpa [Real.norm_eq_abs] using abs_abs_sub_abs_le_abs_sub (F n x) (f x)
  exact MeasureTheory.tendsto_integral_of_L1' (fun x => |f x|)
    (Filter.Eventually.of_forall fun n => (hF n).norm) hnorm

private theorem compact_integral_eq_neg_deriv_coord
    {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : HasCompactSupport f) (i : Fin d) :
    (∫ x, f x ∂volume) = -∫ x, (fderiv ℝ f x) (basisVec i) * x i ∂volume := by
  let c : Vec d → ℝ := fun x => x i
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hc : Differentiable ℝ c := by dsimp [c]; fun_prop
  have hdc : ∀ x, (fderiv ℝ c x) (basisVec i) = 1 := by
    intro x
    rw [show fderiv ℝ c x = ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin d => ℝ) i from ContinuousLinearMap.fderiv (𝕜 := ℝ)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)]
    simp [basisVec]
  have hderiv : Continuous (fun x => (fderiv ℝ f x) (basisVec i)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport (fun x => (fderiv ℝ f x) (basisVec i)) :=
    hs.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have h1 : Integrable (fun x => (fderiv ℝ f x) (basisVec i) * c x) volume :=
    (hderiv.mul hc.continuous).integrable_of_hasCompactSupport hds.mul_right
  have h2 : Integrable (fun x => f x * (fderiv ℝ c x) (basisVec i)) volume := by
    simpa only [hdc, mul_one] using hf.continuous.integrable_of_hasCompactSupport hs
  have h3 : Integrable (fun x => f x * c x) volume :=
    (hf.continuous.mul hc.continuous).integrable_of_hasCompactSupport hs.mul_right
  simpa only [c, hdc, mul_one] using
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := f) (g := c) (v := basisVec i)
      h1 h2 h3 (fun x _ => hd x) (fun x _ => hc x)

private theorem compact_abs_integral_le_coord_variation
    {d : ℕ} [NeZero d] {V : Set (Vec d)} (hV : IsOpen V)
    (hb : IsBoundedDomain V) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f)
    (hsub : tsupport f ⊆ V) :
    |∫ x, f x ∂volume| ≤ Classical.choose hb *
      ∫ x in V, ∑ i : Fin d, |(fderiv ℝ f x) (basisVec i)| ∂volume := by
  classical
  let i : Fin d := 0
  let D : Vec d → Vec d := fun x j => (fderiv ℝ f x) (basisVec j)
  have hDint (j : Fin d) : Integrable (fun x => D x j) volume :=
    ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hprod : Integrable (fun x => D x i * x i) volume :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      (by fun_prop)).integrable_of_hasCompactSupport
        (hs.fderiv_apply (𝕜 := ℝ) (basisVec i)).mul_right
  have hzero : ∀ x, x ∉ V → D x i * x i = 0 := by
    intro x hx
    have ht : x ∉ tsupport f := fun ht => hx (hsub ht)
    have hd : fderiv ℝ f x = 0 := by
      by_contra hd
      exact ht (support_fderiv_subset (𝕜 := ℝ) (f := f) hd)
    simp [D, hd]
  have hsumInt : IntegrableOn (fun x => ∑ j : Fin d, |D x j|) V :=
    integrable_finsetSum Finset.univ (fun j _ => (hDint j).norm.restrict)
  have hR : 0 ≤ Classical.choose hb := (Classical.choose_spec hb).1.le
  calc
    |∫ x, f x ∂volume| = |∫ x, D x i * x i ∂volume| := by
      rw [compact_integral_eq_neg_deriv_coord hf hs i, abs_neg]
    _ = |∫ x in V, D x i * x i ∂volume| := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    _ ≤ ∫ x in V, |D x i * x i| ∂volume := abs_integral_le_integral_abs
    _ ≤ ∫ x in V, Classical.choose hb * (∑ j : Fin d, |D x j|) ∂volume := by
      apply integral_mono_ae hprod.norm.restrict (hsumInt.const_mul _)
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      have hcoord := (Classical.choose_spec hb).2 x hx i
      have hsum : |D x i| ≤ ∑ j : Fin d, |D x j| :=
        Finset.single_le_sum (f := fun j => |D x j|)
          (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      calc
        |D x i * x i| = |D x i| * |x i| := abs_mul _ _
        _ ≤ |D x i| * Classical.choose hb :=
          mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)
        _ ≤ (∑ j : Fin d, |D x j|) * Classical.choose hb :=
          mul_le_mul_of_nonneg_right hsum hR
        _ = Classical.choose hb * (∑ j : Fin d, |D x j|) := mul_comm _ _
    _ = Classical.choose hb * ∫ x in V, ∑ j : Fin d, |D x j| ∂volume := by
      rw [integral_const_mul]

/-- Zero-boundary `W^{1,1}` Poincare on a bounded open set, expressed using
`L¹` functions and a supported smooth approximating sequence.  The constant
is chosen before the function, gradient, and approximating sequence. -/
theorem exists_zero_boundary_poincare_w11
    {d : ℕ} [NeZero d] {V : Set (Vec d)}
    (hV : IsOpen V) (hbounded : Bornology.IsBounded V) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d) (φ : ℕ → Vec d → ℝ),
        IntegrableOn u V →
        (∀ i : Fin d, IntegrableOn (fun x => G x i) V) →
        (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) →
        (∀ n, HasCompactSupport (φ n)) →
        (∀ n, tsupport (φ n) ⊆ V) →
        Filter.Tendsto
          (fun n => eLpNorm (fun x => φ n x - u x) 1 (volume.restrict V))
          Filter.atTop (nhds 0) →
        (∀ i : Fin d, Filter.Tendsto
          (fun n => eLpNorm
            (fun x => (fderiv ℝ (φ n) x) (basisVec i) - G x i)
            1 (volume.restrict V)) Filter.atTop (nhds 0)) →
        ∫ x in V, |u x| ∂volume ≤
          C * ∫ x in V, Real.sqrt (vecDot (G x) (G x)) ∂volume := by
  classical
  let hb : IsBoundedDomain V := hbounded.isBoundedDomain
  let R : ℝ := Classical.choose hb
  have hR : 0 < R := (Classical.choose_spec hb).1
  let B : Set (Vec d) := Metric.ball 0 (R + 1)
  have hB : IsOpenBoundedConvexDomain B :=
    isOpenBoundedConvexDomain_ball 0 (by positivity)
  have hBn : B.Nonempty := ⟨0, by simp [B]; positivity⟩
  have hVB : V ⊆ B := by
    intro x hx
    have hn : ‖x‖ ≤ R := hb.norm_le_choose hx
    simpa [B, Metric.mem_ball, dist_zero_right] using lt_of_le_of_lt hn (by linarith)
  obtain ⟨C0, hC0, hmean⟩ := exists_mean_zero_poincare_w11 hB hBn
  have hCR : 0 ≤ C0 + R := add_nonneg hC0 hR.le
  refine ⟨(C0 + R) * (d : ℝ), mul_nonneg hCR (Nat.cast_nonneg d), ?_⟩
  intro u G φ hu hGi hφsmooth hφcompact hφsub hval hgrad
  let μ : Measure (Vec d) := volume.restrict V
  let D : ℕ → Vec d → Vec d := fun n x i => (fderiv ℝ (φ n) x) (basisVec i)
  have hφint : ∀ n, Integrable (φ n) volume :=
    fun n => (hφsmooth n).continuous.integrable_of_hasCompactSupport (hφcompact n)
  have hDint : ∀ n i, Integrable (fun x => D n x i) volume := by
    intro n i
    exact (((hφsmooth n).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hφcompact n).fderiv_apply (𝕜 := ℝ) (basisVec i))
  have htest : ∀ n,
      ∫ x in V, |φ n x| ∂volume ≤
        (C0 + R) * ∫ x in V, ∑ i : Fin d, |D n x i| ∂volume := by
    intro n
    let ν : Measure (Vec d) := volume.restrict B
    let : IsFiniteMeasure ν := hB.isFiniteMeasure_restrict_volume
    have hfi : Integrable (φ n) ν := (hφint n).restrict
    have hdi : ∀ i, Integrable (fun x => D n x i) ν := fun i => (hDint n i).restrict
    have hlen : Integrable (fun x => Real.sqrt (vecDot (D n x) (D n x))) ν :=
      length_integrable hdi
    have hsum : Integrable (fun x => ∑ i : Fin d, |D n x i|) ν :=
      integrable_finsetSum Finset.univ (fun i _ => (hdi i).norm)
    have hz : ∀ x, x ∉ V → φ n x = 0 := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport (fun ht => hx (hφsub n ht))
    have hzd : ∀ x, x ∉ V → D n x = 0 := by
      intro x hx
      have ht : x ∉ tsupport (φ n) := fun ht => hx (hφsub n ht)
      have hd : fderiv ℝ (φ n) x = 0 := by
        by_contra hd
        exact ht (support_fderiv_subset (𝕜 := ℝ) (f := φ n) hd)
      ext i
      simp [D, hd]
    have hzB : ∀ x, x ∉ B → φ n x = 0 :=
      fun x hx => hz x (fun hv => hx (hVB hv))
    have hzsum : ∀ x, x ∉ V → (∑ i : Fin d, |D n x i|) = 0 := by
      intro x hx
      simp [hzd x hx]
    have hzsumB : ∀ x, x ∉ B → (∑ i : Fin d, |D n x i|) = 0 :=
      fun x hx => hzsum x (fun hv => hx (hVB hv))
    have hleftEq : (∫ x in V, |φ n x| ∂volume) = ∫ x, |φ n x| ∂ν := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hz x hx, abs_zero])]
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hzB x hx, abs_zero])
    have hsumEq : (∫ x, ∑ i : Fin d, |D n x i| ∂ν) =
        ∫ x in V, ∑ i : Fin d, |D n x i| ∂volume := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzsumB,
        setIntegral_eq_integral_of_forall_compl_eq_zero hzsum]
    have hmeanBound :
        (∫ x, |φ n x - volumeAverage B (φ n)| ∂ν) ≤
          C0 * ∫ x, Real.sqrt (vecDot (D n x) (D n x)) ∂ν :=
      hmean (φ n) (D n) hfi hdi
        (HasWeakGradientOn.of_contDiff ((hφsmooth n).of_le (by simp)))
    have hlengthBound :
        (∫ x, Real.sqrt (vecDot (D n x) (D n x)) ∂ν) ≤
          ∫ x, ∑ i : Fin d, |D n x i| ∂ν := by
      apply integral_mono_ae hlen hsum
      filter_upwards with x
      exact length_le_coord_sum (D n x)
    have hvol : 0 < (volume B).toReal :=
      ENNReal.toReal_pos (hB.isOpen.measure_pos volume hBn).ne' hB.volume_lt_top.ne
    have havgMass : (∫ x, |volumeAverage B (φ n)| ∂ν) = |∫ x, φ n x ∂ν| := by
      rw [integral_const]
      simp only [ν, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, volumeAverage,
        abs_mul, abs_inv, abs_of_pos hvol]
      rw [← mul_assoc, mul_inv_cancel₀ hvol.ne', one_mul]
    have hcenterInt : Integrable (fun x => |φ n x - volumeAverage B (φ n)|) ν :=
      (hfi.sub (integrable_const _)).norm
    have htriangle : (∫ x, |φ n x| ∂ν) ≤
        (∫ x, |φ n x - volumeAverage B (φ n)| ∂ν) + |∫ x, φ n x ∂ν| := by
      rw [← havgMass, ← integral_add hcenterInt (integrable_const _)]
      apply integral_mono_ae hfi.norm (hcenterInt.add (integrable_const _))
      filter_upwards with x
      simpa only [sub_add_cancel, Pi.add_apply, Real.norm_eq_abs] using
        abs_add_le (φ n x - volumeAverage B (φ n)) (volumeAverage B (φ n))
    have havgBound : |∫ x, φ n x ∂ν| ≤
        R * ∫ x in V, ∑ i : Fin d, |D n x i| ∂volume := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzB]
      exact compact_abs_integral_le_coord_variation hV hb
        (hφsmooth n) (hφcompact n) (hφsub n)
    calc
      ∫ x in V, |φ n x| ∂volume = ∫ x, |φ n x| ∂ν := hleftEq
      _ ≤ (∫ x, |φ n x - volumeAverage B (φ n)| ∂ν) + |∫ x, φ n x ∂ν| := htriangle
      _ ≤ C0 * (∫ x, Real.sqrt (vecDot (D n x) (D n x)) ∂ν) +
          R * (∫ x in V, ∑ i : Fin d, |D n x i| ∂volume) :=
        add_le_add hmeanBound havgBound
      _ ≤ C0 * (∫ x in V, ∑ i : Fin d, |D n x i| ∂volume) +
          R * (∫ x in V, ∑ i : Fin d, |D n x i| ∂volume) := by
        rw [← hsumEq]
        exact add_le_add (mul_le_mul_of_nonneg_left hlengthBound hC0) le_rfl
      _ = (C0 + R) * ∫ x in V, ∑ i : Fin d, |D n x i| ∂volume := by ring
  have hleft : Filter.Tendsto (fun n => ∫ x, |φ n x| ∂μ)
      Filter.atTop (nhds (∫ x, |u x| ∂μ)) :=
    tendsto_abs_integral_of_l1 (fun n => (hφint n).restrict) hu hval
  have hcoords : ∀ i : Fin d, Filter.Tendsto (fun n => ∫ x, |D n x i| ∂μ)
      Filter.atTop (nhds (∫ x, |G x i| ∂μ)) := by
    intro i
    exact tendsto_abs_integral_of_l1 (fun n => (hDint n i).restrict) (hGi i) (hgrad i)
  have hsumLimit : Filter.Tendsto (fun n => ∫ x, ∑ i : Fin d, |D n x i| ∂μ)
      Filter.atTop (nhds (∫ x, ∑ i : Fin d, |G x i| ∂μ)) := by
    have hsum := tendsto_finsetSum (s := Finset.univ)
      (f := fun i n => ∫ x, |D n x i| ∂μ)
      (a := fun i => ∫ x, |G x i| ∂μ) (fun i _ => hcoords i)
    have hseq : ∀ n, (∫ x, ∑ i : Fin d, |D n x i| ∂μ) =
        ∑ i : Fin d, ∫ x, |D n x i| ∂μ :=
      fun n => integral_finsetSum Finset.univ (fun i _ => (hDint n i).norm.restrict)
    have htarget : (∫ x, ∑ i : Fin d, |G x i| ∂μ) =
        ∑ i : Fin d, ∫ x, |G x i| ∂μ :=
      integral_finsetSum Finset.univ (fun i _ => (hGi i).norm)
    simpa only [hseq, htarget] using hsum
  have hright : Filter.Tendsto
      (fun n => (C0 + R) * ∫ x, ∑ i : Fin d, |D n x i| ∂μ)
      Filter.atTop (nhds ((C0 + R) * ∫ x, ∑ i : Fin d, |G x i| ∂μ)) :=
    tendsto_const_nhds.mul hsumLimit
  have hlimit := le_of_tendsto_of_tendsto' hleft hright htest
  have hGsum : Integrable (fun x => ∑ i : Fin d, |G x i|) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hGi i).norm)
  have hGlen : Integrable (fun x => Real.sqrt (vecDot (G x) (G x))) μ :=
    length_integrable hGi
  have hfinal : (∫ x, ∑ i : Fin d, |G x i| ∂μ) ≤
      (d : ℝ) * ∫ x, Real.sqrt (vecDot (G x) (G x)) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hGsum (hGlen.const_mul _)
    filter_upwards with x
    exact coord_sum_le_dim_length (G x)
  simpa only [mul_assoc] using
    hlimit.trans (mul_le_mul_of_nonneg_left hfinal hCR)

end CoarseDeGiorgi.Foundations
