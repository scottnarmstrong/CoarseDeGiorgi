module

public import CoarseDeGiorgi.Foundations.Reconstruction.FoldedWeakIdentity
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.FaceVanishCollar
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # L¹ closure of the weak identity for tests vanishing on two cube faces

The derivative of the cutoff times the face-zero test is uniformly bounded.
Dominated convergence therefore uses only the integrability of the scalar and
its weak derivative, with no square-integrability assumption on either field.
-/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

variable {d : ℕ}

/-- Multiplication by uniformly bounded, a.e. convergent factors preserves
convergence of their integrals against an L¹ function. -/
theorem tendsto_integral_mul_bounded {μ : Measure (Vec d)} {u : Vec d → ℝ}
    (hu : Integrable u μ) {g : ℕ → Vec d → ℝ} {g₀ : Vec d → ℝ} {C : ℝ}
    (hg : ∀ n, AEStronglyMeasurable (g n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖g n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (g₀ x))) :
    Tendsto (fun n => ∫ x, u x * g n x ∂μ) atTop (𝓝 (∫ x, u x * g₀ x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖u x‖ * C)
  · intro n
    exact hu.aestronglyMeasurable.mul (hg n)
  · exact hu.norm.mul_const C
  · intro n
    filter_upwards [hbound n] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.mul hx

/-- Inner cutoffs are eventually one at every interior point. -/
theorem eventually_faceCutoff_eq_one (Q : TriadicCube d) {x : Vec d}
    (hx : x ∈ openCubeSet Q) : ∀ᶠ n : ℕ in atTop, faceCutoff Q n x = 1 := by
  have h := QuantitativeCubeCutoff.eventually_eq_one_on_compacts_of_tendsto_inner
    (fun n => faceCutoff Q n) tendsto_faceCutoffInnerRadius_one
    {x} isCompact_singleton (Set.singleton_subset_iff.mpr hx)
  exact h.mono fun _ hn => hn x (Set.mem_singleton x)

/-- The coordinate cutoff derivative is eventually zero at every interior point. -/
theorem eventually_fderiv_faceCutoff_eq_zero (Q : TriadicCube d) (i : Fin d)
    {x : Vec d} (hx : x ∈ openCubeSet Q) :
    ∀ᶠ n : ℕ in atTop, (fderiv ℝ (faceCutoff Q n) x) (basisVec i) = 0 := by
  have hxball : dist x (cubeCenter Q) < cubeRadius Q := by
    simpa only [← ball_cubeCenter_eq_openCubeSet Q, Metric.mem_ball] using hx
  have hcoord : |x i - cubeCenter Q i| ≤ dist x (cubeCenter Q) := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs, dist_eq_norm] using
      (norm_le_pi_norm (x - cubeCenter Q) i)
  have hxi : |x i - cubeCenter Q i| < cubeRadius Q := hcoord.trans_lt hxball
  have hrad : Tendsto (fun n => faceCutoffInnerRadius n * cubeRadius Q)
      atTop (𝓝 (cubeRadius Q)) := by
    simpa only [one_mul] using tendsto_faceCutoffInnerRadius_one.mul_const (cubeRadius Q)
  have he := hrad.eventually (isOpen_Ioi.mem_nhds hxi)
  filter_upwards [he] with n hn
  exact QuantitativeCubeCutoff.canonicalFun_fderiv_apply_basisVec_eq_zero_of_abs_sub_center_lt_inner
    Q (faceCutoffInnerRadius_pos n) (faceCutoffInnerRadius_lt_outer n) hn

/-- The boundary-error integral vanishes with an arbitrary integrable scalar weight. -/
theorem tendsto_integral_cutoff_face_error (Q : TriadicCube d) (i : Fin d)
    {w ψ : Vec d → ℝ} (hw : IntegrableOn w (openCubeSet Q) volume)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x, ‖fderiv ℝ ψ x‖ ≤ L)
    (hlower : ∀ x, ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper : ∀ x, ψ (cubeUpperFaceProjection Q i x) = 0) :
    Tendsto (fun n => ∫ x in openCubeSet Q, w x *
      ((fderiv ℝ (faceCutoff Q n) x) (basisVec i) * ψ x) ∂volume)
      atTop (𝓝 0) := by
  have h := tendsto_integral_mul_bounded hw
    (g := fun n x => (fderiv ℝ (faceCutoff Q n) x) (basisVec i) * ψ x)
    (g₀ := fun _ => 0) (C := (L * 2) * quantitativeCubeCutoffGradientConst d) ?_ ?_ ?_
  · simpa only [mul_zero, integral_zero] using h
  · intro n
    exact ((((faceCutoff Q n).smooth.continuous_fderiv (by norm_num)).clm_apply
      continuous_const).mul hψ.continuous).aestronglyMeasurable
  · intro n
    exact ae_of_all _ (norm_canonicalFun_coordDeriv_mul_le_of_face_zero Q
      (faceCutoffInnerRadius_pos n) (faceCutoffInnerRadius_lt_outer n)
      (faceCutoffOuterRadius_le_one n) hL (by norm_num)
      (faceCutoffInnerOuter_width_control n) i ψ hψ hbound hlower hupper)
  · filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact tendsto_const_nhds.congr' ((eventually_fderiv_faceCutoff_eq_zero Q i hx).mono
      fun n hn => by dsimp only; rw [hn, zero_mul])

/-- L¹ weak derivatives may be tested against smooth compact tests that vanish
on the two relevant faces, even when their support reaches those faces. -/
theorem weakPartial_integral_face_zero (Q : TriadicCube d) (i : Fin d)
    {w gi ψ : Vec d → ℝ} (hweak : HasWeakPartialDerivOn (openCubeSet Q) i w gi)
    (hw : IntegrableOn w (openCubeSet Q) volume)
    (hgi : IntegrableOn gi (openCubeSet Q) volume)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcompact : HasCompactSupport ψ)
    (hlower : ∀ x, ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper : ∀ x, ψ (cubeUpperFaceProjection Q i x) = 0) :
    ∫ x in openCubeSet Q, w x * (fderiv ℝ ψ x) (basisVec i) ∂volume =
      -∫ x in openCubeSet Q, gi x * ψ x ∂volume := by
  obtain ⟨L, hL, hbound⟩ := exists_bound_fderiv_of_contDiff_hasCompactSupport hψ hcompact
  obtain ⟨M, hM⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hcompact.norm
  have hnormψ : ∀ x, ‖ψ x‖ ≤ M := by
    intro x
    exact hM (Set.mem_range_self x)
  have hb : ‖basisVec i‖ ≤ (1 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro j
    simp only [basisVec_apply]
    split_ifs <;> norm_num
  have hdψ : ∀ x, ‖(fderiv ℝ ψ x) (basisVec i)‖ ≤ L := by
    intro x
    calc
      ‖(fderiv ℝ ψ x) (basisVec i)‖ ≤ ‖fderiv ℝ ψ x‖ * ‖basisVec i‖ :=
        (fderiv ℝ ψ x).le_opNorm _
      _ ≤ L * 1 := mul_le_mul (hbound x) hb (norm_nonneg _) hL
      _ = L := mul_one L
  have hleft := tendsto_integral_mul_bounded hw
    (g := fun n x => faceCutoff Q n x * (fderiv ℝ ψ x) (basisVec i))
    (g₀ := fun x => (fderiv ℝ ψ x) (basisVec i)) (C := L) ?_ ?_ ?_
  · have hright := tendsto_integral_mul_bounded hgi
      (g := fun n x => faceCutoff Q n x * ψ x) (g₀ := ψ) (C := M) ?_ ?_ ?_
    · have herr := tendsto_integral_cutoff_face_error Q i hw hψ hL hbound hlower hupper
      have hseq : ∀ n,
          (∫ x in openCubeSet Q, w x * (faceCutoff Q n x *
            (fderiv ℝ ψ x) (basisVec i)) ∂volume) +
          (∫ x in openCubeSet Q, w x *
            ((fderiv ℝ (faceCutoff Q n) x) (basisVec i) * ψ x) ∂volume) =
          -∫ x in openCubeSet Q, gi x * (faceCutoff Q n x * ψ x) ∂volume := by
        intro n
        have htest := hweak ((faceCutoff Q n) * ψ) ((faceCutoff Q n).smooth.mul hψ)
          (faceCutoff Q n).hasCompactSupport.mul_right
          (tsupport_mul_subset_left.trans
            ((faceCutoff Q n).tsupport_subset_openCubeSet_of_nonneg_of_lt_one
              (faceCutoffOuterRadius_nonneg n) (faceCutoffOuterRadius_lt_one n)))
        have hI₁ : IntegrableOn (fun x => w x * (faceCutoff Q n x *
            (fderiv ℝ ψ x) (basisVec i))) (openCubeSet Q) volume := by
          refine hw.mul_bdd (c := L) ?_ (ae_of_all _ fun x => ?_)
          · exact ((faceCutoff Q n).smooth.continuous.mul
              ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)).aestronglyMeasurable
          · rw [norm_mul]
            calc
              ‖faceCutoff Q n x‖ * ‖(fderiv ℝ ψ x) (basisVec i)‖ ≤
                  1 * ‖(fderiv ℝ ψ x) (basisVec i)‖ := by
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                rw [Real.norm_eq_abs, abs_of_nonneg ((faceCutoff Q n).nonneg x)]
                exact (faceCutoff Q n).le_one x
              _ ≤ L := by simpa only [one_mul] using hdψ x
        have hI₂ : IntegrableOn (fun x => w x *
            ((fderiv ℝ (faceCutoff Q n) x) (basisVec i) * ψ x)) (openCubeSet Q) volume := by
          refine hw.mul_bdd ?_ (ae_of_all _ (norm_canonicalFun_coordDeriv_mul_le_of_face_zero Q
            (faceCutoffInnerRadius_pos n) (faceCutoffInnerRadius_lt_outer n)
            (faceCutoffOuterRadius_le_one n) hL (by norm_num)
            (faceCutoffInnerOuter_width_control n) i ψ hψ hbound hlower hupper))
          exact ((((faceCutoff Q n).smooth.continuous_fderiv (by norm_num)).clm_apply
            continuous_const).mul hψ.continuous).aestronglyMeasurable
        rw [← integral_add hI₁ hI₂]
        convert htest using 1
        apply setIntegral_congr_fun (measurableSet_openCubeSet Q)
        intro x _
        dsimp only
        rw [fderiv_mul ((faceCutoff Q n).smooth.differentiable (by norm_num) x)
          (hψ.differentiable (by norm_num) x)]
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
      have heq := tendsto_nhds_unique
        ((hleft.add herr).congr' (Filter.Eventually.of_forall hseq)) hright.neg
      simpa only [add_zero] using heq
    · intro n
      exact ((faceCutoff Q n).smooth.continuous.mul hψ.continuous).aestronglyMeasurable
    · intro n
      exact ae_of_all _ fun x => by
        rw [norm_mul]
        calc
          ‖faceCutoff Q n x‖ * ‖ψ x‖ ≤ 1 * ‖ψ x‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            rw [Real.norm_eq_abs, abs_of_nonneg ((faceCutoff Q n).nonneg x)]
            exact (faceCutoff Q n).le_one x
          _ ≤ M := by simpa only [one_mul] using hnormψ x
    · filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
      exact tendsto_const_nhds.congr' ((eventually_faceCutoff_eq_one Q hx).mono
        fun n hn => by dsimp only; rw [hn, one_mul])
  · intro n
    exact ((faceCutoff Q n).smooth.continuous.mul
      ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)).aestronglyMeasurable
  · intro n
    exact ae_of_all _ fun x => by
      rw [norm_mul]
      calc
        ‖faceCutoff Q n x‖ * ‖(fderiv ℝ ψ x) (basisVec i)‖ ≤
            1 * ‖(fderiv ℝ ψ x) (basisVec i)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg ((faceCutoff Q n).nonneg x)]
          exact (faceCutoff Q n).le_one x
        _ ≤ L := by simpa only [one_mul] using hdψ x
  · filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact tendsto_const_nhds.congr' ((eventually_faceCutoff_eq_one Q hx).mono
      fun n hn => by dsimp only; rw [hn, one_mul])

/-- Compact support of the face-zero test is unnecessary on a bounded cube:
a fixed outer cutoff is identically one on a neighbourhood of every interior point. -/
theorem weakPartial_integral_face_zero_of_contDiff (Q : TriadicCube d) (i : Fin d)
    {w gi ψ : Vec d → ℝ} (hweak : HasWeakPartialDerivOn (openCubeSet Q) i w gi)
    (hw : IntegrableOn w (openCubeSet Q) volume)
    (hgi : IntegrableOn gi (openCubeSet Q) volume)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hlower : ∀ x, ψ (cubeLowerFaceProjection Q i x) = 0)
    (hupper : ∀ x, ψ (cubeUpperFaceProjection Q i x) = 0) :
    ∫ x in openCubeSet Q, w x * (fderiv ℝ ψ x) (basisVec i) ∂volume =
      -∫ x in openCubeSet Q, gi x * ψ x ∂volume := by
  let Ψ : Vec d → ℝ := fun x => faceCompactifyingCutoff Q x * ψ x
  have hs : ContDiff ℝ (⊤ : ℕ∞) Ψ := (faceCompactifyingCutoff Q).smooth.mul hψ
  have hc : HasCompactSupport Ψ := (faceCompactifyingCutoff Q).hasCompactSupport.mul_right
  have heq : ∀ x ∈ openCubeSet Q, Ψ x = ψ x := by
    intro x hx
    dsimp only [Ψ]
    rw [faceCompactifyingCutoff_eq_one_on_openCubeSet Q hx, one_mul]
  have hd : ∀ x ∈ openCubeSet Q, fderiv ℝ Ψ x = fderiv ℝ ψ x := by
    intro x hx
    have he : Ψ =ᶠ[𝓝 x] ψ := by
      filter_upwards [(isOpen_openCubeSet Q).mem_nhds hx] with y hy
      exact heq y hy
    exact he.fderiv_eq
  have h := weakPartial_integral_face_zero Q i hweak hw hgi hs hc
    (fun x => by dsimp only [Ψ]; rw [hlower x, mul_zero])
    (fun x => by dsimp only [Ψ]; rw [hupper x, mul_zero])
  calc
    ∫ x in openCubeSet Q, w x * (fderiv ℝ ψ x) (basisVec i) ∂volume =
        ∫ x in openCubeSet Q, w x * (fderiv ℝ Ψ x) (basisVec i) ∂volume := by
      apply setIntegral_congr_fun (measurableSet_openCubeSet Q)
      intro x hx
      dsimp only
      rw [hd x hx]
    _ = -∫ x in openCubeSet Q, gi x * Ψ x ∂volume := h
    _ = -∫ x in openCubeSet Q, gi x * ψ x ∂volume := by
      congr 1
      apply setIntegral_congr_fun (measurableSet_openCubeSet Q)
      intro x hx
      dsimp only
      rw [heq x hx]

end

end CoarseDeGiorgi.Foundations.Reconstruction
