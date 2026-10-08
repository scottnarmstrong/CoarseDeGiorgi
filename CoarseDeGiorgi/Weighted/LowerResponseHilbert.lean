import CoarseDeGiorgi.Weighted.PairSeparation
import CoarseDeGiorgi.Weighted.LowerResponseZero

/-! Continuous gradient integrals and the Riesz map for the lower response. -/

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Unnormalized gradient integration, extended from the finite-energy core. -/
noncomputable def lowerGradientIntegral (ha : IsWeightedCoeffOn V a) :
    GradientHilbert ha →L[ℝ] Vec d :=
  ((MeasureTheory.L1.integralCLM (α := Vec d) (E := Vec d)
    (μ := volume.restrict V)).comp (GradientCore.toL1 ha)).fromCompletion

/-- The extended integration map agrees with literal integrals of representatives. -/
theorem lowerGradientIntegral_coe (ha : IsWeightedCoeffOn V a) (G : GradientCore ha) :
    lowerGradientIntegral ha (G : GradientHilbert ha) = ∫ x in V, G.field x := by
  rw [lowerGradientIntegral, ContinuousLinearMap.fromCompletion_apply_coe]
  change MeasureTheory.L1.integralCLM ((GradientCore.integrable ha G).toL1 G.field) = _
  rw [← MeasureTheory.L1.integral_eq]
  rw [MeasureTheory.integral, dite_eq_left (inferInstance : CompleteSpace (Vec d)),
    dite_eq_left (GradientCore.integrable ha G)]

/-- The finite-coordinate dot product as a continuous linear functional. -/
noncomputable def lowerDot (e : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, e i • ContinuousLinearMap.proj i

theorem lowerDot_apply (e v : Vec d) : lowerDot e v = vecDot e v := by
  simp only [lowerDot, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, vecDot]

/-- Directional gradient integration on the full weighted Hilbert graph. -/
noncomputable def lowerGradientFunctional (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    (e : Vec d) : WeightedHilbert hV ha →L[ℝ] ℝ :=
  (lowerDot e).comp ((lowerGradientIntegral ha).comp
    ((WithLp.sndL 2 ℝ ℝ (GradientHilbert ha)).comp (weightedSubmodule hV ha).subtypeL))

/-- Riesz representative of unnormalized directional gradient integration. -/
noncomputable def lowerRiesz (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    (e : Vec d) : WeightedHilbert hV ha :=
  (InnerProductSpace.toDual ℝ (WeightedHilbert hV ha)).symm
    (lowerGradientFunctional hV ha e)

theorem lowerRiesz_inner (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    (e : Vec d) (x : WeightedHilbert hV ha) :
    inner ℝ (lowerRiesz hV ha e) x =
      vecDot e (lowerGradientIntegral ha x.val.snd) := by
  rw [lowerRiesz, InnerProductSpace.toDual_symm_apply]
  exact lowerDot_apply _ _

/-- Constants lie in the smooth core on bounded domains. -/
theorem lower_const_core (hV : IsOpenBoundedConvexDomain V)
    (c : ℝ) : IsSmoothCore a V (fun _ => c) := by
  refine ⟨contDiffOn_const, integrableOn_const hV.isBoundedDomain.isBounded.measure_lt_top.ne, ?_⟩
  simp [CoarseDeGiorgi.weightedEnergy, CoarseDeGiorgi.smoothGrad, vecDot, matVecMul]

/-- A constant has zero gradient component in the smooth graph. -/
theorem lower_const_gradient (hV : IsOpenBoundedConvexDomain V)
    (ha : IsWeightedCoeffOn V a) (c : ℝ) :
    (smoothGraphMap hV.isOpen ha ⟨fun _ => c, lower_const_core hV c⟩).snd = 0 := by
  change (smoothEnergyField hV.isOpen ha (lower_const_core hV c) : GradientHilbert ha) = 0
  rw [← UniformSpace.Completion.coe_zero]
  apply (GradientCore.coe_eq_iff ha _ _).mpr
  apply Eventually.of_forall
  intro x
  change CoarseDeGiorgi.smoothGrad (fun _ => c) x = 0
  funext i
  simp [CoarseDeGiorgi.smoothGrad]

/-- Testing Riesz with the constant one makes its mean zero. -/
theorem lowerRiesz_mean_zero (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) : (lowerRiesz hV.isOpen ha e).val.fst = 0 := by
  let f : smoothCoreSubmodule hV.isOpen ha := ⟨fun _ => 1, lower_const_core hV 1⟩
  let x : WeightedHilbert hV.isOpen ha :=
    ⟨smoothGraphMap hV.isOpen ha f, subset_closure ⟨f, rfl⟩⟩
  have hxg : x.val.snd = 0 := lower_const_gradient hV ha 1
  have hvol : (volume V).toReal ≠ 0 :=
    (ENNReal.toReal_pos (hV.isOpen.measure_pos volume hne).ne'
      hV.isBoundedDomain.isBounded.measure_lt_top.ne).ne'
  have hxm : x.val.fst = 1 := volumeAverage_const hvol
  have hh := lowerRiesz_inner hV.isOpen ha e x
  change inner ℝ (lowerRiesz hV.isOpen ha e).val x.val = _ at hh
  rw [WithLp.prod_inner_apply] at hh
  change inner ℝ (lowerRiesz hV.isOpen ha e).val.fst x.val.fst +
    inner ℝ (lowerRiesz hV.isOpen ha e).val.snd x.val.snd = _ at hh
  rw [hxg, hxm, inner_zero_right, map_zero, vecDot_zero_right,
    add_zero, real_inner_comm] at hh
  simpa only [Real.inner_apply, one_mul] using hh

/-- The Riesz representatives vary linearly with the direction. -/
noncomputable def lowerRieszLinear (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    Vec d →ₗ[ℝ] WeightedHilbert hV ha where
  toFun := lowerRiesz hV ha
  map_add' e f := by
    apply ext_inner_right ℝ
    intro x
    rw [inner_add_left, lowerRiesz_inner, lowerRiesz_inner, lowerRiesz_inner,
      vecDot_add_left]
  map_smul' c e := by
    apply ext_inner_right ℝ
    intro x
    rw [real_inner_smul_left, lowerRiesz_inner, lowerRiesz_inner, vecDot_smul_left]
    rfl

/-- The full graph pairing with the mean-zero Riesz element is an energy pairing. -/
theorem lowerRiesz_gradient_inner (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) (x : WeightedHilbert hV.isOpen ha) :
    inner ℝ x.val.snd (lowerRiesz hV.isOpen ha e).val.snd =
      vecDot e (lowerGradientIntegral ha x.val.snd) := by
  have hh := lowerRiesz_inner hV.isOpen ha e x
  change inner ℝ (lowerRiesz hV.isOpen ha e).val x.val = _ at hh
  rw [WithLp.prod_inner_apply] at hh
  change inner ℝ (lowerRiesz hV.isOpen ha e).val.fst x.val.fst +
    inner ℝ (lowerRiesz hV.isOpen ha e).val.snd x.val.snd = _ at hh
  rw [lowerRiesz_mean_zero hV hne ha, inner_zero_left, zero_add] at hh
  rw [real_inner_comm]
  exact hh



end CoarseDeGiorgi.Weighted
