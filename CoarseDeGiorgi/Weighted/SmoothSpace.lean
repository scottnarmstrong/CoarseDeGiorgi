module

public import CoarseDeGiorgi.Weighted.GradientRepresentation
public import CoarseDeGiorgi.Weighted.SmoothCore
public import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Classical gradients respect addition on the open smoothness domain. -/
theorem smoothGrad_add_ae (hV : IsOpen V) {f g : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V) :
    smoothGrad (f + g) =ᵐ[volume.restrict V] smoothGrad f + smoothGrad g := by
  filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
  funext i
  change fderiv ℝ (f + g) x (basisVec i) = _
  rw [fderiv_add ((hf.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx))
    ((hg.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx))]
  rfl

/-- Classical gradients respect real scalar multiplication on an open domain. -/
theorem smoothGrad_smul_ae (hV : IsOpen V) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) (c : ℝ) :
    smoothGrad (c • f) =ᵐ[volume.restrict V] c • smoothGrad f := by
  filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
  funext i
  change fderiv ℝ (c • f) x (basisVec i) = _
  rw [fderiv_const_smul ((hf.differentiableOn (by simp) x hx).differentiableAt
    (hV.mem_nhds hx))]
  rfl

/-- A smooth core gradient as a finite-energy representative. -/
noncomputable def smoothEnergyField (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {f : Vec d → ℝ} (hf : IsSmoothCore a V f) : GradientCore ha :=
  ⟨smoothGrad f, smoothGrad_aestronglyMeasurable hV hf.1,
    quadratic_integrable ha (smoothGrad_aestronglyMeasurable hV hf.1) hf.2.2⟩

theorem smoothEnergyField_field (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {f : Vec d → ℝ} (hf : IsSmoothCore a V f) :
    (smoothEnergyField hV ha hf).field = smoothGrad f := rfl

/-- The literal smooth core is a vector space. -/
noncomputable abbrev smoothCoreSubmodule (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    Submodule ℝ (Vec d → ℝ) where
  carrier := {f | IsSmoothCore a V f}
  zero_mem' := by
    refine ⟨contDiffOn_const, integrableOn_zero, ?_⟩
    simp [CoarseDeGiorgi.weightedEnergy,
      CoarseDeGiorgi.smoothGrad, vecDot, matVecMul]
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, ?_⟩
    refine (energy_congr_ae (smoothGrad_add_ae hV hf.1 hg.1)).trans_lt ?_
    exact energy_add_lt_top ha
      (smoothGrad_aestronglyMeasurable hV hf.1)
      (smoothGrad_aestronglyMeasurable hV hg.1) hf.2.2 hg.2.2
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, hf.2.1.smul c, ?_⟩
    refine (energy_congr_ae (smoothGrad_smul_ae hV hf.1 c)).trans_lt ?_
    exact GradientCore.energy_lt_top ha (c • smoothEnergyField hV ha hf)

/-- Mean and gradient ambient Hilbert space, with the squared-mean-plus-energy norm. -/
abbrev WeightedAmbient (ha : IsWeightedCoeffOn V a) := WithLp 2 (ℝ × GradientHilbert ha)

/-- The graph of smooth functions in the shared Hilbert ambient space. -/
noncomputable def smoothGraphMap (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    smoothCoreSubmodule hV ha →ₗ[ℝ] WeightedAmbient ha where
  toFun f := WithLp.toLp 2 (volumeAverage V f.val,
    (smoothEnergyField hV ha f.property : GradientHilbert ha))
  map_add' f g := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact volumeAverage_add f.property.2.1 g.property.2.1
    · change (smoothEnergyField hV ha (f + g).property : GradientHilbert ha) =
        (smoothEnergyField hV ha f.property : GradientHilbert ha) +
          (smoothEnergyField hV ha g.property : GradientHilbert ha)
      rw [← UniformSpace.Completion.coe_add]
      apply (GradientCore.coe_eq_iff ha _ _).mpr
      exact smoothGrad_add_ae hV f.property.1 g.property.1
  map_smul' c f := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact volumeAverage_smul V c f.val
    · change (smoothEnergyField hV ha (c • f).property : GradientHilbert ha) =
        c • (smoothEnergyField hV ha f.property : GradientHilbert ha)
      rw [← UniformSpace.Completion.coe_smul]
      apply (GradientCore.coe_eq_iff ha _ _).mpr
      exact smoothGrad_smul_ae hV f.property.1 c

/-- The graph distance agrees with the literal mean-plus-energy expression. -/
theorem smoothGraph_distance (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    (f g : smoothCoreSubmodule hV ha) :
    ENNReal.ofReal ((volumeAverage V (f.val - g.val)) ^ 2) +
      weightedEnergy a V (smoothGrad f.val - smoothGrad g.val) =
        ENNReal.ofReal (‖smoothGraphMap hV ha f - smoothGraphMap hV ha g‖ ^ 2) := by
  have he : weightedEnergy a V (smoothGrad f.val - smoothGrad g.val) < ⊤ := by
    simpa only [GradientCore.field_sub, smoothEnergyField_field] using
      GradientCore.energy_lt_top ha
        (smoothEnergyField hV ha f.property - smoothEnergyField hV ha g.property)
  have hn : ‖smoothGraphMap hV ha f - smoothGraphMap hV ha g‖ ^ 2 =
      (volumeAverage V (f.val - g.val)) ^ 2 +
        (weightedEnergy a V (smoothGrad f.val - smoothGrad g.val)).toReal := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖volumeAverage V f.val - volumeAverage V g.val‖ ^ 2 +
      ‖(smoothEnergyField hV ha f.property : GradientHilbert ha) -
        (smoothEnergyField hV ha g.property : GradientHilbert ha)‖ ^ 2 = _
    rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe,
      GradientCore.norm_sq, GradientCore.field_sub, smoothEnergyField_field,
      smoothEnergyField_field, volumeAverage_sub f.property.2.1 g.property.2.1]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [hn, ENNReal.ofReal_add (sq_nonneg _) ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal he.ne]

/-- The full weighted Hilbert space is the closure of the smooth graph. -/
noncomputable def weightedSubmodule (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    Submodule ℝ (WeightedAmbient ha) := (smoothGraphMap hV ha).range.topologicalClosure

/-- Full weighted Sobolev Hilbert carrier. -/
noncomputable abbrev WeightedHilbert (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :=
  weightedSubmodule hV ha

/-- Completeness is inherited from the closed graph subspace. -/
instance weightedHilbert_complete (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    CompleteSpace (WeightedHilbert hV ha) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

end CoarseDeGiorgi.Weighted
