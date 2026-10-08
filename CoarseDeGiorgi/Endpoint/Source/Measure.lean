module

public import CoarseDeGiorgi.Endpoint.Source.Functional
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Analysis.Convex.Cone.Extension

/-! Riesz representation of the flux functional of a supersolution by a Radon measure. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted
open scoped CompactlySupported

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

theorem isCompact_preimage_val {K : Set (Vec d)} (hK : IsCompact K) (hKV : K ⊆ V) :
    IsCompact ((Subtype.val : V → Vec d) ⁻¹' K) := by
  rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.mpr hKV]
  exact hK

/-- Restriction of a supported smooth test to the subtype `V`, as a compactly supported map. -/
noncomputable def toCc (V : Set (Vec d)) (φ : supportedCoreSubmodule V) : C_c(↥V, ℝ) where
  toFun x := φ.1 x.1
  continuous_toFun := φ.2.1.continuous.comp continuous_subtype_val
  hasCompactSupport' := by
    refine HasCompactSupport.intro (isCompact_preimage_val φ.2.2.1 φ.2.2.2) ?_
    intro x hx
    by_contra h
    exact hx (subset_tsupport _ h)

noncomputable def toCcLin (V : Set (Vec d)) : supportedCoreSubmodule V →ₗ[ℝ] C_c(↥V, ℝ) where
  toFun := toCc V
  map_add' φ ψ := by ext x; rfl
  map_smul' c φ := by ext x; rfl

theorem toCcLin_injective : Function.Injective (toCcLin V) := by
  intro φ ψ h
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ V
  · exact congrArg (fun f : C_c(↥V, ℝ) => f ⟨x, hx⟩) h
  · have h1 : x ∉ tsupport φ.1 := fun h' => hx (φ.2.2.2 h')
    have h2 : x ∉ tsupport ψ.1 := fun h' => hx (ψ.2.2.2 h')
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

/-- The nonnegative cone of compactly supported continuous functions. -/
noncomputable def posCone (X : Type*) [TopologicalSpace X] : PointedCone ℝ C_c(X, ℝ) where
  carrier := {f | 0 ≤ f}
  add_mem' := fun {f g} hf hg => by
    intro x
    have h1 := hf x
    have h2 := hg x
    change 0 ≤ f x + g x
    exact add_nonneg h1 h2
  zero_mem' := show (0 : C_c(X, ℝ)) ≤ 0 from le_rfl
  smul_mem' := fun c f hf => by
    intro x
    have := hf x
    change 0 ≤ (c : ℝ) * f x
    exact mul_nonneg c.2 this

/-- A supersolution is a weighted Sobolev pair. -/
theorem supersolution_memH1a [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hs : CoarseDeGiorgi.IsWeightedSupersolution a V u G) : CoarseDeGiorgi.MemH1a a V u G := by
  have h := MemH1a.neg hV hne ha hs.1
  have h1 : (-fun x => -u x) = u := by funext x; simp
  have h2 : (-fun x => -G x) = G := by funext x; simp
  rwa [h1, h2] at h

theorem exists_flux_measure [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hs : CoarseDeGiorgi.IsWeightedSupersolution a V u G) :
    ∃ μ : Measure (Vec d), μ Vᶜ = 0 ∧
      (∀ K : Set (Vec d), IsCompact K → K ⊆ V → μ K < ⊤) ∧
      ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ V →
        ∫ x, φ x ∂μ = ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) ∂volume := by
  have hmem := supersolution_memH1a hV hne ha hs
  have hG := hmem.2.1
  have hEG := MemH1a.energy_lt_top hV.isOpen ha hmem
  let Λ : supportedCoreSubmodule V →ₗ[ℝ] ℝ :=
    { toFun := fun φ => fluxPairing a V G φ.1
      map_add' := fun φ ψ => fluxPairing_add hV.isOpen ha hG hEG φ.2.1 φ.2.2.1 φ.2.2.2
        ψ.2.1 ψ.2.2.1 ψ.2.2.2
      map_smul' := fun c φ => fluxPairing_smul c φ.2.1 }
  have hΛnn : ∀ φ : supportedCoreSubmodule V, (∀ x, 0 ≤ φ.1 x) → 0 ≤ Λ φ :=
    fun φ h => fluxPairing_nonneg hs φ.2.1 φ.2.2.1 φ.2.2.2 h
  let e := LinearEquiv.ofInjective (toCcLin V) toCcLin_injective
  let f : C_c(↥V, ℝ) →ₗ.[ℝ] ℝ :=
    { domain := LinearMap.range (toCcLin V)
      toFun := Λ ∘ₗ e.symm.toLinearMap }
  have hf : ∀ φ : supportedCoreSubmodule V,
      f ⟨toCcLin V φ, ⟨φ, rfl⟩⟩ = Λ φ := by
    intro φ
    have : e φ = ⟨toCcLin V φ, ⟨φ, rfl⟩⟩ := Subtype.ext rfl
    change Λ (e.symm _) = _
    rw [← this, LinearEquiv.symm_apply_apply]
  have hnonneg : ∀ x : f.domain, (x : C_c(↥V, ℝ)) ∈ posCone ↥V → 0 ≤ f x := by
    rintro ⟨x, φ, rfl⟩ hx
    rw [show (⟨toCcLin V φ, φ, rfl⟩ : f.domain) = ⟨toCcLin V φ, ⟨φ, rfl⟩⟩ from rfl, hf]
    apply hΛnn
    intro y
    by_cases hy : y ∈ V
    · exact hx ⟨y, hy⟩
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hy (φ.2.2.2 h'))]
  have hdense : ∀ y : C_c(↥V, ℝ), ∃ x : f.domain, (x : C_c(↥V, ℝ)) + y ∈ posCone ↥V := by
    intro y
    obtain ⟨C, hC⟩ := y.hasCompactSupport.exists_bound_of_continuous y.continuous
    have hKc : IsCompact (Subtype.val '' tsupport y) := y.hasCompactSupport.image continuous_subtype_val
    obtain ⟨φ, hφ, hφc, hφs, hφ01, hφ1⟩ := exists_cutoff01 hV.isOpen hKc
      (by rintro _ ⟨x, -, rfl⟩; exact x.2)
    let ψ : supportedCoreSubmodule V := (max C 0) • ⟨φ, hφ, hφc, hφs⟩
    refine ⟨⟨toCcLin V ψ, ψ, rfl⟩, ?_⟩
    intro x
    change 0 ≤ (max C 0) * φ x.1 + y x
    by_cases hx : x ∈ tsupport y
    · rw [hφ1 x.1 ⟨x, hx, rfl⟩, mul_one]
      have := hC x
      rw [Real.norm_eq_abs] at this
      have := neg_abs_le (y x)
      linarith [le_max_left C 0]
    · rw [image_eq_zero_of_notMem_tsupport hx, add_zero]
      exact mul_nonneg (le_max_right _ _) (hφ01 _).1
  obtain ⟨g, hg1, hg2⟩ := riesz_extension (posCone ↥V) f hnonneg hdense
  let Λt : C_c(↥V, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ g (fun x hx => hg2 x hx)
  have : LocallyCompactSpace ↥V := hV.isOpen.locallyCompactSpace
  let ρ : Measure ↥V := RealRMK.rieszMeasure Λt
  refine ⟨ρ.map Subtype.val, ?_, ?_, ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hV.isOpen.measurableSet.compl]
    have : (Subtype.val : V → Vec d) ⁻¹' Vᶜ = ∅ := by ext x; simp
    rw [this, measure_empty]
  · intro K hK hKV
    rw [Measure.map_apply measurable_subtype_coe hK.measurableSet]
    exact (isCompact_preimage_val hK hKV).measure_lt_top
  · intro φ hφ hc hts
    let φs : supportedCoreSubmodule V := ⟨φ, hφ, hc, hts⟩
    rw [integral_map measurable_subtype_coe.aemeasurable hφ.continuous.aestronglyMeasurable]
    have h1 : ∫ x, φ x.1 ∂ρ = Λt (toCcLin V φs) := by
      exact RealRMK.integral_rieszMeasure Λt (toCcLin V φs)
    rw [h1]
    change g (toCcLin V φs) = _
    rw [show g (toCcLin V φs) = f ⟨toCcLin V φs, ⟨φs, rfl⟩⟩ from hg1 ⟨toCcLin V φs, ⟨φs, rfl⟩⟩, hf]
    rfl

end CoarseDeGiorgi.Endpoint
