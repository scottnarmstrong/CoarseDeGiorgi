module

public import CoarseDeGiorgi.Whitney.Extension.Values
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.SelectionInterval
public import CoarseDeGiorgi.Whitney.Interpolation.BoundsAff

/-!
# Linearity, range, vanishing and support of the piecewise affine extension
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

/-- The constant of Lemma `l.whitney.interpolation`. -/
def C32 (d : ℕ) : ℝ := Classical.choose (whitney_interpolation (d := d))

theorem C32_nonneg (d : ℕ) : 0 ≤ C32 d := (Classical.choose_spec (whitney_interpolation (d := d))).1

theorem C32_spec {τ : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {vals : {z : Vec d // IsFreeVertex τ z} → ℝ} {g : Vec d → ℝ} (hg : IsWhitneyInterpolant τ vals g) :
    (∀ g' : Vec d → ℝ, ContinuousOn g' (closedReferenceCube (d := d) τ)ᶜ →
      (∀ cell : ExteriorCell d τ, ∃ (e : Vec d) (c : ℝ),
        ∀ x ∈ exteriorCellSet cell, g' x = vecDot e x + c) →
      (∀ z : {z : Vec d // IsFreeVertex τ z}, g' z.1 = vals z) →
      Set.EqOn g' g (closedReferenceCube (d := d) τ)ᶜ) ∧
    ∀ D : TriadicCube d, D ∈ whitneyCubes (d := d) τ →
      (∀ x ∈ closedTriadicCube D,
        ∃ z z' : {z : Vec d // IsFreeVertex τ z},
          z.1 ∈ closedTriadicCube D ∧ z'.1 ∈ closedTriadicCube D ∧
          vals z ≤ g x ∧ g x ≤ vals z') ∧
      (∀ M : ℝ,
        (∀ z z' : {z : Vec d // IsFreeVertex τ z},
          z.1 ∈ closedTriadicCube D → z'.1 ∈ closedTriadicCube D →
          |g z.1 - g z'.1| ≤ M) →
        ∀ cell : ExteriorCell d τ, cell.1.val = D →
          ∀ x ∈ exteriorCellSet cell,
            euclidNorm (smoothGrad g x) ≤ C32 d / cubeScaleFactor D * M) :=
  (Classical.choose_spec (whitney_interpolation (d := d))).2 τ hτ0 hτ1 vals g hg

theorem interp_spec (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (f : Vec d → ℝ) :
    IsWhitneyInterpolant τ (whitneyFreeValue τ h f) (whitneyAffineExtension τ h f hτ0 hτ1) :=
  (whitneyInterpolation_spec hτ0 hτ1 (whitneyFreeValue τ h f)).1

/-- The range bound of Lemma `l.whitney.interpolation` for `L_h f`. -/
theorem range_bound_ext (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (f : Vec d → ℝ)
    {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ) {x : Vec d}
    (hx : x ∈ closedTriadicCube D) :
    ∃ z z' : {z : Vec d // IsFreeVertex τ z}, z.1 ∈ closedTriadicCube D ∧
      z'.1 ∈ closedTriadicCube D ∧ whitneyFreeValue τ h f z ≤ whitneyAffineExtension τ h f hτ0 hτ1 x ∧
        whitneyAffineExtension τ h f hτ0 hτ1 x ≤ whitneyFreeValue τ h f z' :=
  ((C32_spec hτ0 hτ1 (interp_spec hτ0 hτ1 f)).2 D hD).1 x hx

theorem patchAvg_nonneg {f : Vec d → ℝ} (hτ : 0 ≤ τ) (hf : ∀ y ∈ cubeSurface τ, 0 ≤ f y) (z : Vec d) :
    0 ≤ patchAvg τ f z := by
  unfold patchAvg
  rw [average_eq]
  apply smul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply integral_nonneg_of_ae
  exact ae_restrict_of_ae ((surfaceMeasure_ae_mem τ hτ).mono fun x hx => hf x hx)

theorem freeValue_nonneg {f : Vec d → ℝ} (hτ : 0 ≤ τ) (hf : ∀ y ∈ cubeSurface τ, 0 ≤ f y)
    (z : {z : Vec d // IsFreeVertex τ z}) : 0 ≤ whitneyFreeValue τ h f z := by
  rw [whitneyFreeValue_eq]
  exact mul_nonneg (seedCutoff_nonneg _) (patchAvg_nonneg hτ hf _)

theorem freeValue_mem_Icc {f : Vec d → ℝ} (hτ : 0 ≤ τ) {m M : ℝ} (hm : m ≤ 0) (hM : 0 ≤ M)
    (hf : ∀ y ∈ cubeSurface τ, m ≤ f y ∧ f y ≤ M) (z : {z : Vec d // IsFreeVertex τ z}) :
    m ≤ whitneyFreeValue τ h f z ∧ whitneyFreeValue τ h f z ≤ M := by
  rw [whitneyFreeValue_eq]
  obtain ⟨ha1, ha2⟩ := average_mem_Icc hτ (whitneyPatch τ z.1) hm hM hf
  change m ≤ patchAvg τ f z.1 at ha1
  change patchAvg τ f z.1 ≤ M at ha2
  have h0 := seedCutoff_nonneg ((‖z.1‖ - τ / 2) / h)
  have h1 := seedCutoff_le_one ((‖z.1‖ - τ / 2) / h)
  set ω := seedCutoff ((‖z.1‖ - τ / 2) / h)
  set a := patchAvg τ f z.1
  constructor
  · rcases le_total 0 a with ha | ha
    · nlinarith [mul_nonneg h0 ha]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (neg_nonneg.mpr ha)]
  · rcases le_total 0 a with ha | ha
    · nlinarith [mul_nonneg (sub_nonneg.mpr h1) ha]
    · nlinarith [mul_nonneg h0 (neg_nonneg.mpr ha)]

/-- Range of `L_h f` between `m` and `M`. -/
theorem ext_mem_Icc (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {f : Vec d → ℝ} {m M : ℝ}
    (hm : m ≤ 0) (hM : 0 ≤ M) (hf : ∀ y ∈ cubeSurface τ, m ≤ f y ∧ f y ≤ M)
    {x : Vec d} (hx : x ∈ (closedReferenceCube (d := d) τ)ᶜ) :
    m ≤ whitneyAffineExtension τ h f hτ0 hτ1 x ∧ whitneyAffineExtension τ h f hτ0 hτ1 x ≤ M := by
  obtain ⟨D, hD, hxD⟩ := (whitney_cubes hτ0 hτ1).2.1 x hx
  obtain ⟨z, z', _, _, h1, h2⟩ := range_bound_ext (h := h) hτ0 hτ1 f hD hxD
  have hτ : 0 ≤ τ := by linarith only [hτ0]
  exact ⟨(freeValue_mem_Icc hτ hm hM hf z).1.trans h1, h2.trans (freeValue_mem_Icc hτ hm hM hf z').2⟩

theorem ext_nonneg (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {f : Vec d → ℝ}
    (hf : ∀ y ∈ cubeSurface τ, 0 ≤ f y) {x : Vec d} (hx : x ∈ (closedReferenceCube (d := d) τ)ᶜ) :
    0 ≤ whitneyAffineExtension τ h f hτ0 hτ1 x := by
  obtain ⟨D, hD, hxD⟩ := (whitney_cubes hτ0 hτ1).2.1 x hx
  obtain ⟨z, z', _, _, h1, h2⟩ := range_bound_ext (h := h) hτ0 hτ1 f hD hxD
  exact (freeValue_nonneg (by linarith only [hτ0]) hf z).trans h1

/-- Vanishing on cubes that are not near. -/
theorem ext_eq_zero_of_far (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (hh : 0 < h) (f : Vec d → ℝ)
    {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ)
    (hfar : h ≤ infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ))
    {x : Vec d} (hx : x ∈ closedTriadicCube D) :
    whitneyAffineExtension τ h f hτ0 hτ1 x = 0 := by
  obtain ⟨z, z', hz, hz', h1, h2⟩ := range_bound_ext (h := h) hτ0 hτ1 f hD hx
  have hv : ∀ w : {z : Vec d // IsFreeVertex τ z}, w.1 ∈ closedTriadicCube D →
      whitneyFreeValue τ h f w = 0 := by
    intro w hw
    rw [whitneyFreeValue_eq, seedCutoff_eq_zero, zero_mul]
    have := far_gap hτ0 hτ1 hD hfar w.1 hw
    rw [le_div_iff₀ hh]; linarith only [this]
  rw [hv z hz] at h1
  rw [hv z' hz'] at h2
  exact le_antisymm h2 h1

theorem closedRef_isClosed (τ : ℝ) : IsClosed (closedReferenceCube (d := d) τ) :=
  CoarseDeGiorgi.WhitneyInterp.isClosed_closedReferenceCube

/-- Near cubes lie in `(τ+3h)□̄₀`. -/
theorem cube_subset_closedRef_of_near (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ)
    (hnear : infSupDist (closedTriadicCube D) (closedReferenceCube (d := d) τ) < h) :
    closedTriadicCube D ⊆ closedReferenceCube (d := d) (τ + 3 * h) := by
  intro x hx i
  have h1 := (near_gap hτ0 hτ1 hD hnear).2 x hx
  have h2 : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  linarith only [h1, h2]

theorem closedRef_subset_originCube {ρ₂ : ℝ} (hlt : τ + 3 * h < ρ₂) :
    closedReferenceCube (d := d) (τ + 3 * h) ⊆ originCube (d := d) ρ₂ := by
  intro x hx i
  have := hx i
  rw [abs_le] at this
  constructor <;> linarith [this.1, this.2]

end

end CoarseDeGiorgi.WhitneyExt
