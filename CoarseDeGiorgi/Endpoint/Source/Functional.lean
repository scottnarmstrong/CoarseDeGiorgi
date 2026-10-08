import CoarseDeGiorgi.Weighted.Testing
import CoarseDeGiorgi.Weighted.TestingCompactSupport
import CoarseDeGiorgi.Weighted.Truncation.PositivePart
import CoarseDeGiorgi.Statements.IsWeightedSupersolution

/-! The flux functional `φ ↦ ∫ ∇φ·a∇u` of a supersolution on smooth compactly supported tests. -/

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted
open scoped Manifold

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- A smooth cutoff with values in `[0,1]`, equal to one on a compact subset of an open set. -/
theorem exists_cutoff01 (hV : IsOpen V) {K : Set (Vec d)} (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ V ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ ∀ x ∈ K, φ x = 1 := by
  obtain ⟨W, hWc, hWclosed, hKW, hWV⟩ := exists_compact_closed_between hK hV hKV
  obtain ⟨φ, hφone, hφzero, hφI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, Vec d)) (n := (⊤ : ℕ∞)) hK.isClosed hKW
  have hsupport : Function.support φ ⊆ W := by
    intro x hx
    by_contra hxW
    exact hx (hφzero x hxW)
  refine ⟨φ, contMDiff_iff_contDiff.mp φ.contMDiff,
    HasCompactSupport.of_support_subset_isCompact hWc hsupport,
    (closure_minimal hsupport hWclosed).trans hWV, fun x => hφI x, ?_⟩
  intro x hx
  exact (hφone.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds

theorem smoothGrad_add_all {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : smoothGrad (f + g) = smoothGrad f + smoothGrad g := by
  funext x i
  simp only [smoothGrad, Pi.add_apply]
  rw [fderiv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

theorem smoothGrad_smul_all (c : ℝ) {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    smoothGrad (c • f) = c • smoothGrad f := by
  funext x i
  simp only [smoothGrad, Pi.smul_apply]
  rw [fderiv_const_smul (hf.differentiable (by simp) x)]
  rfl

/-- The flux pairing of a test function with a gradient field. -/
noncomputable def fluxPairing (a : CoeffField d) (V : Set (Vec d)) (G : Vec d → Vec d)
    (φ : Vec d → ℝ) : ℝ :=
  ∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) (G x))

theorem fluxPairing_integrable (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V))
    (hEG : weightedEnergy a V G < ⊤) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (_hs : tsupport φ ⊆ V) :
    IntegrableOn (fun x => vecDot (smoothGrad φ x) (matVecMul (a x) (G x))) V :=
  (pairing_integrable_and_bound ha (smoothGrad_aestronglyMeasurable hV hφ.contDiffOn) hG
    (isSmoothCore_of_supported ha hφ hc).2.2 hEG).1

theorem fluxPairing_bound (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V))
    (hEG : weightedEnergy a V G < ⊤) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (_hs : tsupport φ ⊆ V) :
    |fluxPairing a V G φ| ≤ Real.sqrt (weightedEnergy a V (smoothGrad φ)).toReal *
      Real.sqrt (weightedEnergy a V G).toReal :=
  (pairing_integrable_and_bound ha (smoothGrad_aestronglyMeasurable hV hφ.contDiffOn) hG
    (isSmoothCore_of_supported ha hφ hc).2.2 hEG).2

theorem fluxPairing_add (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V))
    (hEG : weightedEnergy a V G < ⊤) {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ V) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ V) :
    fluxPairing a V G (f + g) = fluxPairing a V G f + fluxPairing a V G g := by
  unfold fluxPairing
  rw [smoothGrad_add_all hf hg, ← integral_add (fluxPairing_integrable hV ha hG hEG hf hfc hfs)
    (fluxPairing_integrable hV ha hG hEG hg hgc hgs)]
  congr 1
  funext x
  simp [vecDot_add_left]

theorem fluxPairing_smul (c : ℝ) {G : Vec d → Vec d} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    fluxPairing a V G (c • f) = c * fluxPairing a V G f := by
  unfold fluxPairing
  rw [smoothGrad_smul_all c hf, ← integral_const_mul]
  congr 1
  funext x
  simp [vecDot_smul_left]

/-- Supersolutions have a nonnegative flux pairing on nonnegative tests. -/
theorem fluxPairing_nonneg {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hs : CoarseDeGiorgi.IsWeightedSupersolution a V u G) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hts : tsupport φ ⊆ V)
    (hnn : ∀ x, 0 ≤ φ x) : 0 ≤ fluxPairing a V G φ := by
  have h := (hs.2 φ hφ hc hts hnn).2
  unfold fluxPairing
  have : (∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) (-G x))) =
      -∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) := by
    rw [← integral_neg]
    congr 1
    funext x
    simp [matVecMul_neg, vecDot_neg_right]
  rw [this] at h
  linarith

end CoarseDeGiorgi.Endpoint
