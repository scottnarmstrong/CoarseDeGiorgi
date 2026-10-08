module

public import CoarseDeGiorgi.GoodRadius.Hypothesis
public import CoarseDeGiorgi.GoodRadius.OpenCover
public import CoarseDeGiorgi.GoodRadius.SummableSlicing
public import CoarseDeGiorgi.Assembly.HybridFractional
public import CoarseDeGiorgi.Selection.SurfaceMeasurability
public import CoarseDeGiorgi.Statements.SmoothGrad
public import CoarseDeGiorgi.Statements.IsSmoothCore

/-!
# Step 1 of Proposition `p.good.radius`: traces for almost every radius

From the localization clauses (cover, fractional bound, convergence for sequences) we get
measurable representatives, and one subsequence along which, for almost every radius `τ`, the
series of `r`-th powers of the surface fractional norms of `vᵢ - v` converges.
-/

@[expose] public section

namespace CoarseDeGiorgi.GoodRadius

open Homogenization MeasureTheory Set Filter CoarseDeGiorgi.Selection
open scoped BigOperators ENNReal Topology

noncomputable section

/-- The relevant clauses of the localization of Proposition `p.fractional.localization`, at fixed
data and one cover `(S, φ)`: representation on a neighborhood of each selected surface, the bound,
and the convergence for sequences. -/
def LocalizationClause {d : ℕ} (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (q t : ℝ) (hq : 1 < q) (ht : 0 < t)
    (S : Finset (ℤ × (Fin d → ℤ))) (φ : ℤ × (Fin d → ℤ) → Vec d → ℝ)
    (ρ₁ ρ₂ : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
    MemH1a a (originCube 1) v G →
    (∀ τ ∈ selectionInterval ρ₁ ρ₂,
      ∃ U : Set (Vec d), IsOpen U ∧ cubeSurface τ ⊆ U ∧
        ∀ᵐ x ∂(volume.restrict U),
          ∑ i ∈ S, φ i x * v x = v x) ∧
    fracNorm Set.univ (alphaParam t) (paramR q)
        (fun x => ∑ i ∈ S, φ i x * v x) ≤
      C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-alphaParam t) *
        ((lowerMoment a ha t q ht (le_of_lt hq)).rpow (-(1 / 2)) *
            (weightedEnergy a (originCube ρ₂) G).rpow (1 / 2) +
          eLpNorm v (ENNReal.ofReal (paramR q))
            (volume.restrict (originCube ρ₂))) ∧
    ∀ (vⱼ : ℕ → Vec d → ℝ) (Gⱼ : ℕ → Vec d → Vec d),
      (∀ j, MemH1a a (originCube 1) (vⱼ j) (Gⱼ j)) →
      Filter.Tendsto
        (fun j => h1aWeightedNorm a (originCube 1)
          (fun x => vⱼ j x - v x) (fun x => Gⱼ j x - G x))
        Filter.atTop (nhds 0) →
      Filter.Tendsto
        (fun j => fracNorm Set.univ (alphaParam t) (paramR q)
          (fun x => (∑ i ∈ S, φ i x * vⱼ j x) - ∑ i ∈ S, φ i x * v x))
        Filter.atTop (nhds 0)

theorem h1aWeightedNorm_congr_ae {d : ℕ} (a : CoeffField d) (Q : Set (Vec d))
    {w w' : Vec d → ℝ} (G : Vec d → Vec d) (h : w =ᵐ[volume.restrict Q] w') :
    h1aWeightedNorm a Q w G = h1aWeightedNorm a Q w' G := by
  unfold h1aWeightedNorm volumeAverage
  rw [integral_congr_ae h]

theorem measurable_localized_sum {d : ℕ} {S : Finset (ℤ × (Fin d → ℤ))}
    {φ : ℤ × (Fin d → ℤ) → Vec d → ℝ} (hφ : ∀ i ∈ S, ContDiff ℝ (⊤ : ℕ∞) (φ i))
    {w : Vec d → ℝ} (hw : Measurable w) :
    Measurable (fun x => ∑ i ∈ S, φ i x * w x) :=
  Finset.measurable_sum _ fun i hi => ((hφ i hi).continuous.measurable).mul hw

theorem trace_data {n : ℕ} (hd : 3 ≤ n + 1) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta (n + 1) p q s t)
    (a : CoeffField (n + 1)) (ha : IsWeightedCoeffOn (originCube 1) a)
    {ρ₁ ρ₂ : ℝ} (hρ : 1 / 2 ≤ ρ₁) (hgap : ρ₁ < ρ₂) (hR : ρ₂ ≤ 1)
    {S : Finset (ℤ × (Fin (n + 1) → ℤ))}
    {φ : ℤ × (Fin (n + 1) → ℤ) → Vec (n + 1) → ℝ}
    (hφ : ∀ i ∈ S, ContDiff ℝ (⊤ : ℕ∞) (φ i)) {Cl : ℝ≥0∞}
    (hL : LocalizationClause a ha q t hq ht S φ ρ₁ ρ₂ Cl)
    (v : Vec (n + 1) → ℝ) (G : Vec (n + 1) → Vec (n + 1))
    (hv : MemH1a a (originCube 1) v G)
    (vi : ℕ → Vec (n + 1) → ℝ) (hvi : ∀ i, IsSmoothCore a (originCube 1) (vi i))
    (hnorm : Tendsto (fun i => h1aWeightedNorm a (originCube 1)
        (fun x => vi i x - v x) (fun x => smoothGrad (vi i) x - G x)) atTop (𝓝 0)) :
    ∃ w₀ : Vec (n + 1) → ℝ, ∃ W : ℕ → Vec (n + 1) → ℝ,
      Measurable w₀ ∧ (∀ i, Measurable (W i)) ∧
      w₀ =ᵐ[volume.restrict (originCube 1)] v ∧
      (∀ i, W i =ᵐ[volume.restrict (originCube 1)] vi i) ∧
      fracNorm univ (alphaParam t) (paramR q) (fun x => ∑ i ∈ S, φ i x * w₀ x) ≤
        Cl * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-alphaParam t) *
          ((lowerMoment a ha t q ht hq.le).rpow (-(1 / 2)) *
            (weightedEnergy a (originCube ρ₂) G).rpow (1 / 2) +
          eLpNorm v (ENNReal.ofReal (paramR q)) (volume.restrict (originCube ρ₂))) ∧
      (∀ᵐ τ ∂volume.restrict (selectionInterval ρ₁ ρ₂),
        (fun x => ∑ i ∈ S, φ i x * w₀ x) =ᵐ[surfaceMeasure τ] w₀ ∧
        w₀ =ᵐ[surfaceMeasure τ] v ∧ ∀ i, W i =ᵐ[surfaceMeasure τ] vi i) ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ τ ∂volume.restrict (selectionInterval ρ₁ ρ₂),
        (∑' i, surfaceFracNorm τ (alphaParam t) (paramR q)
          (fun x => W (ns i) x - w₀ x) ^ paramR q ≠ ⊤) ∧
        Tendsto (fun i => eLpNorm (fun x => W (ns i) x - w₀ x) 2 (surfaceMeasure τ))
          atTop (𝓝 0) := by
  have : NeZero (n + 1) := ⟨by omega⟩
  obtain ⟨hα, hα1, hr, _, hc, _, h2, _⟩ :=
    Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  have hunit := Assembly.hybrid_unitCube_domain (d := n + 1)
  have hmem (i : ℕ) : MemH1a a (originCube 1) (vi i) (smoothGrad (vi i)) :=
    Weighted.memH1a_of_isSmoothCore hunit.1.isOpen ha (hvi i)
  let w₀ := hv.1.mk v
  let W := fun i => (hmem i).1.mk (vi i)
  have hw₀ : Measurable w₀ := hv.1.measurable_mk
  have hW (i : ℕ) : Measurable (W i) := (hmem i).1.measurable_mk
  have hew : v =ᵐ[volume.restrict (originCube 1)] w₀ := hv.1.ae_eq_mk
  have heW (i : ℕ) : vi i =ᵐ[volume.restrict (originCube 1)] W i := (hmem i).1.ae_eq_mk
  have hmemw₀ : MemH1a a (originCube 1) w₀ G :=
    Weighted.MemH1a.congr_ae hv hew EventuallyEq.rfl
  have hmemW (i : ℕ) : MemH1a a (originCube 1) (W i) (smoothGrad (vi i)) :=
    Weighted.MemH1a.congr_ae (hmem i) (heW i) EventuallyEq.rfl
  have hnorm' : Tendsto (fun i => h1aWeightedNorm a (originCube 1)
      (fun x => W i x - w₀ x) (fun x => smoothGrad (vi i) x - G x)) atTop (𝓝 0) := by
    refine hnorm.congr fun i => ?_
    exact h1aWeightedNorm_congr_ae a _ _ ((heW i).sub hew)
  obtain ⟨hcov, hbd, hconvfun⟩ := hL w₀ G hmemw₀
  have hconv := hconvfun W (fun i => smoothGrad (vi i)) hmemW hnorm'
  have hρ0 : 0 ≤ ρ₁ := by linarith only [hρ]
  have hJ : selectionInterval ρ₁ ρ₂ ⊆ Ioo (1 / 2 : ℝ) 1 := by
    intro τ hτ
    have hh := selectionInterval_subset hgap hτ
    exact ⟨lt_of_le_of_lt hρ hh.1, lt_of_lt_of_le hh.2 hR⟩
  have hAnn : cubicalAnnulus (n + 1) ρ₁ ρ₂ ⊆ originCube (d := n + 1) 1 := by
    intro x hx i
    have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact abs_lt.mp (by linarith only [hi, hx.2, hR])
  have hFsurf : ∀ᵐ τ ∂volume.restrict (selectionInterval ρ₁ ρ₂),
      (fun x => ∑ i ∈ S, φ i x * w₀ x) =ᵐ[surfaceMeasure τ] w₀ :=
    surface_ae_eq_of_local_cover hρ0 measurableSet_Ioo (selectionInterval_subset hgap) hcov
  have hFi : ∀ i, ∀ᵐ τ ∂volume.restrict (selectionInterval ρ₁ ρ₂),
      (fun x => ∑ j ∈ S, φ j x * W i x) =ᵐ[surfaceMeasure τ] W i := fun i =>
    surface_ae_eq_of_local_cover hρ0 measurableSet_Ioo (selectionInterval_subset hgap)
      (hL (W i) (smoothGrad (vi i)) (hmemW i)).1
  have hwv : ∀ᵐ τ ∂volume.restrict (selectionInterval ρ₁ ρ₂), w₀ =ᵐ[surfaceMeasure τ] v := by
    have := source_surface_ae_of_annulus_ae (n := n) (ρ := ρ₁) (R := ρ₂) hρ0
      (ae_restrict_of_ae_restrict_of_subset hAnn hew.symm)
    exact ae_restrict_of_ae_restrict_of_subset (selectionInterval_subset hgap) this
  have hWv : ∀ i, ∀ᵐ τ ∂volume.restrict (selectionInterval ρ₁ ρ₂),
      W i =ᵐ[surfaceMeasure τ] vi i := fun i => by
    have := source_surface_ae_of_annulus_ae (n := n) (ρ := ρ₁) (R := ρ₂) hρ0
      (ae_restrict_of_ae_restrict_of_subset hAnn (heW i).symm)
    exact ae_restrict_of_ae_restrict_of_subset (selectionInterval_subset hgap) this
  let Gs : ℕ → Vec (n + 1) → ℝ := fun i x =>
    (∑ j ∈ S, φ j x * W i x) - ∑ j ∈ S, φ j x * w₀ x
  have hGs (i : ℕ) : Measurable (Gs i) :=
    (measurable_localized_sum hφ (hW i)).sub (measurable_localized_sum hφ hw₀)
  obtain ⟨ns, hns, hsl⟩ := summable_surface_subsequence hα hα1 hr hc h2.le
    measurableSet_Ioo hJ Gs hGs hconv
  have heLp : eLpNorm v (ENNReal.ofReal (paramR q)) (volume.restrict (originCube ρ₂)) =
      eLpNorm w₀ (ENNReal.ofReal (paramR q)) (volume.restrict (originCube ρ₂)) :=
    eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset
      (Assembly.caccioppoli_cube_mono hR) hew)
  refine ⟨w₀, W, hw₀, hW, hew.symm, fun i => (heW i).symm, ?_, ?_, ns, hns, ?_⟩
  · rw [heLp]; exact hbd
  · filter_upwards [hFsurf, hwv, ae_all_iff.mpr hWv] with τ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · filter_upwards [hsl, hFsurf, ae_all_iff.mpr hFi] with τ hτ hF hFis
    have hcongr (i : ℕ) : Gs (ns i) =ᵐ[surfaceMeasure τ] (fun x => W (ns i) x - w₀ x) :=
      (hFis (ns i)).sub hF
    refine ⟨?_, ?_⟩
    · simpa only [surfaceFracNorm_congr_ae (hcongr _)] using hτ.1
    · simpa only [eLpNorm_congr_ae (hcongr _)] using hτ.2

end

end CoarseDeGiorgi.GoodRadius
