import CoarseDeGiorgi.Whitney.Harmonic.Conseq2Wide

/-! The trace identity of Proposition `p.whitney.extension`. -/

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

/-- The ordinary trace of `H_h f` on `∂(τ□₀)` is `f` (Gauss-Green identity). -/
theorem trace_statement (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    {a : CoeffField d} (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {f : Vec d → ℝ} (hfacts : AffFacts τ h ρ₂ hτ0 hτ1 f)
    (hf : ∃ K : ℝ≥0, LipschitzOnWith K f (CoarseDeGiorgi.cubeSurface (d := d) τ))
    {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH)
    (i : Fin d) (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ CoarseDeGiorgi.originCube (d := d) 1) :
    ∫ x in CoarseDeGiorgi.originCube (d := d) 1 \ CoarseDeGiorgi.closedReferenceCube (d := d) τ,
        (H x * fderiv ℝ φ x (basisVec i) + GH x i * φ x) =
      (∫ x, f x * φ x ∂(CoarseDeGiorgi.cubeFaceMeasure τ i false)) -
        ∫ x, f x * φ x ∂(CoarseDeGiorgi.cubeFaceMeasure τ i true) := by
  have : NeZero d := ⟨by omega⟩
  have hτpos : 0 < τ := by linarith
  obtain ⟨w, K₂, hw, hwf⟩ := exists_lipschitz_extension hf
  obtain ⟨Φ, K, ξ, Gξ, hΦ, hΦB, hξ, hψ, hH, hB⟩ :=
    glued_correction hd hτ0 hτ1 hρ₂ hτρ hh hwidth ha hfacts hHGH
      (hw.lipschitzOnWith) hwf
  have hOd : IsOpenBoundedConvexDomain (CoarseDeGiorgi.originCube (d := d) 1) :=
    Whitney.source_cube_domain (by norm_num)
  have hOne : (CoarseDeGiorgi.originCube (d := d) 1).Nonempty :=
    Whitney.source_cube_nonempty (by norm_num)
  have hBc := isClosed_closedRef (d := d) hτpos.le
  have hBO := closedRef_subset_unit (d := d) hτ1
  have hSsub : CoarseDeGiorgi.originCube (d := d) 1 \ CoarseDeGiorgi.closedReferenceCube (d := d) τ ⊆
      CoarseDeGiorgi.originCube (d := d) 1 := sdiff_subset
  obtain ⟨hξi, hξGi, hξweak, -, -⟩ := Weighted.memH1a_memW11 hOd hOne ha
    (Weighted.MemH1a0.memH1a ha hξ)
  have hdφ : Continuous (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := hdφ.bounded_above_of_compact_support (hc.fderiv_apply (𝕜 := ℝ) (basisVec i))
  obtain ⟨C', hC'⟩ := hφ.continuous.bounded_above_of_compact_support hc
  have hQ1 : Integrable (fun x => ξ x * fderiv ℝ φ x (basisVec i))
      (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)) :=
    hξi.mul_bdd hdφ.aestronglyMeasurable (c := C) (Filter.Eventually.of_forall hC)
  have hQ2 : Integrable (fun x => Gξ x i * φ x)
      (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)) :=
    (hξGi i).mul_bdd hφ.continuous.aestronglyMeasurable (c := C') (Filter.Eventually.of_forall hC')
  have hP := integrable_gaussGreen_integrand hΦ hφ hc i
  have hQ : Integrable (fun x => ξ x * fderiv ℝ φ x (basisVec i) + Gξ x i * φ x)
      (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)) := hQ1.add hQ2
  -- the correction integrates to zero
  have hQO : ∫ x in CoarseDeGiorgi.originCube (d := d) 1,
      (ξ x * fderiv ℝ φ x (basisVec i) + Gξ x i * φ x) = 0 := by
    rw [integral_add hQ1 hQ2, hξweak i φ hφ hc hs]
    ring
  have hQB : ∫ x in CoarseDeGiorgi.closedReferenceCube (d := d) τ,
      (ξ x * fderiv ℝ φ x (basisVec i) + Gξ x i * φ x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hB] with x hx
    simp [hx.1, hx.2]
  have hQS : ∫ x in CoarseDeGiorgi.originCube (d := d) 1 \
      CoarseDeGiorgi.closedReferenceCube (d := d) τ,
      (ξ x * fderiv ℝ φ x (basisVec i) + Gξ x i * φ x) = 0 := by
    rw [setIntegral_sdiff hBc.measurableSet hQ hBO, hQO, hQB]; ring
  have hGG := lipschitz_exterior_gauss_green (by omega) hτpos hτ1 hΦ i φ hφ hc hs
  have hcongr : ∫ x in CoarseDeGiorgi.originCube (d := d) 1 \
        CoarseDeGiorgi.closedReferenceCube (d := d) τ,
        (H x * fderiv ℝ φ x (basisVec i) + GH x i * φ x) =
      ∫ x in CoarseDeGiorgi.originCube (d := d) 1 \ CoarseDeGiorgi.closedReferenceCube (d := d) τ,
        ((Φ x * fderiv ℝ φ x (basisVec i) + fderiv ℝ Φ x (basisVec i) * φ x) +
          (ξ x * fderiv ℝ φ x (basisVec i) + Gξ x i * φ x)) := by
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    rw [hx.1]
    have : GH x i = fderiv ℝ Φ x (basisVec i) + Gξ x i := by
      rw [hx.2]; rfl
    rw [this]; ring
  rw [hcongr, integral_add hP.integrableOn (IntegrableOn.mono_set hQ hSsub), hQS,
    add_zero, hGG]
  -- faces
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hface (b : Bool) : ∫ x, Φ x * φ x ∂(CoarseDeGiorgi.cubeFaceMeasure τ i b) =
      ∫ x, f x * φ x ∂(CoarseDeGiorgi.cubeFaceMeasure τ i b) := by
    apply integral_congr_ae
    filter_upwards [ae_cubeFace_mem_surface τ hτpos.le i b] with x hx
    rw [hΦB x (surface_subset_closedRef hτpos hx), hwf x hx]
  rw [hface false, hface true]

end CoarseDeGiorgi.Whitney.Harmonic.Wide
