module

public import CoarseDeGiorgi.Whitney.Harmonic.GaussGreenLine
public import CoarseDeGiorgi.Selection.Coarea
public import CoarseDeGiorgi.Statements.ClosedReferenceCube
public import CoarseDeGiorgi.Statements.OriginCube

/-! # Gauss-Green on the exterior of a closed cube

For a Lipschitz function `Φ` and a smooth test function `φ` supported in `□₀`, the integral of
`∂ᵢ(Φ φ)` over `□₀ ∖ τ□̄₀` equals the difference of the integrals of `Φ φ` over the two faces of
`τ□̄₀` orthogonal to `eᵢ`.  The proof splits off the coordinate `i` by Fubini and applies the
fundamental theorem of calculus for absolutely continuous functions on each line.
-/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CoarseDeGiorgi.Whitney.Harmonic

noncomputable section

/-- The integrand `∂ᵢ(Φ φ)` is integrable. -/
theorem integrable_gaussGreen_integrand {d : ℕ} {K : ℝ≥0} {Φ φ : Vec d → ℝ}
    (hΦ : LipschitzWith K Φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (i : Fin d) :
    Integrable (fun x => Φ x * fderiv ℝ φ x (basisVec i) + fderiv ℝ Φ x (basisVec i) * φ x) := by
  have hdφ : Continuous (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  refine Integrable.add ?_ ?_
  · exact (hΦ.continuous.mul hdφ).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) (basisVec i)).mul_left
  · refine (hφ.continuous.integrable_of_hasCompactSupport hc).bdd_mul
      (c := K * ‖basisVec i‖) (measurable_fderiv_apply_const ℝ Φ _).aestronglyMeasurable ?_
    filter_upwards with x
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hΦ) (norm_nonneg _))

variable {n : ℕ}

/-- On almost every line in the direction `eᵢ`, the integral of `∂ᵢ(Φ φ)` is the difference of
the endpoint values of `Φ φ`. -/
theorem ae_integral_insertNth_eq_sub {K : ℝ≥0} {Φ φ : Vec (n + 1) → ℝ}
    (hΦ : LipschitzWith K Φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (i : Fin (n + 1)) :
    ∀ᵐ u : Vec n, ∀ a b : ℝ,
      ∫ t in a..b, (Φ (i.insertNth (α := fun _ => ℝ) t u) *
          fderiv ℝ φ (i.insertNth (α := fun _ => ℝ) t u) (basisVec i) +
        fderiv ℝ Φ (i.insertNth (α := fun _ => ℝ) t u) (basisVec i) *
          φ (i.insertNth (α := fun _ => ℝ) t u)) =
        Φ (i.insertNth (α := fun _ => ℝ) b u) * φ (i.insertNth (α := fun _ => ℝ) b u) -
          Φ (i.insertNth (α := fun _ => ℝ) a u) * φ (i.insertNth (α := fun _ => ℝ) a u) := by
  obtain ⟨L, hφL⟩ := hφ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  filter_upwards [ae_ae_differentiableAt_insertNth hΦ i] with u hu a b
  have hins : ∀ t : ℝ, (i.insertNth (α := fun _ => ℝ) t u : Vec (n + 1)) =
      i.insertNth (α := fun _ => ℝ) 0 u + t • basisVec i :=
    fun t => insertNth_eq_add_smul_basisVec i t u
  have hdiff : ∀ᵐ t : ℝ, DifferentiableAt ℝ Φ
      (i.insertNth (α := fun _ => ℝ) 0 u + t • basisVec i) := by
    filter_upwards [hu] with t ht
    rwa [← hins t]
  have h := integral_line_lipschitz_mul_eq_sub hΦ hφL hφd
    (i.insertNth (α := fun _ => ℝ) 0 u) (basisVec i) a b hdiff
  simp only [← hins] at h
  exact h

/-- Whole-space integration by parts: `∫ ∂ᵢ(Φ φ) = 0`. -/
theorem integral_gaussGreen_integrand_eq_zero {K : ℝ≥0} {Φ φ : Vec (n + 1) → ℝ}
    (hΦ : LipschitzWith K Φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ CoarseDeGiorgi.originCube (d := n + 1) 1) (i : Fin (n + 1)) :
    ∫ x, (Φ x * fderiv ℝ φ x (basisVec i) + fderiv ℝ Φ x (basisVec i) * φ x) = 0 := by
  have hout : ∀ x, x ∉ CoarseDeGiorgi.originCube (d := n + 1) 1 →
      φ x = 0 ∧ fderiv ℝ φ x (basisVec i) = 0 := fun x hx =>
    ⟨image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)),
      image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (basisVec i))
        (fun h => hx (hs (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := φ) (basisVec i) h)))⟩
  have hmem : ∀ (u : Vec n) (t : ℝ), ¬(-(1 / 2 : ℝ) < t ∧ t < 1 / 2) →
      i.insertNth (α := fun _ => ℝ) t u ∉ CoarseDeGiorgi.originCube (d := n + 1) 1 := by
    intro u t ht hx
    have hi := hx i
    rw [Fin.insertNth_apply_same] at hi
    exact ht hi
  have hmem' : ∀ (u : Vec n) (t : ℝ), t ∉ Ioc (-1 : ℝ) 1 →
      i.insertNth (α := fun _ => ℝ) t u ∉ CoarseDeGiorgi.originCube (d := n + 1) 1 :=
    fun u t ht => hmem u t fun h => ht ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [integral_eq_integral_insertNth (integrable_gaussGreen_integrand hΦ hφ hc i) i]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_integral_insertNth_eq_sub hΦ hφ hc i] with u hu
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (-1 : ℝ) 1) (fun t ht => by
      obtain ⟨h1, h2⟩ := hout _ (hmem' u t ht)
      simp [h1, h2]),
    ← intervalIntegral.integral_of_le (by norm_num), hu (-1) 1,
    (hout _ (hmem u 1 (by norm_num))).1, (hout _ (hmem u (-1) (by norm_num))).1]
  simp

/-- Gauss-Green on the closed cube `τ□̄₀`, with the faces written in the coordinates `u` of the
free variables. -/
theorem setIntegral_closedReferenceCube_gaussGreen {K : ℝ≥0} {Φ φ : Vec (n + 1) → ℝ}
    (hΦ : LipschitzWith K Φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    {τ : ℝ} (hτ : 0 ≤ τ) (i : Fin (n + 1)) :
    ∫ x in CoarseDeGiorgi.closedReferenceCube (d := n + 1) τ,
        (Φ x * fderiv ℝ φ x (basisVec i) + fderiv ℝ Φ x (basisVec i) * φ x) =
      (∫ u in Selection.faceBox n τ, Φ (i.insertNth (α := fun _ => ℝ) (τ / 2) u) *
          φ (i.insertNth (α := fun _ => ℝ) (τ / 2) u)) -
        ∫ u in Selection.faceBox n τ, Φ (i.insertNth (α := fun _ => ℝ) (-τ / 2) u) *
          φ (i.insertNth (α := fun _ => ℝ) (-τ / 2) u) := by
  set F : Vec (n + 1) → ℝ :=
    fun x => Φ x * fderiv ℝ φ x (basisVec i) + fderiv ℝ Φ x (basisVec i) * φ x with hF
  set B := CoarseDeGiorgi.closedReferenceCube (d := n + 1) τ with hB
  set Q : Set (Vec n) := Set.pi univ (fun _ => Icc (-τ / 2) (τ / 2)) with hQ
  have hBm : MeasurableSet B := by
    have : B = ⋂ j, {x : Vec (n + 1) | |x j| ≤ τ / 2} := by
      ext x
      simp [hB, CoarseDeGiorgi.closedReferenceCube]
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) measurable_const
  have hQm : MeasurableSet Q := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hFi : Integrable F := integrable_gaussGreen_integrand hΦ hφ hc i
  have hmemB : ∀ (t : ℝ) (u : Vec n), i.insertNth (α := fun _ => ℝ) t u ∈ B ↔
      t ∈ Icc (-τ / 2) (τ / 2) ∧ u ∈ Q := by
    intro t u
    simp only [hB, hQ, CoarseDeGiorgi.closedReferenceCube, mem_ofPred_eq,
      Fin.forall_iff_succAbove i, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
      mem_univ_pi, mem_Icc, abs_le, neg_div]
  have hslice : ∀ u : Vec n, ∫ t, B.indicator F (i.insertNth (α := fun _ => ℝ) t u) =
      Q.indicator (fun u => ∫ t in (-τ / 2)..(τ / 2),
        F (i.insertNth (α := fun _ => ℝ) t u)) u := by
    intro u
    by_cases hu : u ∈ Q
    · rw [indicator_of_mem hu, intervalIntegral.integral_of_le (by linarith),
        ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
      congr 1
      funext t
      by_cases ht : t ∈ Icc (-τ / 2) (τ / 2)
      · rw [indicator_of_mem ((hmemB t u).2 ⟨ht, hu⟩), indicator_of_mem ht]
      · rw [indicator_of_notMem (fun h => ht ((hmemB t u).1 h).1),
          indicator_of_notMem ht]
    · rw [indicator_of_notMem hu]
      have h0 : ∀ t : ℝ, B.indicator F (i.insertNth (α := fun _ => ℝ) t u) = 0 :=
        fun t => indicator_of_notMem (fun h => hu ((hmemB t u).1 h).2) _
      simp [h0]
  have hfaceQ : Selection.faceBox n τ =ᵐ[volume] Q :=
    Measure.pi_Ioo_ae_eq_pi_Icc (μ := fun _ : Fin n => (volume : Measure ℝ))
  have hcont : ∀ c : ℝ, Continuous fun u : Vec n =>
      Φ (i.insertNth (α := fun _ => ℝ) c u) * φ (i.insertNth (α := fun _ => ℝ) c u) := by
    intro c
    have hins : Continuous fun u : Vec n => (i.insertNth (α := fun _ => ℝ) c u : Vec (n + 1)) :=
      Continuous.finInsertNth i continuous_const continuous_id
    exact (hΦ.continuous.comp hins).mul (hφ.continuous.comp hins)
  have hint : ∀ c : ℝ, IntegrableOn (fun u : Vec n =>
      Φ (i.insertNth (α := fun _ => ℝ) c u) * φ (i.insertNth (α := fun _ => ℝ) c u))
      (Selection.faceBox n τ) := by
    intro c
    refine ((hcont c).integrableOn_Icc (a := fun _ => -τ / 2) (b := fun _ => τ / 2)).mono_set ?_
    rw [← pi_univ_Icc]
    exact pi_mono fun _ _ => Ioo_subset_Icc_self
  rw [← integral_indicator hBm, integral_eq_integral_insertNth (hFi.indicator hBm) i]
  simp_rw [hslice]
  rw [integral_indicator hQm, ← setIntegral_congr_set hfaceQ, ← integral_sub (hint _) (hint _)]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_integral_insertNth_eq_sub hΦ hφ hc i] with u hu
  exact hu _ _

/-- Integration against the face measure in the coordinates of the free variables. -/
theorem integral_cubeFaceMeasure_eq_faceBox {P : Vec (n + 1) → ℝ} (hP : Continuous P)
    (τ : ℝ) (i : Fin (n + 1)) (pos : Bool) :
    ∫ x, P x ∂(CoarseDeGiorgi.cubeFaceMeasure τ i pos) =
      ∫ u in Selection.faceBox n τ,
        P (i.insertNth (α := fun _ => ℝ) (if pos then τ / 2 else -τ / 2) u) := by
  rw [Selection.cubeFaceMeasure_eq_map, integral_map]
  · exact (Continuous.finInsertNth i continuous_const continuous_id).aemeasurable
  · exact hP.aestronglyMeasurable

/-- **Gauss-Green on `□₀ ∖ τ□̄₀`** for a Lipschitz function and a smooth test function supported
in `□₀`: the boundary terms are the integrals over the two faces of `τ□̄₀` orthogonal to `eᵢ`,
with the outward normal of the exterior domain. -/
theorem lipschitz_exterior_gauss_green {d : ℕ} (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    {K : ℝ≥0} {Φ : Vec d → ℝ} (hΦ : LipschitzWith K Φ)
    (i : Fin d) (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ CoarseDeGiorgi.originCube (d := d) 1) :
    ∫ x in CoarseDeGiorgi.originCube (d := d) 1 \ CoarseDeGiorgi.closedReferenceCube (d := d) τ,
        (Φ x * fderiv ℝ φ x (basisVec i) + fderiv ℝ Φ x (basisVec i) * φ x) =
      (∫ x, Φ x * φ x ∂(CoarseDeGiorgi.cubeFaceMeasure τ i false)) -
        ∫ x, Φ x * φ x ∂(CoarseDeGiorgi.cubeFaceMeasure τ i true) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hFi := integrable_gaussGreen_integrand hΦ hφ hc i
  have hBm : MeasurableSet (CoarseDeGiorgi.closedReferenceCube (d := n + 1) τ) := by
    have : CoarseDeGiorgi.closedReferenceCube (d := n + 1) τ =
        ⋂ j, {x : Vec (n + 1) | |x j| ≤ τ / 2} := by
      ext x
      simp [CoarseDeGiorgi.closedReferenceCube]
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) measurable_const
  have hBO : CoarseDeGiorgi.closedReferenceCube (d := n + 1) τ ⊆
      CoarseDeGiorgi.originCube (d := n + 1) 1 := by
    intro x hx j
    have h := abs_le.1 (hx j)
    constructor <;> linarith [h.1, h.2]
  have hO : ∫ x in CoarseDeGiorgi.originCube (d := n + 1) 1,
      (Φ x * fderiv ℝ φ x (basisVec i) + fderiv ℝ Φ x (basisVec i) * φ x) =
      ∫ x, (Φ x * fderiv ℝ φ x (basisVec i) + fderiv ℝ Φ x (basisVec i) * φ x) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have h1 : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
    have h2 : fderiv ℝ φ x (basisVec i) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (basisVec i))
        (fun h => hx (hs (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := φ) (basisVec i) h)))
    simp [h1, h2]
  have hPc : Continuous fun x => Φ x * φ x := hΦ.continuous.mul hφ.continuous
  rw [setIntegral_sdiff hBm hFi.integrableOn hBO, hO,
    integral_gaussGreen_integrand_eq_zero hΦ hφ hc hs i,
    setIntegral_closedReferenceCube_gaussGreen hΦ hφ hc hτ.le i,
    integral_cubeFaceMeasure_eq_faceBox hPc, integral_cubeFaceMeasure_eq_faceBox hPc]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  ring

end

end CoarseDeGiorgi.Whitney.Harmonic
