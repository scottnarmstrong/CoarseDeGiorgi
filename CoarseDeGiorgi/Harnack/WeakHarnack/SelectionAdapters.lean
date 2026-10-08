module

public import CoarseDeGiorgi.Statements.EuclideanSetDistance
public import CoarseDeGiorgi.Statements.EuclidDist
public import CoarseDeGiorgi.Statements.CubeSurface
public import CoarseDeGiorgi.Statements.PositiveCap
public import CoarseDeGiorgi.Statements.PositiveCapGradient
public import CoarseDeGiorgi.Statements.SampledUpperResponse
public import CoarseDeGiorgi.Statements.SampledResponseSeries
public import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
public import CoarseDeGiorgi.Harnack.Selection.Cap
public import CoarseDeGiorgi.Selection.SourceResponses
public import CoarseDeGiorgi.Selection.SurfaceEnergy
public import CoarseDeGiorgi.Foundations.Euclid.Basic

@[expose] public section

namespace CoarseDeGiorgi.Harnack.WeakHarnack

open Homogenization MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

private theorem euclideanSetDistance_eq_minimum {d : ℕ}
    {C T : Set (Vec d)} (hC : IsCompact C) (hT : IsCompact T)
    (hCne : C.Nonempty) (hTne : T.Nonempty) :
    ∃ x ∈ C, ∃ y ∈ T,
      euclideanSetDistance C T = ENNReal.ofReal (euclidDist x y) ∧
        ∀ x' ∈ C, ∀ y' ∈ T, euclidDist x y ≤ euclidDist x' y' := by
  let P : Set (Vec d × Vec d) := C ×ˢ T
  let f : Vec d × Vec d → ℝ := fun z => euclidDist z.1 z.2
  have hP : IsCompact P := hC.prod hT
  have hPne : P.Nonempty := by
    obtain ⟨x, hx⟩ := hCne
    obtain ⟨y, hy⟩ := hTne
    exact ⟨(x, y), hx, hy⟩
  have hf : ContinuousOn f P := by
    have hc : Continuous f := by
      change Continuous (fun z : Vec d × Vec d =>
        Foundations.Euclid.eNorm2 (z.1 - z.2))
      exact Foundations.Euclid.continuous_eNorm2.comp (continuous_fst.sub continuous_snd)
    exact hc.continuousOn
  obtain ⟨z, hz, hzmin⟩ := hP.exists_isMinOn hPne hf
  have hdist_form : euclideanSetDistance C T =
      ⨅ w : C × T, ENNReal.ofReal
        (euclidDist (w.1 : Vec d) (w.2 : Vec d)) := by
    unfold euclideanSetDistance
    simp only [iInf_subtype', iInf_prod]
  have hlow : ENNReal.ofReal (euclidDist z.1 z.2) ≤ euclideanSetDistance C T := by
    rw [hdist_form]
    apply le_iInf
    intro w
    have hmem : ((w.1 : Vec d), (w.2 : Vec d)) ∈ P := ⟨w.1.2, w.2.2⟩
    apply ENNReal.ofReal_le_ofReal
    simpa [f] using hzmin hmem
  have hupp : euclideanSetDistance C T ≤ ENNReal.ofReal (euclidDist z.1 z.2) := by
    rw [hdist_form]
    exact iInf_le _ (⟨⟨z.1, hz.1⟩, ⟨z.2, hz.2⟩⟩ : C × T)
  refine ⟨z.1, hz.1, z.2, hz.2, le_antisymm hupp hlow, ?_⟩
  intro x hx y hy
  have hmem : (x, y) ∈ P := ⟨hx, hy⟩
  exact hzmin hmem

private theorem euclideanSetDistance_le_iff_exists {d : ℕ}
    {C T : Set (Vec d)} (hC : IsCompact C) (hT : IsCompact T)
    (hCne : C.Nonempty) (hTne : T.Nonempty) {r : ℝ} (hr : 0 ≤ r) :
    euclideanSetDistance C T ≤ ENNReal.ofReal r ↔
      ∃ x ∈ C, ∃ y ∈ T, euclidDist x y ≤ r := by
  obtain ⟨x, hx, y, hy, hmin, hminimal⟩ :=
    euclideanSetDistance_eq_minimum hC hT hCne hTne
  have hxnonneg : 0 ≤ euclidDist x y := by
    simp [euclidDist]
  constructor
  · intro h
    have h' : ENNReal.ofReal (euclidDist x y) ≤ ENNReal.ofReal r := by
      rw [← hmin]
      exact h
    exact ⟨x, hx, y, hy,
      (ENNReal.ofReal_le_ofReal_iff hr).mp h'⟩
  · rintro ⟨x', hx', y', hy', hxy⟩
    rw [hmin]
    apply ENNReal.ofReal_le_ofReal
    exact (hminimal x' hx' y' hy').trans hxy

private theorem cubeSurface_nonempty_of_pos {d : ℕ} [NeZero d] {τ : ℝ}
    (hτ : 0 < τ) : (cubeSurface (d := d) τ).Nonempty := by
  let x : Vec d := fun _ => τ / 2
  refine ⟨x, ?_⟩
  change ‖x‖ = τ / 2
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    have hτ2 : 0 ≤ τ / 2 := by linarith
    simp only [x, Real.norm_eq_abs, abs_of_nonneg hτ2]
    exact le_rfl
  · calc
      τ / 2 = |x 0| := by
        change τ / 2 = |τ / 2|
        rw [abs_of_pos (by linarith)]
      _ = ‖x 0‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖x‖ := norm_le_pi_norm x 0

private theorem sourceCellIncidence_iff_statement_near {d : ℕ} [NeZero d]
    (k : ℕ) (η : SimplexIndex d k) (τ : ℝ) :
    Selection.sourceCellIncidence k η τ ↔
      τ ∈ Ioo (1 / 2 : ℝ) 1 ∧
        euclideanSetDistance (closure (simplexCell k η)) (cubeSurface τ) ≤
          ENNReal.ofReal (100 * (d : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) := by
  have hC := Selection.source_cell_closure_bounds k η
  have hT : IsCompact (cubeSurface (d := d) τ) :=
    Selection.isCompact_cubeSurface (d := d) τ
  change τ ∈ Selection.radiusIncidence (closure (simplexCell k η))
      (100 * (d : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) ↔ _
  rw [Selection.radiusIncidence_iff]
  constructor
  · rintro ⟨hτ, x, hx, y, hy, hxy⟩
    have hτpos : 0 < τ := by linarith [hτ.1]
    have hTne := cubeSurface_nonempty_of_pos (d := d) hτpos
    have hCne : (closure (simplexCell k η)).Nonempty := by
      obtain ⟨x, hx⟩ := CoarseDeGiorgi.simplexCell_nonempty k η
      exact ⟨x, subset_closure hx⟩
    refine ⟨hτ, ?_⟩
    apply (euclideanSetDistance_le_iff_exists hC.1 hT hCne hTne (by positivity)).2
    · refine ⟨x, hx, y, hy, ?_⟩
      simpa [euclidDist, Foundations.Euclid.eDist2, Foundations.Euclid.eNorm2] using hxy
  · rintro ⟨hτ, hnear⟩
    have hτpos : 0 < τ := by linarith [hτ.1]
    have hTne := cubeSurface_nonempty_of_pos (d := d) hτpos
    have hCne : (closure (simplexCell k η)).Nonempty := by
      obtain ⟨x, hx⟩ := CoarseDeGiorgi.simplexCell_nonempty k η
      exact ⟨x, subset_closure hx⟩
    refine ⟨hτ, ?_⟩
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (euclideanSetDistance_le_iff_exists hC.1 hT hCne hTne (by positivity)).1 hnear
    refine ⟨x, hx, y, hy, ?_⟩
    simpa [euclidDist, Foundations.Euclid.eDist2, Foundations.Euclid.eNorm2] using hxy

private theorem responseThreshold_eq {d : ℕ} (k : ℕ) :
    ENNReal.ofReal (100 * (d : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) =
      (100 : ℝ≥0∞) * (d : ℝ≥0∞) * ((3 : ℝ≥0∞) ^ k)⁻¹ := by
  have hpow : (3 : ℝ) ^ (-(k : ℤ)) = ((3 : ℝ) ^ k)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hpow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_inv_of_pos (by positivity)]
  norm_num

private theorem sourceSampledResponse_eq_statement {d : ℕ} [NeZero d]
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (k : ℕ) (τ : ℝ) (hτ : τ ∈ Ioo (1 / 2 : ℝ) 1) :
    Selection.sourceSampledResponse a ha k τ =
      sampledUpperResponse a ha k τ := by
  classical
  have hattach : (triangulation (d := d) k).attach =
      (Finset.univ : Finset (SimplexIndex d k)) := by
    ext η
    simp [SimplexIndex]
  dsimp only [SimplexIndex] at hattach ⊢
  unfold Selection.sourceSampledResponse Selection.sampledMaximum
  rw [Finset.sup_eq_iSup, hattach]
  simp only [Finset.mem_univ, iSup_true]
  unfold sampledUpperResponse
  apply iSup_congr
  intro η
  let η' : SimplexIndex d k := ⟨η.1, η.2⟩
  change (if Selection.sourceCellIncidence k η' τ then
      ENNReal.ofReal ‖upperResponseOnCell k a ha η'‖ else 0) =
    ⨆ (_ : euclideanSetDistance (closure (simplexCell k η')) (cubeSurface τ) ≤
      ENNReal.ofReal (100 * (d : ℝ) * (3 : ℝ) ^ (-(k : ℤ)))),
      ENNReal.ofReal ‖upperResponseOnCell k a ha η'‖
  rw [sourceCellIncidence_iff_statement_near]
  rw [responseThreshold_eq]
  simp only [Set.mem_Ioo]
  simp only [Set.mem_Ioo] at hτ
  obtain ⟨hbelow, habove⟩ := hτ
  have hhalf : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
  have hlo : 2⁻¹ < τ := by simpa only [hhalf] using hbelow
  by_cases hnear : euclideanSetDistance (closure (simplexCell k η'))
      (cubeSurface τ) ≤ (100 : ℝ≥0∞) * (d : ℝ≥0∞) * ((3 : ℝ≥0∞) ^ k)⁻¹
  · simp [hlo, habove, hnear]
  · simp [hlo, habove, hnear]

theorem sourceSampledSeries_eq_statement {d : ℕ} [NeZero d]
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (s p τ : ℝ) (hτ : τ ∈ Ioo (1 / 2 : ℝ) 1) :
    Selection.sourceSampledSeries a ha s p τ =
      sampledResponseSeries a ha s p τ := by
  unfold Selection.sourceSampledSeries Selection.sampledSeries sampledResponseSeries
  apply tsum_congr
  intro k
  change Selection.triadicSamplingDiscount d s p k *
      (Selection.sourceSampledResponse a ha k τ) ^ (1 / 2 : ℝ) =
    ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * (s + ((d : ℝ) - 1) / (2 * p)))) ) *
      (sampledUpperResponse a ha k τ) ^ (1 / 2 : ℝ)
  rw [sourceSampledResponse_eq_statement a ha k τ hτ]
  rw [Selection.triadicSamplingDiscount]
  have hbase : (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) := by norm_num
  rw [hbase, ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 3)]
  norm_num

theorem sourceSurfaceEnergyMaximal_eq_statement {n : ℕ}
    (ρ R : ℝ) (a : CoeffField (n + 1))
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (G : Vec (n + 1) → Vec (n + 1)) (τ : ℝ) :
    Selection.surfaceEnergyMaximal ρ R
        (fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))) τ =
      surfaceEnergyMaximal ρ R a ha G τ := by
  unfold Selection.surfaceEnergyMaximal Selection.centeredMaximal surfaceEnergyMaximal
  congr 1
  funext ε
  congr 1
  funext hε
  rw [Selection.surfaceEnergyMeasure_ball]
  rw [Real.ball_eq_Ioo]
  rw [div_eq_mul_inv]
  ac_rfl

end
end CoarseDeGiorgi.Harnack.WeakHarnack
