module

public import CoarseDeGiorgi.Selection.CellIncidence
public import CoarseDeGiorgi.Selection.TraceBounds
public import CoarseDeGiorgi.Selection.SamplingMoment
public import CoarseDeGiorgi.Statements.CriticalSurfaceEmbedding
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.TwoLevelQuantity
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Assembly.ParameterDefs
public import CoarseDeGiorgi.Statements.RBoundaryParam
public import CoarseDeGiorgi.Statements.RStarParam
public import CoarseDeGiorgi.Statements.TriangulationCard

@[expose] public section

namespace CoarseDeGiorgi.Selection
open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators Matrix.Norms.L2Operator
noncomputable section

/-- Actual sampled-cell incidence from `e.boundary.maxima`. -/
def sourceCellIncidence {d : ℕ} (k : ℕ) (η : SimplexIndex d k) : Set ℝ :=
  radiusIncidence (closure (simplexCell k η)) (100 * (d : ℝ) * (3 : ℝ) ^ (-(k : ℤ)))

/-- Actual matrix-response weight: the norm of the upper response `upperResponseOnCell`. -/
def sourceResponseWeight {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (η : SimplexIndex d k) : ℝ≥0∞ :=
  ENNReal.ofReal ‖upperResponseOnCell k a ha η‖

/-- The source's empty-maximum-zero convention is inherited from sampledMaximum. -/
def sourceSampledResponse {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (τ : ℝ) : ℝ≥0∞ :=
  sampledMaximum (triangulation k).attach (sourceResponseWeight a ha k) (sourceCellIncidence k) τ

/-- The literal discounted response series S of `e.boundary.maxima.series`. -/
def sourceSampledSeries {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s p τ : ℝ) : ℝ≥0∞ :=
  sampledSeries (fun k => (triangulation k).attach) (sourceResponseWeight a ha)
    sourceCellIncidence (triadicSamplingDiscount d s p) τ

theorem source_cell_closure_bounds {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    IsCompact (closure (simplexCell k η)) ∧
    ∀ x ∈ closure (simplexCell k η),
      ‖x - (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.val.1 i : ℝ))‖ ≤
        (3 : ℝ) ^ (-(k : ℤ)) / 2 := by
  let z : Vec d := fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.val.1 i : ℝ)
  let ell := (3 : ℝ) ^ (-(k : ℤ))
  have he : simplexCell k η = Foundations.Simplex.kuhnSimplex (-(k : ℤ)) η.val.2 z :=
    Moments.simplex_eq_kuhnSimplex _ _ _
  have hs : 0 < ell := zpow_pos (by norm_num) _
  have hsub : simplexCell k η ⊆ Metric.closedBall z (ell / 2) := by
    intro x hx
    rw [he] at hx
    rw [Metric.mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg (half_pos hs).le]
    intro i
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    constructor
    · simpa only [neg_div] using (hx.1 i).1.le
    · exact (hx.1 i).2.le
  have hcl := closure_minimal hsub Metric.isClosed_closedBall
  refine ⟨(isCompact_closedBall z (ell / 2)).of_isClosed_subset isClosed_closure hcl, ?_⟩
  intro x hx
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hcl hx

theorem source_cell_incidence_measurable {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    MeasurableSet (sourceCellIncidence k η) :=
  radiusIncidence_measurable (source_cell_closure_bounds k η).1 _

theorem source_cell_incidence_width {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    volume (sourceCellIncidence k η) ≤
      ENNReal.ofReal (2 + 400 * (d : ℝ)) * (3 : ℝ≥0∞) ^ (-(k : ℝ)) := by
  have hh := incidence_measure_le (radiusIncidence_subset_interval
    (h := 100 * (d : ℝ) * (3 : ℝ) ^ (-(k : ℤ))) (source_cell_closure_bounds k η).2)
  apply hh.trans_eq
  have hp : (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ (-(k : ℝ)) := by
    rw [zpow_neg, zpow_natCast, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  conv_rhs => rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num,
    ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 3),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hp]
  ring

theorem source_response_average_identity {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (upperCellAverage a ha k p) =
      (∑ η ∈ (triangulation k).attach, (sourceResponseWeight a ha k η) ^ p) /
        ((Nat.factorial d : ℝ≥0∞) * (3 : ℝ≥0∞) ^ ((k : ℝ) * d)) := by
  let f : SimplexIndex d k → ℝ := fun η => ‖upperResponseOnCell k a ha η‖ ^ p
  let g : SimplexIndex d k → ℝ≥0∞ := fun η => ENNReal.ofReal ‖upperResponseOnCell k a ha η‖ ^ p
  change ENNReal.ofReal ((triangulation k).attach.sum f / ((triangulation k).card : ℝ)) =
    (triangulation k).attach.sum g / _
  rw [ENNReal.ofReal_div_of_pos (by
    rw [triangulation_card]
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos d) (pow_pos (by decide) _))]
  have hsum : ENNReal.ofReal ((triangulation k).attach.sum f) =
      (triangulation k).attach.sum (fun η => ENNReal.ofReal (f η)) :=
    ENNReal.ofReal_sum_of_nonneg (fun η _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hfg : (triangulation k).attach.sum (fun η => ENNReal.ofReal (f η)) =
      (triangulation k).attach.sum g := by
    apply Finset.sum_congr rfl
    intro η _
    exact (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (upperResponseOnCell k a ha η)) hp).symm
  have hden : ENNReal.ofReal ((triangulation (d := d) k).card : ℝ) =
      (Nat.factorial d : ℝ≥0∞) * (3 : ℝ≥0∞) ^ ((k : ℝ) * d) := by
    rw [triangulation_card]
    norm_cast
  exact congrArg₂ (fun x y : ℝ≥0∞ => x / y) (hsum.trans hfg) hden

theorem source_upper_moment_identity {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) :
    upperMoment a ha s p hs hp =
      (ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
        ∑' k : ℕ, (3 : ℝ≥0∞) ^ (-((k : ℝ) * s)) *
          ((∑ η ∈ (triangulation k).attach, (sourceResponseWeight a ha k η) ^ p) /
            ((Nat.factorial d : ℝ≥0∞) * (3 : ℝ≥0∞) ^ ((k : ℝ) * d))) ^
            (1 / (2 * p))) ^ (2 : ℕ) := by
  unfold upperMoment
  simp only [Real.rpow_eq_pow]
  simp_rw [source_response_average_identity a ha _ (zero_le_one.trans hp),
    ENNReal.rpow_eq_pow, ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 3)]
  norm_num only [ENNReal.ofReal_ofNat]

theorem source_sampled_series_measurable {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s p : ℝ) : Measurable (sourceSampledSeries a ha s p) :=
  sampledSeries_measurable _ _ _ _ (fun k η _ => source_cell_incidence_measurable k η)

/-- Concrete response sampling bound, with Λ the upper moment `upperMoment`. -/
theorem source_response_sampling {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) :
    powerNorm (2 * p) volume (sourceSampledSeries a ha s p) ≤
      (ENNReal.ofReal (2 + 400 * (d : ℝ)) * (Nat.factorial d : ℝ≥0∞)) ^ (1 / (2 * p)) *
        (upperMoment a ha s p hs hp) ^ (1 / 2 : ℝ) /
        ENNReal.ofReal (1 - Real.rpow 3 (-s)) := by
  apply response_sampling_of_moment_identity _ _ _
    (fun k η _ => source_cell_incidence_measurable k η) d hs hp volume _ _ _
    (by exact_mod_cast (Nat.factorial_pos d).ne') (by finiteness)
    (fun k η _ => source_cell_incidence_width k η)
    (source_upper_moment_identity a ha hs hp)

end
end CoarseDeGiorgi.Selection
