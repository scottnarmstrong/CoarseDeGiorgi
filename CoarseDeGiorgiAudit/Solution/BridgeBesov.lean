import CoarseDeGiorgi.Weighted.ZeroCore
import CoarseDeGiorgi.Weighted.LowerResponse
import CoarseDeGiorgi.Weighted.ResponseBoundsLower

open Homogenization MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.Solution.BridgeBesov

theorem posDef_abs_entry_le_trace {d : ℕ} (A : Mat d) (hA : A.PosDef)
    (i j : Fin d) : |A i j| ≤ A.trace := by
  by_cases hij : i = j
  · subst j
    have hdiag : 0 ≤ A i i := by
      simpa [Matrix.diag] using hA.posSemidef.diag_nonneg
    have hsum : A i i ≤ A.trace := by
      unfold Matrix.trace
      calc
        A i i = A.diag i := rfl
        _ ≤ ∑ k, A.diag k :=
          Finset.single_le_sum
            (fun k _ => by simpa [Matrix.diag] using hA.posSemidef.diag_nonneg)
            (Finset.mem_univ i)
    rw [abs_of_nonneg hdiag]
    exact hsum
  · have hsym : A.IsSymm := by
      simpa [Matrix.IsSymm, Matrix.IsHermitian] using hA.1
    have hji : A j i = A i j := by
      have h := congrFun (congrFun hsym i) j
      simpa [Matrix.IsSymm] using h
    let ei : Vec d := Pi.single i 1
    let ej : Vec d := Pi.single j 1
    have hplusQ :=
      CoarseDeGiorgi.Weighted.quadratic_le_trace_mul_length_sq A hA (ei + ej)
    have hminusQ :=
      CoarseDeGiorgi.Weighted.quadratic_le_trace_mul_length_sq A hA (ei - ej)
    have hplusSq :
        vecDot (ei + ej) (matVecMul A (ei + ej)) =
          A i i + A i j + A j i + A j j := by
      change dotProduct (ei + ej) (Matrix.mulVec A (ei + ej)) = _
      rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add]
      simp [ei, ej, Matrix.col_apply]
      ring
    have hminusSq :
        vecDot (ei - ej) (matVecMul A (ei - ej)) =
          A i i - A i j - A j i + A j j := by
      change dotProduct (ei - ej) (Matrix.mulVec A (ei - ej)) = _
      rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
      simp [ei, ej, Matrix.col_apply]
      ring
    have hplusLen : vecDot (ei + ej) (ei + ej) = 2 := by
      change dotProduct (ei + ej) (ei + ej) = 2
      rw [add_dotProduct, dotProduct_add]
      simp [ei, ej, hij]
      norm_num
    have hminusLen : vecDot (ei - ej) (ei - ej) = 2 := by
      change dotProduct (ei - ej) (ei - ej) = 2
      rw [sub_dotProduct, dotProduct_sub]
      simp [ei, ej, hij]
      norm_num
    have hplus : A i i + A j j + 2 * A i j ≤ 2 * A.trace := by
      rw [hplusSq, hji] at hplusQ
      rw [hplusLen] at hplusQ
      nlinarith [hplusQ]
    have hminus : A i i + A j j - 2 * A i j ≤ 2 * A.trace := by
      rw [hminusSq, hji] at hminusQ
      rw [hminusLen] at hminusQ
      nlinarith [hminusQ]
    have hii : 0 ≤ A i i := by
      simpa [Matrix.diag] using hA.posSemidef.diag_nonneg
    have hjj : 0 ≤ A j j := by
      simpa [Matrix.diag] using hA.posSemidef.diag_nonneg
    have htrace : 0 ≤ A.trace := hA.posSemidef.trace_nonneg
    have hupper : A i j ≤ A.trace := by nlinarith [hplus]
    have hlower : -A.trace ≤ A i j := by nlinarith [hminus]
    exact abs_le.mpr ⟨hlower, hupper⟩

theorem matrixField_entries_integrable {d : ℕ} {μ : Measure (Vec d)}
    (A : Vec d → Mat d) (hAmeas : AEStronglyMeasurable A μ)
    (hApos : ∀ᵐ x ∂μ, (A x).PosDef)
    (htrace : Integrable (fun x => (A x).trace) μ) :
    ∀ i j, Integrable (fun x => A x i j) μ := by
  intro i j
  have hmeas : AEStronglyMeasurable (fun x => A x i j) μ :=
    (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hAmeas)
  apply Integrable.mono' htrace.norm hmeas
  filter_upwards [hApos] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hx.posSemidef.trace_nonneg]
  exact posDef_abs_entry_le_trace (A x) hx i j

theorem weightedCoeff_entries_integrable {d : ℕ} {V : Set (Vec d)}
    {A : CoeffField d} (hA : CoarseDeGiorgi.IsWeightedCoeffOn V A) :
    (∀ i j, Integrable (fun x => A x i j) (volume.restrict V)) ∧
      (∀ i j, Integrable (fun x => (A x)⁻¹ i j) (volume.restrict V)) := by
  refine ⟨matrixField_entries_integrable A hA.1 hA.2.1 hA.2.2.1, ?_⟩
  have hinvMeas : AEStronglyMeasurable (fun x => (A x)⁻¹)
      (volume.restrict V) :=
    (CoarseDeGiorgi.Weighted.response_matrix_inverse_measurable.comp_aemeasurable
      hA.1.aemeasurable).aestronglyMeasurable
  have hinvPos : ∀ᵐ x ∂(volume.restrict V), ((A x)⁻¹).PosDef :=
    hA.2.1.mono fun x hx => hx.inv
  exact matrixField_entries_integrable (fun x => (A x)⁻¹)
    hinvMeas hinvPos hA.2.2.2

theorem sqrt_toReal_le_mul {x y : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c)
    (hy : y ≠ ⊤) (hxy : x ≤ ENNReal.ofReal c * y) :
    Real.sqrt x.toReal ≤ Real.sqrt c * Real.sqrt y.toReal := by
  have hrightTop : ENNReal.ofReal c * y ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy
  have hleftTop : x ≠ ⊤ := ne_top_of_le_ne_top hrightTop hxy
  have hreal := (ENNReal.toReal_le_toReal hleftTop hrightTop).mpr hxy
  have hmul : (ENNReal.ofReal c * y).toReal = c * y.toReal := by
    simp [ENNReal.toReal_mul, hc]
  calc
    Real.sqrt x.toReal ≤ Real.sqrt ((ENNReal.ofReal c * y).toReal) :=
      Real.sqrt_le_sqrt hreal
    _ = Real.sqrt (c * y.toReal) := congrArg Real.sqrt hmul
    _ = Real.sqrt c * Real.sqrt y.toReal := Real.sqrt_mul hc _

theorem one_add_rpow_bound {x y : ℝ≥0∞} {c κ : ℝ}
    (hc : 1 ≤ c) (hκ : 0 ≤ κ) (hxy : x ≤ ENNReal.ofReal c * y) :
    (1 + x).rpow κ ≤ (ENNReal.ofReal c).rpow κ * (1 + y).rpow κ := by
  have hcENN : (1 : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    simpa using ENNReal.ofReal_le_ofReal hc
  have hbase : 1 + x ≤ ENNReal.ofReal c * (1 + y) := by
    calc
      1 + x ≤ ENNReal.ofReal c + ENNReal.ofReal c * y := add_le_add hcENN hxy
      _ = ENNReal.ofReal c * (1 + y) := by rw [mul_add, mul_one]
  calc
    (1 + x).rpow κ ≤ (ENNReal.ofReal c * (1 + y)).rpow κ :=
      ENNReal.rpow_le_rpow hbase hκ
    _ = (ENNReal.ofReal c).rpow κ * (1 + y).rpow κ :=
      ENNReal.mul_rpow_of_nonneg _ _ hκ

end CoarseDeGiorgiAudit.Solution.BridgeBesov
