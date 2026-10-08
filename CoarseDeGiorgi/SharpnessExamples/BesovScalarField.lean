module

public import CoarseDeGiorgi.SharpnessExamples.BesovNorms
public import CoarseDeGiorgi.SharpnessExamples.BesovCylinderSum
public import CoarseDeGiorgi.SharpnessExamples.ScalarNormBounds

/-! # Finite cube quasi-norms for the scalar cylinder field and its inverse

Step 3 of the source: the summed cylinder bound, applied to the majorants of the field and of
its inverse, with Minkowski, square-root subadditivity and monotone convergence.
-/

@[expose] public section

open Homogenization MeasureTheory
open CoarseDeGiorgi.Sharpness CoarseDeGiorgi.Foundations.FracGeometry
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem summable_sqrt_cylinderB : Summable (fun n => Real.sqrt (cylinderB n)) := by
  have hs2 : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have h : ∀ n, Real.sqrt (cylinderB n) = Real.sqrt (1 / 2) ^ (n + 3) := by
    intro n
    unfold cylinderB
    have : (1 / 2 : ℝ) ^ (n + 3) = (Real.sqrt (1 / 2) ^ (n + 3)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, hs2]
    rw [this, Real.sqrt_sq (by positivity)]
  simp_rw [h]
  have hlt : Real.sqrt (1 / 2 : ℝ) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  simpa only [pow_add] using
    (summable_geometric_of_lt_one (Real.sqrt_nonneg _) hlt).mul_right (Real.sqrt (1 / 2) ^ 3)

private theorem majorant_average (m n k : ℕ) (ζ κ α L : ℝ)
    (η : SimplexIndex (m + 1) k) :
    volumeAverage (simplexCell k η) (scalarMajorantTerm m n ζ κ α L) =
      cylinderB n * Real.rpow (cylinderRadius (m + 1) n ζ κ) (-α) *
        cylinderFraction (simplexCell k η) (L * cylinderRadius (m + 1) n ζ κ)
          (scalarTailCenter m n) := by
  unfold scalarMajorantTerm cylinderFraction volumeAverage
  rw [integral_const_mul]
  ring

private theorem levelMoment_eq_mean' {m k : ℕ}
    (ε : ℝ) (c : Vec m) (v : ℝ) :
    cylinderFractionLevelMoment k ε c v = finitePowerMean
      (fun η : SimplexIndex (m + 1) k => cylinderFraction (simplexCell k η) ε c) v := by
  simp only [cylinderFractionLevelMoment, finitePowerMean, SimplexIndex,
    Fintype.card_coe, Finset.univ_eq_attach]

/-- The discounted level of a cylinder majorant is its amplitude times the discounted level of
the cylinder fractions. -/
theorem majorant_level_eq {m : ℕ} (hm : 2 ≤ m) {ζ κ α L v b : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hκ : 0 < κ) (hv : 1 ≤ v) (n k : ℕ) :
    Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
      finitePowerMean (fun η : SimplexIndex (m + 1) k =>
        volumeAverage (simplexCell k η) (scalarMajorantTerm m n ζ κ α L)) v =
      cylinderB n * Real.rpow (cylinderRadius (m + 1) n ζ κ) (-α) *
        cylinderFractionDiscountedLevel k (L * cylinderRadius (m + 1) n ζ κ)
          (scalarTailCenter m n) v b := by
  have hrad := scalarRadius_small (m := m) (k := n) (by omega) hζ0 hζ2 hκ
  have hA : 0 ≤ cylinderB n * Real.rpow (cylinderRadius (m + 1) n ζ κ) (-α) :=
    mul_nonneg (cylinderB_pos n).le (Real.rpow_nonneg hrad.1.le _)
  have hmean : finitePowerMean (fun η : SimplexIndex (m + 1) k =>
        volumeAverage (simplexCell k η) (scalarMajorantTerm m n ζ κ α L)) v =
      cylinderB n * Real.rpow (cylinderRadius (m + 1) n ζ κ) (-α) *
        cylinderFractionLevelMoment k (L * cylinderRadius (m + 1) n ζ κ)
          (scalarTailCenter m n) v := by
    simp only [majorant_average]
    rw [finitePowerMean_smul _
      (fun η => (cylinderSimplex_fraction_bounds _ (scalarTailCenter m n) η).1)
      hA (zero_lt_one.trans_le hv), levelMoment_eq_mean']
  rw [hmean]
  unfold cylinderFractionDiscountedLevel
  ring

/-- The summed roots over the levels of one cylinder majorant. -/
theorem majorant_root_sum {m : ℕ} (hm : 2 ≤ m) {ζ κ α L v b : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hκ : 0 < κ) (hL0 : 0 < L) (hL2 : L ≤ 2) (hv : 1 ≤ v) (hb : 0 < b)
    (hαm : α < m) (hαvb : α ≤ (m : ℝ) / v + 2 * b) (n : ℕ) :
    Summable (fun k : ℕ => Real.sqrt (Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
        finitePowerMean (fun η : SimplexIndex (m + 1) k =>
          volumeAverage (simplexCell k η) (scalarMajorantTerm m n ζ κ α L)) v)) ∧
      ∑' k : ℕ, Real.sqrt (Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
        finitePowerMean (fun η : SimplexIndex (m + 1) k =>
          volumeAverage (simplexCell k η) (scalarMajorantTerm m n ζ κ α L)) v) ≤
        cylinderRootConstant m v b α * Real.rpow L (α / 2) * Real.sqrt (cylinderB n) := by
  have hrad := scalarRadius_small (m := m) (k := n) (by omega) hζ0 hζ2 hκ
  set ε := cylinderRadius (m + 1) n ζ κ with hε
  have hLε0 : 0 < L * ε := mul_pos hL0 hrad.1
  have hLε : L * ε < 1 / 4 := (mul_le_mul_of_nonneg_right hL2 hrad.1.le).trans_lt hrad.2
  obtain ⟨hs, hsum⟩ := cylinderFractionDiscountedRoot_sum (n := m) hLε0 hLε (scalarTailCenter m n)
    scalarTailCenter_coord_bound hv hb hαm hαvb
  have hA : 0 ≤ cylinderB n * Real.rpow ε (-α) :=
    mul_nonneg (cylinderB_pos n).le (Real.rpow_nonneg hrad.1.le _)
  have heq : ∀ k : ℕ, Real.sqrt (Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
        finitePowerMean (fun η : SimplexIndex (m + 1) k =>
          volumeAverage (simplexCell k η) (scalarMajorantTerm m n ζ κ α L)) v) =
      Real.sqrt (cylinderB n * Real.rpow ε (-α)) *
        Real.sqrt (cylinderFractionDiscountedLevel k (L * ε) (scalarTailCenter m n) v b) := by
    intro k
    rw [majorant_level_eq hm hζ0 hζ2 hκ hv n k, Real.sqrt_mul hA]
  simp_rw [heq]
  refine ⟨hs.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have hcoef : Real.sqrt (cylinderB n * Real.rpow ε (-α)) * Real.rpow (L * ε) (α / 2) =
      Real.rpow L (α / 2) * Real.sqrt (cylinderB n) := by
    have h1 : Real.sqrt (Real.rpow ε (-α)) = ε ^ (-α / 2) := by
      rw [Real.sqrt_eq_rpow]
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hrad.1.le]
      congr 1
      ring
    have h2 : ε ^ (-α / 2) * ε ^ (α / 2) = 1 := by
      rw [← Real.rpow_add hrad.1]
      have : -α / 2 + α / 2 = 0 := by ring
      rw [this, Real.rpow_zero]
    have h3 : Real.rpow (L * ε) (α / 2) = L ^ (α / 2) * ε ^ (α / 2) :=
      Real.mul_rpow hL0.le hrad.1.le
    rw [Real.sqrt_mul (cylinderB_pos n).le, h1, h3]
    calc _ = Real.sqrt (cylinderB n) * L ^ (α / 2) * (ε ^ (-α / 2) * ε ^ (α / 2)) := by ring
      _ = _ := by rw [h2]; simp only [Real.rpow_eq_pow]; ring
  calc _ ≤ Real.sqrt (cylinderB n * Real.rpow ε (-α)) *
        (cylinderRootConstant m v b α * Real.rpow (L * ε) (α / 2)) :=
      mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
    _ = cylinderRootConstant m v b α *
        (Real.sqrt (cylinderB n * Real.rpow ε (-α)) * Real.rpow (L * ε) (α / 2)) := by ring
    _ = _ := by rw [hcoef]; ring

/-- A positive field dominated by `1 +` a series of cylinder majorants has finite cube
quasi-norm. -/
theorem majorant_besov_lt_top {m : ℕ} (hm : 2 ≤ m) {ζ κ α L v b : ℝ} (hζ0 : 0 < ζ)
    (hζ2 : ζ < 2) (hκ : 0 < κ) (hL0 : 0 < L) (hL2 : L ≤ 2) (hv : 1 ≤ v) (hb : 0 < b)
    (hαm : α < m) (hαvb : α ≤ (m : ℝ) / v + 2 * b)
    (w : Vec (m + 1) → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw : IntegrableOn w (originCube 1) volume)
    (hmaj : ∀ x, w x ≤ 1 + ∑' n, scalarMajorantTerm m n ζ κ α L x)
    (hentries : ∀ i j, Integrable (fun x => (w x • (1 : Mat (m + 1))) i j)
      (volume.restrict (originCube 1))) :
    besovCubeNorm (fun x => w x • (1 : Mat (m + 1))) hentries b v hb hv < ⊤ := by
  have hB : Summable cylinderB := by
    change Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 3))
    simpa only [pow_add] using summable_geometric_two.mul_right ((1 / 2 : ℝ) ^ 3)
  set K : ℝ := cylinderFractionDiscountedUpperConstant m v *
    Real.rpow L (min (m : ℝ) ((m : ℝ) / v + 2 * b)) with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    unfold cylinderFractionDiscountedUpperConstant
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg hL0.le _)
  have hlevel := fun k n => scalarMajorant_discounted_bound hm hζ0 hζ2 hκ hαm.le hαvb hL0 hL2 hv
    hb.le k n
  refine scalar_besovCubeNorm_lt_top w hw0 hw (fun n => scalarMajorantTerm m n ζ κ α L)
    (scalarMajorantTerm_nonneg m · ζ κ α L) (fun n => scalarMajorantTerm_integrable m n ζ κ α L)
    (scalarMajorant_integral_summable hm hζ0 hζ2 hκ hαm.le hL0 hL2) hmaj hv hb
    (fun n => K * cylinderB n) (hB.mul_left K) ?_ (fun k n => hlevel k n)
    (fun n => cylinderRootConstant m v b α * Real.rpow L (α / 2) * Real.sqrt (cylinderB n))
    (summable_sqrt_cylinderB.mul_left _)
    (fun n => majorant_root_sum hm hζ0 hζ2 hκ hL0 hL2 hv hb hαm hαvb n) hentries
  simp_rw [Real.sqrt_mul hK0]
  exact summable_sqrt_cylinderB.mul_left _

/-- The cube quasi-norm of the scalar field. -/
theorem scalarSharpnessWeight_besov {m : ℕ} (hm : 2 ≤ m) {ζ κ v b : ℝ} (hζ0 : 0 < ζ)
    (hζ2 : ζ < 2) (hκ : 0 < κ) (hv : 1 ≤ v) (hb : 0 < b)
    (hζ : ζ ≤ (m : ℝ) / v + 2 * b)
    (hentries : ∀ i j, Integrable
      (fun x => (scalarSharpnessWeight (d := m + 1) ζ κ x • (1 : Mat (m + 1))) i j)
      (volume.restrict (originCube 1))) :
    besovCubeNorm (fun x => scalarSharpnessWeight (d := m + 1) ζ κ x • (1 : Mat (m + 1)))
      hentries b v hb hv < ⊤ := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact majorant_besov_lt_top hm hζ0 hζ2 hκ (by norm_num) (by norm_num) hv hb (by linarith) hζ _
    (fun x => (scalarSharpnessWeight_pos (by omega) hζ0 hζ2 hκ x).le)
    (scalarSharpnessWeight_integrable (by omega) hζ0 hζ2 hκ).1
    (scalarSharpnessWeight_majorant hm hζ0 hζ2 hκ) hentries

/-- The inverse of the scalar coefficient matrix is the scalar inverse times the identity. -/
theorem scalarWeight_inv_matrix {m : ℕ} (hm : 2 ≤ m) {ζ κ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hκ : 0 < κ) :
    (fun x : Vec (m + 1) => (scalarSharpnessWeight (d := m + 1) ζ κ x • (1 : Mat (m + 1)))⁻¹) =
      fun x => (scalarSharpnessWeight (d := m + 1) ζ κ x)⁻¹ • (1 : Mat (m + 1)) := by
  funext x
  have h := scalarSharpnessCoefficient_inv_diagonal (d := m + 1) (by omega) hζ0 hζ2 hκ x
  change (scalarSharpnessCoefficient (d := m + 1) ζ κ x)⁻¹ = _ at h
  unfold scalarSharpnessCoefficient at h
  rw [h]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]

/-- The cube quasi-norm of the inverse scalar field. -/
theorem scalarSharpnessWeight_inv_besov {m : ℕ} (hm : 2 ≤ m) {ζ κ v b : ℝ} (hζ0 : 0 < ζ)
    (hζ2 : ζ < 2) (hκ : 0 < κ) (hv : 1 ≤ v) (hb : 0 < b)
    (hζ : 2 - ζ ≤ (m : ℝ) / v + 2 * b)
    (hentries : ∀ i j, Integrable
      (fun x => (scalarSharpnessWeight (d := m + 1) ζ κ x • (1 : Mat (m + 1)))⁻¹ i j)
      (volume.restrict (originCube 1))) :
    besovCubeNorm (fun x => (scalarSharpnessWeight (d := m + 1) ζ κ x • (1 : Mat (m + 1)))⁻¹)
      hentries b v hb hv < ⊤ := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have heq := scalarWeight_inv_matrix hm hζ0 hζ2 hκ
  have hωinv := (scalarSharpnessWeight_integrable (d := m + 1) (by omega) hζ0 hζ2 hκ).2
  have hent' : ∀ i j, Integrable
      (fun x => ((scalarSharpnessWeight (d := m + 1) ζ κ x)⁻¹ • (1 : Mat (m + 1))) i j)
      (volume.restrict (originCube 1)) := by
    intro i j
    simpa only [Matrix.smul_apply, smul_eq_mul] using hωinv.mul_const ((1 : Mat (m + 1)) i j)
  have key := majorant_besov_lt_top hm hζ0 hζ2 hκ (by norm_num : (0 : ℝ) < 2) le_rfl hv hb
    (α := 2 - ζ) (by linarith) hζ (fun x => (scalarSharpnessWeight (d := m + 1) ζ κ x)⁻¹)
    (fun x => (inv_pos.mpr (scalarSharpnessWeight_pos (by omega) hζ0 hζ2 hκ x)).le) hωinv
    (scalarInvSharpnessWeight_majorant hm hζ0 hζ2 hκ) hent'
  simp only [besovCubeNorm] at key ⊢
  simpa only [heq] using key

end

end CoarseDeGiorgi.SharpnessExamples
