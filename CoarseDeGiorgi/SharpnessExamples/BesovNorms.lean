module

public import CoarseDeGiorgi.SharpnessExamples.BesovSeries

/-! # Finite cube quasi-norms from summed cylinder bounds -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

private theorem three_pow_neg_sqrt (k : ℕ) (b : ℝ) :
    Real.sqrt (Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b))) = Real.rpow 3 (-((k : ℝ) * b)) := by
  rw [Real.sqrt_eq_rpow]
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- The level estimate: the term of the cube quasi-norm is at most the square root of the
discounted simplex power mean. -/
theorem besovCubeTerm_le {d : ℕ} [NeZero d] (k : ℕ) {w : Vec d → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hw : IntegrableOn w (originCube 1) volume) {v b : ℝ} (hv : 1 ≤ v) :
    Real.rpow 3 (-((k : ℝ) * b)) * Real.rpow (cubePowerMean k w v) (1 / (2 * v)) ≤
      Real.sqrt (Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
        finitePowerMean (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) w) v) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hnn : ∀ (V : Set (Vec d)), 0 ≤ volumeAverage V w := fun V => by
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg hw0)
  have hcpm0 : 0 ≤ cubePowerMean k w v :=
    div_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hnn _) _) (Nat.cast_nonneg _)
  have hle := cubePowerMean_le_simplex k hw0 hw hv
  have hsm0 : 0 ≤ ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow (volumeAverage (simplexCell k η) w) v) /
          ((triangulation (d := d) k).card : ℝ) :=
    div_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hnn _) _) (Nat.cast_nonneg _)
  have hfpm : finitePowerMean (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) w) v =
      Real.rpow (((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow (volumeAverage (simplexCell k η) w) v) /
          ((triangulation (d := d) k).card : ℝ)) (1 / v) := by
    unfold finitePowerMean
    simp only [SimplexIndex, Fintype.card_coe, Finset.univ_eq_attach]
  rw [Real.sqrt_mul (show (0 : ℝ) ≤ Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) from
    Real.rpow_nonneg (by norm_num) _), three_pow_neg_sqrt, hfpm]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  rw [Real.sqrt_eq_rpow]
  simp only [Real.rpow_eq_pow] at *
  rw [← Real.rpow_mul hsm0]
  have : 1 / v * (1 / 2) = 1 / (2 * v) := by field_simp
  rw [this]
  exact Real.rpow_le_rpow hcpm0 hle (by positivity)

/-- The cube quasi-norm of a positive scalar field dominated by `1 + ∑ f_n` is finite when the
levels of each `f_n` are bounded by a summable sequence with summable roots and the summed roots
over the levels are summable in `n`. -/
theorem scalar_besovCubeNorm_lt_top {d : ℕ} [NeZero d]
    (w : Vec d → ℝ) (hw0 : ∀ x, 0 ≤ w x)
    (hw : IntegrableOn w (originCube 1) volume)
    (f : ℕ → Vec d → ℝ) (hf0 : ∀ j x, 0 ≤ f j x)
    (hf : ∀ j, IntegrableOn (f j) (originCube 1) volume)
    (hs : Summable (fun j => ∫ x in originCube 1, ‖f j x‖ ∂volume))
    (hmaj : ∀ x, w x ≤ 1 + ∑' j, f j x)
    {v b : ℝ} (hv : 1 ≤ v) (hb : 0 < b)
    (C : ℕ → ℝ) (hC : Summable C) (hCs : Summable (fun n => Real.sqrt (C n)))
    (hlevel : ∀ (k n : ℕ), Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
      finitePowerMean (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) (f n)) v ≤ C n)
    (R : ℕ → ℝ) (hR : Summable R)
    (hroot : ∀ n, Summable (fun k : ℕ => Real.sqrt (Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
        finitePowerMean (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) (f n)) v)) ∧
      ∑' k : ℕ, Real.sqrt (Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b)) *
        finitePowerMean (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) (f n)) v) ≤ R n)
    (hentries : ∀ i j, Integrable (fun x => (w x • (1 : Mat d)) i j)
      (volume.restrict (originCube 1))) :
    besovCubeNorm (fun x => w x • (1 : Mat d)) hentries b v hb hv < ⊤ := by
  classical
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  let δ : ℕ → ℝ := fun k => Real.rpow 3 (-((2 : ℝ) * (k : ℝ) * b))
  have hδ : ∀ k, 0 < δ k := fun k => Real.rpow_pos_of_pos (by norm_num) _
  let M : ℕ → ℕ → ℝ := fun k n =>
    finitePowerMean (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) (f n)) v
  let y : ℕ → ℕ → ℝ := fun k n => Real.sqrt (δ k * M k n)
  have hM0 : ∀ k n, 0 ≤ M k n := fun k n => finitePowerMean_nonneg _ (fun η => by
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg (hf0 n))) v
  have hyC : ∀ k n, y k n ≤ Real.sqrt (C n) := fun k n =>
    Real.sqrt_le_sqrt (hlevel k n)
  have hysum : ∀ k, Summable (fun n => y k n) := fun k =>
    Summable.of_nonneg_of_le (fun n => Real.sqrt_nonneg _) (hyC k) hCs
  -- the level estimate
  have hX : ∀ k, Real.sqrt (δ k * finitePowerMean
      (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) w) v) ≤
      Real.rpow 3 (-((k : ℝ) * b)) + ∑' n, y k n := by
    intro k
    have hMsum : Summable (fun n => M k n) := by
      have hbound : ∀ n, M k n ≤ C n / δ k := fun n =>
        (le_div_iff₀ (hδ k)).2 (by rw [mul_comm]; exact hlevel k n)
      exact Summable.of_nonneg_of_le (hM0 k) hbound (hC.div_const _)
    have hmink := simplexMean_le_one_add_series k w hw0 hw f hf0 hf hs hmaj hv hMsum
    have h1 : δ k * finitePowerMean
        (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) w) v ≤
        δ k + ∑' n, δ k * M k n := by
      rw [tsum_mul_left]
      calc _ ≤ δ k * (1 + ∑' n, M k n) := mul_le_mul_of_nonneg_left hmink (hδ k).le
        _ = _ := by ring
    have hz0 : ∀ n, 0 ≤ δ k * M k n := fun n => mul_nonneg (hδ k).le (hM0 k n)
    have h2 := sqrt_tsum_le_tsum_sqrt hz0 (hysum k)
    calc Real.sqrt (δ k * _) ≤ Real.sqrt (δ k + ∑' n, δ k * M k n) := Real.sqrt_le_sqrt h1
      _ ≤ Real.sqrt (δ k) + Real.sqrt (∑' n, δ k * M k n) := by
        apply Real.sqrt_le_iff.2
        refine ⟨by positivity, ?_⟩
        have ha := Real.sq_sqrt (hδ k).le
        have hb' : Real.sqrt (∑' n, δ k * M k n) ^ 2 = ∑' n, δ k * M k n :=
          Real.sq_sqrt (tsum_nonneg hz0)
        nlinarith [Real.sqrt_nonneg (δ k), Real.sqrt_nonneg (∑' n, δ k * M k n),
          mul_nonneg (Real.sqrt_nonneg (δ k)) (Real.sqrt_nonneg (∑' n, δ k * M k n))]
      _ ≤ _ := by
        rw [show Real.sqrt (δ k) = Real.rpow 3 (-((k : ℝ) * b)) from three_pow_neg_sqrt k b]
        exact add_le_add le_rfl h2
  -- the sum over levels
  have hgeom : (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b)))) < ⊤ := by
    have hσ : Real.rpow 3 (-b) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hσ0 : 0 ≤ Real.rpow 3 (-b) := Real.rpow_nonneg (by norm_num) _
    have heq : ∀ k : ℕ, Real.rpow 3 (-((k : ℝ) * b)) = (Real.rpow 3 (-b)) ^ k := by
      intro k
      change (3 : ℝ) ^ (-((k : ℝ) * b)) = ((3 : ℝ) ^ (-b)) ^ k
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    simp_rw [heq]
    exact (summable_geometric_of_lt_one hσ0 hσ).tsum_ofReal_lt_top
  have hterm : ∀ k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b))) *
      (ENNReal.ofReal ((∑ j : Fin d → Fin (3 ^ k),
          Real.rpow ‖volumeAverageMat (triadicCube k j) (fun x => w x • (1 : Mat d))‖ v) /
        ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ))).rpow (1 / (2 * v)) ≤
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b))) + ∑' n, ENNReal.ofReal (y k n) := by
    intro k
    have hnorm : ∀ j : Fin d → Fin (3 ^ k),
        ‖volumeAverageMat (triadicCube k j) (fun x => w x • (1 : Mat d))‖ =
          volumeAverage (triadicCube k j) w := fun j =>
      norm_volumeAverageMat_scalar_identity _ w hw0
    simp only [hnorm]
    change ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b))) *
      (ENNReal.ofReal (cubePowerMean k w v)).rpow (1 / (2 * v)) ≤ _
    have hcpm0 : 0 ≤ cubePowerMean k w v :=
      div_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (by
        unfold volumeAverage
        exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg hw0)) _)
        (Nat.cast_nonneg _)
    have hA0 : 0 ≤ Real.rpow 3 (-((k : ℝ) * b)) := Real.rpow_nonneg (by norm_num) _
    have hsum0 : 0 ≤ ∑' n, y k n := tsum_nonneg fun n => Real.sqrt_nonneg _
    calc ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b))) *
          (ENNReal.ofReal (cubePowerMean k w v)).rpow (1 / (2 * v))
        = ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b)) *
            Real.rpow (cubePowerMean k w v) (1 / (2 * v))) := by
          simp only [ENNReal.rpow_eq_pow]
          rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_rpow_of_nonneg hcpm0 (by positivity)]
          rfl
      _ ≤ ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b)) + ∑' n, y k n) :=
          ENNReal.ofReal_le_ofReal ((besovCubeTerm_le k hw0 hw hv).trans (hX k))
      _ = ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b))) + ∑' n, ENNReal.ofReal (y k n) := by
          rw [ENNReal.ofReal_add hA0 hsum0,
            ENNReal.ofReal_tsum_of_nonneg (fun n => Real.sqrt_nonneg _) (hysum k)]
  unfold besovCubeNorm
  apply ENNReal.pow_lt_top
  calc _ ≤ ∑' k : ℕ, (ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b))) +
          ∑' n, ENNReal.ofReal (y k n)) := ENNReal.tsum_le_tsum hterm
    _ = ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b))) +
          ∑' k : ℕ, ∑' n, ENNReal.ofReal (y k n) := ENNReal.tsum_add
    _ = ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b))) +
          ∑' n, ∑' k : ℕ, ENNReal.ofReal (y k n) := by rw [ENNReal.tsum_comm]
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * b))) +
          ∑' n, ENNReal.ofReal (R n) := by
      gcongr with n
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => Real.sqrt_nonneg _) (hroot n).1]
      exact ENNReal.ofReal_le_ofReal (hroot n).2
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hgeom, hR.tsum_ofReal_lt_top⟩

end CoarseDeGiorgi.SharpnessExamples
