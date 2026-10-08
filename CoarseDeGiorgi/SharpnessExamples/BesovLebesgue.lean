module

public import CoarseDeGiorgi.SharpnessExamples.BesovScalarField
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # The Lebesgue norm of the scalar cylinder field

The case of order zero in Theorem F: the field and its inverse lie in `L^ξ` and `L^ζ` of the unit
cube. Minkowski's inequality for the series of cylinder majorants is obtained from the finite
inequality and Fatou's lemma for the Lebesgue seminorm.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Sharpness CoarseDeGiorgi.Foundations.FracGeometry
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- Minkowski's inequality for a pointwise summable series of nonnegative functions. -/
theorem eLpNorm_tsum_le_tsum {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) {f : ℕ → α → ℝ} (hm : ∀ n, AEStronglyMeasurable (f n) μ)
    (hs : ∀ x, Summable (fun n => f n x)) :
    eLpNorm (fun x => ∑' n, f n x) p μ ≤ ∑' n, eLpNorm (f n) p μ := by
  have hpart : ∀ N : ℕ, eLpNorm (fun x => ∑ n ∈ Finset.range N, f n x) p μ ≤
      ∑' n, eLpNorm (f n) p μ := by
    intro N
    have h := eLpNorm_sum_le (μ := μ) (s := Finset.range N) (f := f) hp
    have e : (∑ n ∈ Finset.range N, f n) = fun x => ∑ n ∈ Finset.range N, f n x := by
      funext x; simp [Finset.sum_apply]
    rw [e] at h
    exact h.trans (ENNReal.sum_le_tsum _)
  have hlim := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p) (μ := μ)
    (f := fun N x => ∑ n ∈ Finset.range N, f n x)
    (fun N => Finset.aestronglyMeasurable_fun_sum _ (fun n _ => hm n))
    (fun x => ∑' n, f n x) (AEStronglyMeasurable.tsum hm)
    (Eventually.of_forall fun x => (hs x).hasSum.tendsto_sum_nat)
  refine hlim.trans ?_
  refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
  obtain ⟨N, hN⟩ := hb.exists
  exact hN.trans (hpart N)

private theorem real_cylinder_bound {m : ℕ} {ε L α v : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hL0 : 0 < L) (hv : 1 ≤ v) (hα : α ≤ (m : ℝ) / v) :
    Real.rpow ε (-α) * (((2 * (L * ε)) ^ m) ^ (1 / v)) ≤ Real.rpow (2 * L) ((m : ℝ) / v) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have h1 : ((2 * (L * ε)) ^ m) ^ (1 / v) = (2 * L) ^ ((m : ℝ) / v) * ε ^ ((m : ℝ) / v) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show (2 * (L * ε)) = (2 * L) * ε by ring, Real.mul_rpow (by positivity) hε0.le]
    congr 2 <;> ring
  rw [h1]
  simp only [Real.rpow_eq_pow]
  have h2 : ε ^ (-α) * ε ^ ((m : ℝ) / v) ≤ 1 := by
    rw [← Real.rpow_add hε0]
    exact Real.rpow_le_one hε0.le hε1.le (by linarith)
  have h3 : 0 ≤ (2 * L) ^ ((m : ℝ) / v) := Real.rpow_nonneg (by positivity) _
  calc ε ^ (-α) * ((2 * L) ^ ((m : ℝ) / v) * ε ^ ((m : ℝ) / v))
      = (2 * L) ^ ((m : ℝ) / v) * (ε ^ (-α) * ε ^ ((m : ℝ) / v)) := by ring
    _ ≤ (2 * L) ^ ((m : ℝ) / v) * 1 := mul_le_mul_of_nonneg_left h2 h3
    _ = _ := mul_one _

/-- Each cylinder majorant has small `L^v` norm on the unit cube. -/
theorem majorant_eLpNorm_le {m : ℕ} (hm : 2 ≤ m) {ζ κ α L v : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hκ : 0 < κ) (hL0 : 0 < L) (hL2 : L ≤ 2) (hv : 1 ≤ v) (hα : α ≤ (m : ℝ) / v) (n : ℕ) :
    eLpNorm (scalarMajorantTerm m n ζ κ α L) (ENNReal.ofReal v)
        (volume.restrict (originCube 1)) ≤
      ENNReal.ofReal (Real.rpow (2 * L) ((m : ℝ) / v) * cylinderB n) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hrad := scalarRadius_small (m := m) (k := n) (by omega) hζ0 hζ2 hκ
  set ε := cylinderRadius (m + 1) n ζ κ with hε
  have hLε : L * ε < 1 / 4 := (mul_le_mul_of_nonneg_right hL2 hrad.1.le).trans_lt hrad.2
  have hε1 : ε < 1 := by linarith [hrad.2]
  set T := {x : Vec (m + 1) | transverseNorm (flatJoin 0 (scalarTailCenter m n) - x) < L * ε}
    with hT
  have hTm : MeasurableSet T := cylinderTube_measurable _ _
  set A := cylinderB n * Real.rpow ε (-α) with hA
  have hA0 : 0 ≤ A := mul_nonneg (cylinderB_pos n).le (Real.rpow_nonneg hrad.1.le _)
  have hfun : scalarMajorantTerm m n ζ κ α L = T.indicator (fun _ => A) := by
    funext x
    unfold scalarMajorantTerm
    simp only [Set.indicator, hT, Set.mem_ofPred_eq]
    split_ifs <;> simp [hA, hε]
  have hp0 : ENNReal.ofReal v ≠ 0 := by simpa using hvpos
  have hptop : ENNReal.ofReal v ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [hfun, eLpNorm_indicator_const hTm.nullMeasurableSet hp0 hptop, ENNReal.toReal_ofReal hvpos.le]
  have hvol : (volume.restrict (originCube (d := m + 1) 1)) T =
      volume (averagesCylinder (L * ε) (scalarTailCenter m n)) := by
    rw [Measure.restrict_apply hTm, averagesCylinder, Set.inter_comm]
  have hbd := (averagesCylinder_volume_bounds (L * ε) (scalarTailCenter m n)
    (mul_pos hL0 hrad.1) hLε scalarTailCenter_coord_bound).2
  have hfinite : volume (averagesCylinder (L * ε) (scalarTailCenter m n)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := volume (originCube (d := m + 1) 1))
    · rw [Assembly.ClassicalMomentsImpl.originCube_volume_one]; simp
    · exact measure_mono Set.inter_subset_left
  rw [hvol]
  have hle : volume (averagesCylinder (L * ε) (scalarTailCenter m n)) ≤
      ENNReal.ofReal ((2 * (L * ε)) ^ m) := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hbd
  have hnorm : ‖A‖ₑ = ENNReal.ofReal A := by
    rw [Real.enorm_eq_ofReal hA0]
  rw [hnorm]
  calc ENNReal.ofReal A * volume (averagesCylinder (L * ε) (scalarTailCenter m n)) ^ (1 / v)
      ≤ ENNReal.ofReal A * (ENNReal.ofReal ((2 * (L * ε)) ^ m)) ^ (1 / v) := by
        gcongr
    _ = ENNReal.ofReal (A * (((2 * (L * ε)) ^ m) ^ (1 / v))) := by
        rw [ENNReal.ofReal_mul hA0, ENNReal.ofReal_rpow_of_nonneg
          (pow_nonneg (mul_pos (by norm_num) (mul_pos hL0 hrad.1)).le m)
          (one_div_nonneg.mpr hvpos.le)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have := real_cylinder_bound (m := m) hrad.1 hε1 hL0 hv hα
        calc A * (((2 * (L * ε)) ^ m) ^ (1 / v))
            = cylinderB n * (Real.rpow ε (-α) * (((2 * (L * ε)) ^ m) ^ (1 / v))) := by
              rw [hA]; ring
          _ ≤ cylinderB n * Real.rpow (2 * L) ((m : ℝ) / v) :=
              mul_le_mul_of_nonneg_left this (cylinderB_pos n).le
          _ = _ := by ring

local instance isFiniteMeasure_restrict_originCube {d : ℕ} :
    IsFiniteMeasure (volume.restrict (originCube (d := d) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Assembly.ClassicalMomentsImpl.originCube_volume_one]; simp⟩

/-- A nonnegative function below `1 +` a series of cylinder majorants lies in `L^v`. -/
theorem majorant_lp_lt_top {m : ℕ} (hm : 2 ≤ m) {ζ κ α L v : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hκ : 0 < κ) (hL0 : 0 < L) (hL2 : L ≤ 2) (hv : 1 ≤ v) (hα : α ≤ (m : ℝ) / v)
    (w : Vec (m + 1) → ℝ) (hwm : AEStronglyMeasurable w (volume.restrict (originCube 1)))
    (hw0 : ∀ x, 0 ≤ w x)
    (hmaj : ∀ x, w x ≤ 1 + ∑' n, scalarMajorantTerm m n ζ κ α L x) :
    eLpNorm w (ENNReal.ofReal v) (volume.restrict (originCube 1)) < ⊤ := by
  have hp : 1 ≤ ENNReal.ofReal v := ENNReal.one_le_ofReal.mpr hv
  have hfm : ∀ n, AEStronglyMeasurable (scalarMajorantTerm m n ζ κ α L)
      (volume.restrict (originCube 1)) := fun n =>
    (scalarMajorantTerm_integrable m n ζ κ α L).aestronglyMeasurable
  have hsum : ∀ x, Summable (fun n => scalarMajorantTerm m n ζ κ α L x) := fun x =>
    scalarMajorantTerm_pointwise_summable hm hζ0 hζ2 hκ hL2 x
  have hB : Summable cylinderB := by
    change Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 3))
    simpa only [pow_add] using summable_geometric_two.mul_right ((1 / 2 : ℝ) ^ 3)
  have hF : eLpNorm (fun x => ∑' n, scalarMajorantTerm m n ζ κ α L x) (ENNReal.ofReal v)
      (volume.restrict (originCube 1)) < ⊤ := by
    refine lt_of_le_of_lt (eLpNorm_tsum_le_tsum hp hfm hsum) ?_
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n =>
      majorant_eLpNorm_le hm hζ0 hζ2 hκ hL0 hL2 hv hα n) ?_
    exact (hB.mul_left (Real.rpow (2 * L) ((m : ℝ) / v))).tsum_ofReal_lt_top
  have hle : eLpNorm w (ENNReal.ofReal v) (volume.restrict (originCube 1)) ≤
      eLpNorm (fun x => 1 + ∑' n, scalarMajorantTerm m n ζ κ α L x) (ENNReal.ofReal v)
        (volume.restrict (originCube 1)) := by
    apply eLpNorm_mono hwm
    intro x
    have h0 : 0 ≤ ∑' n, scalarMajorantTerm m n ζ κ α L x :=
      tsum_nonneg fun n => scalarMajorantTerm_nonneg _ _ _ _ _ _ x
    rw [Real.norm_of_nonneg (hw0 x), Real.norm_of_nonneg (by linarith)]
    exact hmaj x
  refine lt_of_le_of_lt hle ?_
  have hadd : eLpNorm ((fun _ : Vec (m + 1) => (1 : ℝ)) +
      fun x => ∑' n, scalarMajorantTerm m n ζ κ α L x) (ENNReal.ofReal v)
      (volume.restrict (originCube 1)) ≤ _ := eLpNorm_add_le hp
  refine lt_of_le_of_lt hadd (ENNReal.add_lt_top.2 ⟨?_, hF⟩)
  exact (memLp_const (1 : ℝ)).eLpNorm_lt_top

/-- A scalar multiple of the identity has the Lebesgue norm of its scalar. -/
theorem eLpNorm_scalar_identity_lt_top {d : ℕ} {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x) {p : ℝ≥0∞}
    {μ : Measure (Vec d)} (hg : eLpNorm g p μ < ⊤) :
    eLpNorm (fun x => ‖g x • (1 : Mat d)‖) p μ < ⊤ := by
  have : (fun x => ‖g x • (1 : Mat d)‖) = ‖(1 : Mat d)‖ • g := by
    funext x
    rw [norm_smul, Real.norm_of_nonneg (hg0 x)]
    simp [mul_comm]
  rw [this, eLpNorm_const_smul]
  exact ENNReal.mul_lt_top (by simp) hg

end

end CoarseDeGiorgi.SharpnessExamples
