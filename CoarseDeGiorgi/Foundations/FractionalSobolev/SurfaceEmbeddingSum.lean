import CoarseDeGiorgi.Foundations.FractionalSobolev.SurfaceEmbeddingNorms

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section

lemma embedding_rpow_sum_le {ι : Type*} (S : Finset ι) (a : ι → ℝ≥0∞) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) : (∑ i ∈ S, a i) ^ t ≤ ∑ i ∈ S, a i ^ t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, ENNReal.zero_rpow_of_pos ht, le_refl]
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (ENNReal.rpow_add_le_add_rpow _ _ ht.le ht1).trans (add_le_add le_rfl ih)

/-- The critical norm on the sum of face measures is at most the sum of face norms. -/
lemma embedding_surface_lp_le_sum {d : ℕ} {q : ℝ} (hq : 1 ≤ q)
    {g : Vec d → ℝ} (hg : Measurable g) (τ : ℝ) :
    eLpNorm g (ENNReal.ofReal q) (surfaceMeasure τ) ≤
      ∑ i : Fin d, ∑ pos : Bool, eLpNorm g (ENNReal.ofReal q) (cubeFaceMeasure τ i pos) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hroot : 0 < 1 / q := one_div_pos.mpr hq0
  have hroot1 : 1 / q ≤ 1 := (div_le_one hq0).mpr hq
  have hn (μ : Measure (Vec d)) : eLpNorm g (ENNReal.ofReal q) μ =
      (∫⁻ x, (ENNReal.ofReal |g x|) ^ q ∂μ) ^ (1/q) := by
    rw [← lp_power_integral hg.aestronglyMeasurable hq0, ← ENNReal.rpow_mul,
      mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  rw [hn, surfaceMeasure]
  simp_rw [lintegral_finsetSum_measure]
  calc
    _ ≤ ∑ i : Fin d, (∑ pos : Bool, ∫⁻ x, (ENNReal.ofReal |g x|) ^ q ∂cubeFaceMeasure τ i pos) ^ (1/q) :=
      embedding_rpow_sum_le _ _ hroot hroot1
    _ ≤ ∑ i : Fin d, ∑ pos : Bool, (∫⁻ x, (ENNReal.ofReal |g x|) ^ q ∂cubeFaceMeasure τ i pos) ^ (1/q) :=
      Finset.sum_le_sum (fun _ _ => embedding_rpow_sum_le _ _ hroot hroot1)
    _ = _ := by simp_rw [← hn]

lemma embedding_lp_le_fracNorm {n : ℕ} (V : Set (Vec n)) (α : ℝ) {r : ℝ}
    (hr : 0 < r) (f : Vec n → ℝ) :
    eLpNorm f (ENNReal.ofReal r) (volume.restrict V) ≤ fracNorm V α r f := by
  apply (ENNReal.rpow_le_rpow_iff hr).mp
  rw [fracNorm_power _ _ hr]
  exact le_add_right le_rfl

lemma embedding_semi_le_fracNorm {n : ℕ} (V : Set (Vec n)) (α : ℝ) {r : ℝ}
    (hr : 0 < r) (f : Vec n → ℝ) : fracSeminorm V α r f ≤ fracNorm V α r f := by
  apply (ENNReal.rpow_le_rpow_iff hr).mp
  rw [fracNorm_power _ _ hr]
  exact le_add_left le_rfl

/-- Finite surface area gives the L² consequence with a constant independent of τ. -/
lemma embedding_surface_ltwo_le {d : ℕ} (hd : 1 ≤ d) {q τ : ℝ}
    (hq : 2 ≤ q) (hτ : τ ≤ 1) {g : Vec d → ℝ} (hg : Measurable g) :
    eLpNorm g 2 (surfaceMeasure τ) ≤
      (2 * d : ℝ≥0∞) * eLpNorm g (ENNReal.ofReal q) (surfaceMeasure τ) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hδ : 0 ≤ 1 / 2 - 1 / q := by
    have hi := (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hq)
    linarith
  have hδ1 : 1 / 2 - 1 / q ≤ 1 := by
    have hi := (one_div_pos.mpr hq0).le
    linarith only [hi]
  have harea : surfaceMeasure (d := d) τ univ ≤ (2 * d : ℝ≥0∞) := by
    exact FracGeometry.surfaceMeasure_univ_le hτ
  have hbase : (1 : ℝ≥0∞) ≤ 2 * d := by
    exact_mod_cast (by omega : 1 ≤ 2 * d)
  have hc : surfaceMeasure (d := d) τ univ ^ (1/2 - 1/q) ≤ (2 * d : ℝ≥0∞) :=
    (ENNReal.rpow_le_rpow harea hδ).trans
      (by simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le hbase hδ1)
  have hpq : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hq
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := surfaceMeasure τ) hpq hg.aestronglyMeasurable
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hq0.le] at h
  have hm := mul_le_mul' (le_refl (eLpNorm g (ENNReal.ofReal q) (surfaceMeasure τ))) hc
  exact h.trans (by simpa only [mul_comm] using hm)

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
