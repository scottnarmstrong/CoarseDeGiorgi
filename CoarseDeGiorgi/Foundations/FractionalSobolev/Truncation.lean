import CoarseDeGiorgi.Foundations.FractionalSobolev.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.MetricSpace.Lipschitz

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- The truncation in DNPV (6.20). -/
def truncate {X : Type*} (f : X → ℝ) (N : ℕ) (x : X) : ℝ :=
  max (min (f x) (N : ℝ)) (-(N : ℝ))

lemma abs_truncate {X : Type*} (f : X → ℝ) (N : ℕ) (x : X) :
    |truncate f N x| = min |f x| (N : ℝ) := by
  unfold truncate
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rcases le_total (f x) 0 with hx | hx
  · rw [min_eq_left (hx.trans hN), abs_of_nonpos hx]
    by_cases h : -(N : ℝ) ≤ f x
    · rw [max_eq_left h, abs_of_nonpos hx, min_eq_left (by linarith)]
    · rw [max_eq_right (le_of_not_ge h), abs_of_nonpos (neg_nonpos.mpr hN),
        neg_neg, min_eq_right (by linarith)]
  · rw [abs_of_nonneg hx, max_eq_left (le_min (by linarith) (by linarith)),
      abs_of_nonneg (le_min hx hN)]

lemma truncate_measurable {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Measurable f) (N : ℕ) : Measurable (truncate f N) :=
  (hf.min measurable_const).max measurable_const

lemma truncate_compact_support {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : HasCompactSupport f) (N : ℕ) : HasCompactSupport (truncate f N) := by
  change HasCompactSupport ((fun t : ℝ => max (min t (N : ℝ)) (-(N : ℝ))) ∘ f)
  apply hf.comp_left
  rw [min_eq_left (show (0 : ℝ) ≤ N from Nat.cast_nonneg N),
    max_eq_left (show -(N : ℝ) ≤ 0 from neg_nonpos.mpr (Nat.cast_nonneg N))]

lemma truncate_difference {X : Type*} (f : X → ℝ) (N : ℕ) (x y : X) :
    |truncate f N x - truncate f N y| ≤ |f x - f y| := by
  have h : LipschitzWith 1 (fun t : ℝ => max (min t (N : ℝ)) (-(N : ℝ))) :=
    (LipschitzWith.id.min_const _).max_const _
  simpa only [truncate, Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul (f x) (f y)

lemma truncate_kernel_le {n : ℕ} {s p : ℝ} (hp : 0 ≤ p)
    (f : Vec n → ℝ) (N : ℕ) (xy : Vec n × Vec n) :
    fracKernel s p (truncate f N) xy ≤ fracKernel s p f xy := by
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (euclidDist_nonneg _ _) _)
  exact Real.rpow_le_rpow (abs_nonneg _) (truncate_difference f N _ _) hp

lemma truncate_energy_le {n : ℕ} {s p : ℝ} (hp : 0 ≤ p)
    (f : Vec n → ℝ) (N : ℕ) :
    (∫⁻ xy : Vec n × Vec n, fracKernel s p (truncate f N) xy ∂(volume.prod volume)) ≤
      ∫⁻ xy : Vec n × Vec n, fracKernel s p f xy ∂(volume.prod volume) :=
  lintegral_mono (truncate_kernel_le hp f N)

/-- DNPV Lemma 6.4, including the case of infinite norm. -/
theorem lemma_6_4 {n : ℕ} {q : ℝ} (hq : 1 ≤ q) {f : Vec n → ℝ}
    (hf : Measurable f) :
    Tendsto (fun N : ℕ => eLpNorm (truncate f N) (ENNReal.ofReal q) volume)
      atTop (𝓝 (eLpNorm f (ENNReal.ofReal q) volume)) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqi : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq0)
  have hnorm : ∀ N, eLpNorm (truncate f N) (ENNReal.ofReal q) volume =
      (∫⁻ x, (ENNReal.ofReal (min |f x| (N : ℝ))) ^ q) ^ (1 / q) := by
    intro N
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqi ENNReal.ofReal_ne_top
      (truncate_measurable hf N).aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
    simp only [Real.enorm_eq_ofReal_abs, abs_truncate]
  have htarget : eLpNorm f (ENNReal.ofReal q) volume =
      (∫⁻ x, (ENNReal.ofReal |f x|) ^ q) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqi ENNReal.ofReal_ne_top
      hf.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
    simp only [Real.enorm_eq_ofReal_abs]
  simp_rw [hnorm]
  rw [htarget]
  apply ((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto _).comp
  apply lintegral_tendsto_of_tendsto_of_monotone
    (f := fun N x => (ENNReal.ofReal (min |f x| (N : ℝ))) ^ q)
    (F := fun x => (ENNReal.ofReal |f x|) ^ q)
  · intro N
    exact ((((continuous_abs.measurable.comp hf).min measurable_const).ennreal_ofReal).pow_const q).aemeasurable
  · apply ae_of_all
    intro x i j hij
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
      (min_le_min_left _ (Nat.cast_le.mpr hij))) hq0.le
  · apply ae_of_all
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge |f x|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with j hj
    rw [min_eq_left (hN.trans (Nat.cast_le.mpr hj))]

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
