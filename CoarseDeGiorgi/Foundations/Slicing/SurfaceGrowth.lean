import CoarseDeGiorgi.Foundations.FracGeometry.FaceHausdorff
import CoarseDeGiorgi.Foundations.Slicing.AnnularTail

/-! Euclidean ball growth and uniform exterior kernel tails for cube surfaces. -/

namespace CoarseDeGiorgi.Foundations.Slicing

open Homogenization MeasureTheory Set Metric FracGeometry
open scoped BigOperators ENNReal

noncomputable section

/-- Coordinate faces have dimension-only polynomial growth in Euclidean balls. -/
theorem faceMeasure_euclid_ball_le {n : ℕ} (τ : ℝ) (i : Fin (n + 1)) (pos : Bool)
    (x : Vec (n + 1)) {R : ℝ} (hR : 0 < R) :
    faceMeasure τ i pos {y | Euclid.eDist2 x y < R} ≤ ENNReal.ofReal ((2 * R) ^ n) := by
  let c : ℝ := if pos then τ / 2 else -τ / 2
  let f : Vec n → Vec (n + 1) := fun u => i.insertNth c u
  have hf : Measurable f := (isometry_insertNth i c).continuous.measurable
  have hball : MeasurableSet {y | Euclid.eDist2 x y < R} :=
    measurableSet_lt (Euclid.continuous_eDist2.measurable.comp
      (measurable_const.prodMk measurable_id)) measurable_const
  calc
    _ ≤ (Measure.map f volume) {y | Euclid.eDist2 x y < R} :=
      faceMeasure_le_map_insertNth τ i pos _
    _ = volume (f ⁻¹' {y | Euclid.eDist2 x y < R}) := Measure.map_apply hf hball
    _ ≤ volume (ball (i.removeNth x) R) := by
      apply measure_mono
      intro u hu
      change Euclid.eDist2 x (f u) < R at hu
      rw [mem_ball, dist_eq_norm]
      apply lt_of_le_of_lt ?_ hu
      calc
        ‖u - i.removeNth x‖ ≤ ‖x - f u‖ := by
          apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
          intro j
          have h := norm_le_pi_norm (x - f u) (i.succAbove j)
          simpa only [Pi.sub_apply, f, Fin.insertNth_apply_succAbove,
            Fin.removeNth_apply, norm_sub_rev] using h
        _ ≤ Euclid.eDist2 x (f u) := Euclid.norm_le_eNorm2 _
    _ = _ := by rw [Real.volume_pi_ball _ hR, Fintype.card_fin]

/-- Sum over the `2d` coordinate faces; no exponent occurs in the growth constant. -/
theorem surfaceMeasure_euclid_ball_le {n : ℕ} (τ : ℝ) (x : Vec (n + 1))
    {R : ℝ} (hR : 0 < R) :
    CoarseDeGiorgi.surfaceMeasure τ {y | Euclid.eDist2 x y < R} ≤
      ENNReal.ofReal ((2 * (n + 1 : ℕ) : ℝ) * (2 * R) ^ n) := by
  rw [CoarseDeGiorgi.surfaceMeasure]
  simp only [Measure.finsetSum_apply]
  calc
    _ ≤ ∑ _i : Fin (n + 1), ∑ _pos : Bool, ENNReal.ofReal ((2 * R) ^ n) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun pos _ =>
        faceMeasure_euclid_ball_le τ i pos x hR
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
      ring

/-- The exterior surface kernel tail, uniform in every nonnegative extra decay. -/
theorem surface_kernel_tail_le {n : ℕ} (τ : ℝ) (x : Vec (n + 1))
    {γ R : ℝ} (hγ : 0 ≤ γ) (hR : 0 < R) :
    (∫⁻ y in {y | R < Euclid.eDist2 x y},
      ENNReal.ofReal (Euclid.eDist2 x y ^ (-(2 * (n : ℝ) + 1 + γ)))
      ∂CoarseDeGiorgi.surfaceMeasure τ) ≤
      ENNReal.ofReal (4 * (n + 1 : ℕ) * (2 : ℝ) ^ (2 * (n : ℝ)) *
        R ^ (-((n : ℝ) + 1 + γ))) := by
  have hg : Measurable (fun y => Euclid.eDist2 x y) :=
    Euclid.continuous_eDist2.measurable.comp (measurable_const.prodMk measurable_id)
  have hgrowth (T : ℝ) (hT : 0 < T) :
      CoarseDeGiorgi.surfaceMeasure τ {y | Euclid.eDist2 x y < T} ≤
      ENNReal.ofReal ((2 * (n + 1 : ℕ) * (2 : ℝ) ^ (n : ℝ)) * T ^ (n : ℝ)) := by
    have h := surfaceMeasure_euclid_ball_le τ x hT
    rw [← Real.rpow_natCast, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT.le] at h
    convert h using 2
    ring
  have ht := lintegral_tail_le_of_growth (CoarseDeGiorgi.surfaceMeasure τ) hg
    (K := 2 * (n + 1 : ℕ) * (2 : ℝ) ^ (n : ℝ))
    (m := n) (q := 2 * (n : ℝ) + 1 + γ)
    (by positivity) (Nat.cast_nonneg n)
    (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n), hγ]) hR hgrowth
  rw [show (n : ℝ) - (2 * (n : ℝ) + 1 + γ) = -((n : ℝ) + 1 + γ) by ring] at ht
  refine ht.trans_eq ?_
  congr 1
  rw [show 2 * (n : ℝ) = (n : ℝ) + n by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  ring

end

end CoarseDeGiorgi.Foundations.Slicing
