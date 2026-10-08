module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.CrossoverExponent
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import Homogenization.CoarseGraining.ResponseIdentities.Foundations.Algebra
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Crossover

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- The moment-range hypotheses make the contrast finite, as required by the
real-valued crossover exponent. -/
theorem contrast_lt_top_of_spatialMomentRange {d : ℕ}
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (s t p q : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hrange : spatialMomentRange a ha p q s t) :
    contrast a ha s t p q hs ht hp hq < ⊤ := by
  rcases hrange with ⟨hp', hq', hs', ht', _, _, _, _, _, hupper, hlower⟩
  have hupper' : upperMoment a ha s p hs hp < ⊤ := by simpa using hupper
  have hlower' : 0 < lowerMoment a ha t q ht hq := by simpa using hlower
  exact ENNReal.div_lt_top hupper'.ne (pos_iff_ne_zero.mp hlower')

/-- The normalization of `U ^ p` by the exponential of `p` times the mean of `log U`
(step of `l.crossover`). -/
def centeredWeight {d : ℕ} (V : Set (Vec d)) (U : Vec d → ℝ)
    (p : ℝ) : Vec d → ℝ :=
  fun x => Real.exp (-p * volumeAverage V (fun y => Real.log (U y))) * (U x) ^ p

/-- The reciprocal normalization of the negative power `U ^ (-p)`. -/
def centeredWeightInv {d : ℕ} (V : Set (Vec d)) (U : Vec d → ℝ)
    (p : ℝ) : Vec d → ℝ :=
  fun x => Real.exp (p * volumeAverage V (fun y => Real.log (U y))) * (U x) ^ (-p)

/-- For every `c ≥ 0`, the crossover exponent times `√Θ` is at most `c`
(the choice `e.small.exponent`). -/
theorem crossoverExponent_sqrt_le {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s t p q : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hΘtop : contrast a ha s t p q hs ht hp hq < ⊤)
    (c : ℝ) (hc : 0 ≤ c) :
    crossoverExponent c a ha s t p q hs ht hp hq *
      Real.sqrt (contrast a ha s t p q hs ht hp hq).toReal ≤ c := by
  let θ : ℝ≥0∞ := contrast a ha s t p q hs ht hp hq
  let X : ℝ≥0∞ := 1 + θ
  have hX1 : 1 ≤ X := by dsimp [X, θ]; exact le_add_right le_rfl
  have hXtop : X < ⊤ := by
    dsimp [X, θ]
    exact ENNReal.add_lt_top.mpr ⟨by simp, hΘtop⟩
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX1
  have hθreal : 0 ≤ θ.toReal := ENNReal.toReal_nonneg
  have hθleX : θ ≤ X := by dsimp [X]; exact le_add_left le_rfl
  have hquot : θ / X ≤ 1 := (ENNReal.div_le_iff hXpos.ne' hXtop.ne).2 (by simpa using hθleX)
  have hkle : X.rpow (-(1 / 2 : ℝ)) ≤ 1 :=
    ENNReal.rpow_le_one_of_one_le_of_neg hX1 (by norm_num)
  have hktop : X.rpow (-(1 / 2 : ℝ)) < ⊤ := lt_of_le_of_lt hkle ENNReal.one_lt_top
  have hkfactor : (X.rpow (-(1 / 2 : ℝ))) ^ 2 * θ ≤ 1 := by
    have hksq : (X.rpow (-(1 / 2 : ℝ))) ^ 2 = X.rpow (-1 : ℝ) := by
      calc
        _ = (X.rpow (-(1 / 2 : ℝ))).rpow (2 : ℝ) :=
          (ENNReal.rpow_two (X.rpow (-(1 / 2 : ℝ)))).symm
        _ = X.rpow (-1 : ℝ) := by
          change (X ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) = X ^ (-1 : ℝ)
          rw [← ENNReal.rpow_mul]
          norm_num
    calc
      _ = X.rpow (-1 : ℝ) * θ := by rw [hksq]
      _ = θ / X := by
        rw [ENNReal.rpow_eq_pow, ENNReal.rpow_neg_one, div_eq_mul_inv]
        ac_rfl
      _ ≤ 1 := hquot
  have hkfactorReal : (X.rpow (-(1 / 2 : ℝ))).toReal ^ 2 * θ.toReal ≤ 1 := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top hkfactor
  have hpcSq :
      (crossoverExponent c a ha s t p q hs ht hp hq * Real.sqrt θ.toReal) ^ 2 ≤ c ^ 2 := by
    rw [CoarseDeGiorgi.crossoverExponent, mul_pow, Real.sq_sqrt hθreal]
    calc
      _ = c ^ 2 * ((X.rpow (-(1 / 2 : ℝ))).toReal ^ 2 * θ.toReal) := by
        ring
      _ ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left hkfactorReal (sq_nonneg c)
      _ = c ^ 2 := mul_one _
  have hpcNonneg :
      0 ≤ crossoverExponent c a ha s t p q hs ht hp hq * Real.sqrt θ.toReal :=
    mul_nonneg (mul_nonneg hc (ENNReal.toReal_nonneg)) (Real.sqrt_nonneg _)
  exact (sq_le_sq₀ hpcNonneg hc).mp hpcSq

/-- The logarithm of the normalized weight is `p` times the centered logarithm of `U`. -/
theorem centeredWeight_log {d : ℕ} (V : Set (Vec d)) (U : Vec d → ℝ)
    (p : ℝ) {x : Vec d} (hU : 0 < U x) :
    Real.log (centeredWeight V U p x) =
      p * (Real.log (U x) - volumeAverage V (fun y => Real.log (U y))) := by
  rw [centeredWeight, Real.log_mul (Real.exp_ne_zero _)
      (ne_of_gt (Real.rpow_pos_of_pos hU _)),
    Real.log_exp, Real.log_rpow hU]
  ring

/-- The inverse weight has the opposite centered logarithm. -/
theorem centeredWeightInv_log {d : ℕ} (V : Set (Vec d)) (U : Vec d → ℝ)
    (p : ℝ) {x : Vec d} (hU : 0 < U x) :
    Real.log (centeredWeightInv V U p x) =
      -p * (Real.log (U x) - volumeAverage V (fun y => Real.log (U y))) := by
  rw [centeredWeightInv, Real.log_mul (Real.exp_ne_zero _)
      (ne_of_gt (Real.rpow_pos_of_pos hU _)),
    Real.log_exp, Real.log_rpow hU]
  ring

/-- The mean absolute centered logarithm is at most one for either sign whenever
the joint log/exponent witness supplies `c C₂ ≤ 1`. -/
theorem centeredWeight_log_average_bound {d : ℕ} (V : Set (Vec d))
    (U : Vec d → ℝ) (p c C₂ : ℝ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (s t p₀ q : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hp₀ : 1 ≤ p₀) (hq : 1 ≤ q)
    (hΘtop : contrast a ha s t p₀ q hs ht hp₀ hq < ⊤)
    (hc : 0 ≤ c) (hC₂ : 0 ≤ C₂)
    (hp : p = crossoverExponent c a ha s t p₀ q hs ht hp₀ hq)
    (hcc : c * C₂ ≤ 1)
    (hcenter : volumeAverage V
      (fun x => |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) ≤
        C₂ * Real.sqrt
          (contrast a ha s t p₀ q hs ht hp₀ hq).toReal)
    (hU : ∀ᵐ x ∂(volume.restrict V), 0 < U x) :
    volumeAverage V (fun x => |Real.log (centeredWeight V U p x)|) ≤ 1 ∧
      volumeAverage V (fun x => |Real.log (centeredWeightInv V U p x)|) ≤ 1 := by
  have hp0 : 0 ≤ p := by
    rw [hp]
    exact mul_nonneg hc ENNReal.toReal_nonneg
  have hps : p * Real.sqrt
      (contrast a ha s t p₀ q hs ht hp₀ hq).toReal ≤ c := by
    rw [hp]
    exact crossoverExponent_sqrt_le a ha s t p₀ q hs ht hp₀ hq hΘtop c hc
  have hweight_ae : (fun x => |Real.log (centeredWeight V U p x)|) =ᵐ[
      volume.restrict V]
      fun x => p * |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))| := by
    filter_upwards [hU] with x hx
    rw [centeredWeight_log V U p hx, abs_mul, abs_of_nonneg hp0]
  have hinv_ae : (fun x => |Real.log (centeredWeightInv V U p x)|) =ᵐ[
      volume.restrict V]
      fun x => p * |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))| := by
    filter_upwards [hU] with x hx
    rw [centeredWeightInv_log V U p hx, abs_mul]
    simp [abs_of_nonneg hp0]
  have havg_weight : volumeAverage V (fun x => |Real.log (centeredWeight V U p x)|) =
      p * volumeAverage V
        (fun x => |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) := by
    calc
      volumeAverage V (fun x => |Real.log (centeredWeight V U p x)|) =
          volumeAverage V (fun x => p *
            |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) := by
        unfold volumeAverage
        congr 1
        exact integral_congr_ae hweight_ae
      _ = p * volumeAverage V
          (fun x => |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) := by
        rw [show (fun x => p * |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) =
          p • (fun x => |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) by
            funext x; simp [smul_eq_mul]]
        exact volumeAverage_smul V p _
  have havg_inv : volumeAverage V (fun x => |Real.log (centeredWeightInv V U p x)|) =
      p * volumeAverage V
        (fun x => |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) := by
    calc
      volumeAverage V (fun x => |Real.log (centeredWeightInv V U p x)|) =
          volumeAverage V (fun x => p *
            |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) := by
        unfold volumeAverage
        congr 1
        exact integral_congr_ae hinv_ae
      _ = p * volumeAverage V
          (fun x => |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) := by
        rw [show (fun x => p * |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) =
          p • (fun x => |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) by
            funext x; simp [smul_eq_mul]]
        exact volumeAverage_smul V p _
  rw [havg_weight, havg_inv]
  constructor
  · calc
      p * volumeAverage V
          (fun x => |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) ≤
          p * (C₂ * Real.sqrt
            (contrast a ha s t p₀ q hs ht hp₀ hq).toReal) :=
              mul_le_mul_of_nonneg_left hcenter hp0
      _ = C₂ * (p * Real.sqrt
        (contrast a ha s t p₀ q hs ht hp₀ hq).toReal) := by ring
      _ ≤ C₂ * c := mul_le_mul_of_nonneg_left hps hC₂
      _ = c * C₂ := mul_comm _ _
      _ ≤ 1 := hcc
  · calc
      p * volumeAverage V
          (fun x => |Real.log (U x) - volumeAverage V (fun y => Real.log (U y))|) ≤
          p * (C₂ * Real.sqrt
            (contrast a ha s t p₀ q hs ht hp₀ hq).toReal) :=
              mul_le_mul_of_nonneg_left hcenter hp0
      _ = C₂ * (p * Real.sqrt
        (contrast a ha s t p₀ q hs ht hp₀ hq).toReal) := by ring
      _ ≤ C₂ * c := mul_le_mul_of_nonneg_left hps hC₂
      _ = c * C₂ := mul_comm _ _
      _ ≤ 1 := hcc

end
end CoarseDeGiorgi.Harnack.Crossover
