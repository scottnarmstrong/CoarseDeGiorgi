module

public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.BesovCubeNorm

public import CoarseDeGiorgi.CoefficientConditions.BesovSeries

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem moment_bounds_besov (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hA : ∀ i j, Integrable (fun x => a x i j) (volume.restrict (originCube 1)))
    (hAinv : ∀ i j, Integrable (fun x => (a x)⁻¹ i j) (volume.restrict (originCube 1)))
    (_hap : besovCubeNorm a hA s p hs hp.le < ⊤)
    (_haq : besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le < ⊤) :
    upperMoment a ha s p hs hp.le ≤
        ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-s)) ^ 2) *
          besovCubeNorm a hA s p hs hp.le ∧
      (lowerMoment a ha t q ht hq.le)⁻¹ ≤
        ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-t)) ^ 2) *
          besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le ∧
      contrast a ha s t p q hs ht hp.le hq.le ≤
        ENNReal.ofReal ((d.factorial : ℝ) ^ 2) *
          besovCubeNorm a hA s p hs hp.le *
          besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le
:=
  by
  have hU := CoarseDeGiorgi.CoefficientConditions.upper_le a ha hA hs hp.le
  have hL := CoarseDeGiorgi.CoefficientConditions.lower_le a ha hAinv ht hq.le
  refine ⟨hU, hL, ?_⟩
  have hs1 : Real.rpow 3 (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)
  have ht1 : Real.rpow 3 (-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht)
  have hs0 : 0 ≤ Real.rpow 3 (-s) := Real.rpow_nonneg (by norm_num) _
  have ht0 : 0 ≤ Real.rpow 3 (-t) := Real.rpow_nonneg (by norm_num) _
  have hf : (0 : ℝ) ≤ d.factorial := Nat.cast_nonneg _
  have hconst : ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-s)) ^ 2) *
      ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-t)) ^ 2) ≤
      ENNReal.ofReal ((d.factorial : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (1 - Real.rpow 3 (-s)) ^ 2 ≤ 1 := by nlinarith
    have h2 : (1 - Real.rpow 3 (-t)) ^ 2 ≤ 1 := by nlinarith
    have h3 : 0 ≤ (1 - Real.rpow 3 (-s)) ^ 2 := sq_nonneg _
    have h4 : 0 ≤ (1 - Real.rpow 3 (-t)) ^ 2 := sq_nonneg _
    have h5 : (1 - Real.rpow 3 (-s)) ^ 2 * (1 - Real.rpow 3 (-t)) ^ 2 ≤ 1 := by
      nlinarith
    calc (d.factorial : ℝ) * (1 - Real.rpow 3 (-s)) ^ 2 *
          ((d.factorial : ℝ) * (1 - Real.rpow 3 (-t)) ^ 2)
        = (d.factorial : ℝ) ^ 2 * ((1 - Real.rpow 3 (-s)) ^ 2 * (1 - Real.rpow 3 (-t)) ^ 2) := by
          ring
      _ ≤ (d.factorial : ℝ) ^ 2 * 1 := mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = _ := mul_one _
  unfold contrast
  rw [div_eq_mul_inv]
  calc upperMoment a ha s p hs hp.le * (lowerMoment a ha t q ht hq.le)⁻¹
      ≤ (ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-s)) ^ 2) *
          besovCubeNorm a hA s p hs hp.le) *
        (ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-t)) ^ 2) *
          besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le) := mul_le_mul' hU hL
    _ = (ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-s)) ^ 2) *
        ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-t)) ^ 2)) *
        besovCubeNorm a hA s p hs hp.le *
          besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le := by ring
    _ ≤ ENNReal.ofReal ((d.factorial : ℝ) ^ 2) *
        besovCubeNorm a hA s p hs hp.le *
          besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq.le := by gcongr

end CoarseDeGiorgi
