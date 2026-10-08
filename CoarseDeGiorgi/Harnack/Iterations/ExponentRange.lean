module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.RStarParam

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Iterations

open Homogenization MeasureTheory
open scoped ENNReal

/-- The crossover exponent `p_c = c (1 + Θ)^(-1/2)` has the required range for every admissible
scalar `c`, given the contrast bounds `1 ≤ Θ < ⊤` supplied by `e.moment.comparison`.
-/
theorem ruled_exponent_range_of_moment_comparison {d : ℕ} (hd : 3 ≤ d)
    (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hΘ : 1 ≤ contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq) ∧
      contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq) < ⊤)
    (c : ℝ) (hc : 0 < c)
    (hcrange : c ≤ min (1 / 2) (paramR q /
      (16 * (rStarParam (d := d) q t / paramR q)))) :
    let p_c := c * ((1 + contrast a ha s t p q hs ht
      (le_of_lt hp) (le_of_lt hq)).rpow (-(1 / 2 : ℝ))).toReal
    0 < p_c ∧ p_c ≤ c ∧ p_c < paramR q / 4 ∧
      2 * c / paramR q < 1 ∧ 1 ≤ (contrast a ha s t p q hs ht
        (le_of_lt hp) (le_of_lt hq)).toReal ∧
      p_c ^ 2 * (contrast a ha s t p q hs ht
        (le_of_lt hp) (le_of_lt hq)).toReal ≤ c ^ 2 := by
  dsimp only
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hr : 0 < paramR q := by
    unfold paramR
    exact div_pos (by positivity) (by linarith)
  have hr1 : 1 < paramR q := by
    unfold paramR
    rw [lt_div_iff₀ (by linarith : 0 < q + 1)]
    linarith only [hq]
  have hr2 : paramR q < 2 := by
    unfold paramR
    rw [div_lt_iff₀ (by linarith : 0 < q + 1)]
    linarith only [hq]
  have hα : 0 < alphaParam t := by
    have hterm : 0 ≤ (((d : ℝ) - 1) / 2) * (1 / p + 1 / q) := by
      have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
      positivity
    unfold paramTheta at hθ
    unfold alphaParam
    linarith only [hθ, hterm, hs]
  have hα1 : alphaParam t < 1 := by
    unfold alphaParam
    linarith
  have hαr : 0 < alphaParam t * paramR q := mul_pos hα hr
  have hd' : 3 ≤ (d : ℝ) := by exact_mod_cast hd
  have hαr_lt2 : alphaParam t * paramR q < 2 := by
    calc
      alphaParam t * paramR q < 1 * paramR q :=
        mul_lt_mul_of_pos_right hα1 hr
      _ = paramR q := one_mul _
      _ < 2 := hr2
  have hden : 0 < (d : ℝ) - alphaParam t * paramR q := by
    have hd' : 2 < (d : ℝ) := by exact_mod_cast (show 2 < d by omega)
    linarith only [hd', hαr_lt2]
  have hχ : 1 < rStarParam (d := d) q t / paramR q := by
    rw [rStarParam]
    have hcancel :
        (((d : ℝ) * paramR q) / ((d : ℝ) - alphaParam t * paramR q)) /
            paramR q = (d : ℝ) / ((d : ℝ) - alphaParam t * paramR q) := by
      field_simp [ne_of_gt hr, ne_of_gt hden]
    rw [hcancel]
    exact (lt_div_iff₀ hden).2 (by linarith only [hαr])
  have hcχ : c ≤ paramR q /
      (16 * (rStarParam (d := d) q t / paramR q)) := (le_min_iff.mp hcrange).2
  have hdenχ : 16 < 16 * (rStarParam (d := d) q t / paramR q) := by
    have hmul := mul_lt_mul_of_pos_left hχ (show 0 < (16 : ℝ) by norm_num)
    simpa only [mul_one] using hmul
  have hc16 : c < paramR q / 16 :=
    lt_of_le_of_lt hcχ
      (div_lt_div_of_pos_left hr (by norm_num) hdenχ)
  have hratio : c / paramR q < 1 / 16 := by
    calc
      c / paramR q < (paramR q / 16) / paramR q :=
        div_lt_div_of_pos_right hc16 hr
      _ = 1 / 16 := by field_simp
  have hcquarter : c < paramR q / 4 := by
    exact hc16.trans (by
      calc
        paramR q / 16 = paramR q * (1 / 16) := by ring
        _ < paramR q * (1 / 4) :=
          mul_lt_mul_of_pos_left (by norm_num : (1 / 16 : ℝ) < 1 / 4) hr
        _ = paramR q / 4 := by ring)
  have hcsmall : 2 * c / paramR q < 1 := by
    rw [div_lt_one hr]
    linarith [hc16]
  let θ : ℝ≥0∞ := contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)
  let X : ℝ≥0∞ := 1 + θ
  have hX1 : 1 ≤ X := by
    dsimp [X, θ]
    exact le_add_right le_rfl
  have hXtop : X < ⊤ := by
    dsimp [X, θ]
    exact ENNReal.add_lt_top.mpr ⟨by simp, hΘ.2⟩
  have hXpos : 0 < X := by
    exact lt_of_lt_of_le (by norm_num) hX1
  have hkpos : 0 < X.rpow (-(1 / 2 : ℝ)) :=
    ENNReal.rpow_pos hXpos hXtop.ne
  have hkle : X.rpow (-(1 / 2 : ℝ)) ≤ 1 :=
    ENNReal.rpow_le_one_of_one_le_of_neg hX1 (by norm_num)
  have hktop : X.rpow (-(1 / 2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt hkle ENNReal.one_lt_top
  have hkrealpos : 0 < (X.rpow (-(1 / 2 : ℝ))).toReal :=
    ENNReal.toReal_pos hkpos.ne' hktop.ne
  have hkreal_le : (X.rpow (-(1 / 2 : ℝ))).toReal ≤ 1 :=
    ENNReal.toReal_mono ENNReal.one_ne_top hkle
  have hΘreal : 1 ≤ θ.toReal := by
    simpa using ENNReal.toReal_mono hΘ.2.ne hΘ.1
  have hθleX : θ ≤ X := by
    dsimp [X]
    exact le_add_left le_rfl
  have hquot : θ / X ≤ 1 :=
    (ENNReal.div_le_iff hXpos.ne' hXtop.ne).2 (by simpa using hθleX)
  have hksq : (X.rpow (-(1 / 2 : ℝ))) ^ 2 = X.rpow (-1 : ℝ) := by
    calc
      _ = (X.rpow (-(1 / 2 : ℝ))).rpow (2 : ℝ) :=
        (ENNReal.rpow_two (X.rpow (-(1 / 2 : ℝ)))).symm
      _ = X.rpow (-1 : ℝ) := by
        change (X ^ (-(1 / 2 : ℝ))) ^ (2 : ℝ) = X ^ (-1 : ℝ)
        rw [← ENNReal.rpow_mul]
        norm_num
  have hfactor : (X.rpow (-(1 / 2 : ℝ))) ^ 2 * θ ≤ 1 := by
    calc
      _ = X.rpow (-1 : ℝ) * θ := by rw [hksq]
      _ = θ / X := by
        rw [ENNReal.rpow_eq_pow, ENNReal.rpow_neg_one, div_eq_mul_inv]
        ac_rfl
      _ ≤ 1 := hquot
  have hfactorReal :
      (X.rpow (-(1 / 2 : ℝ))).toReal ^ 2 * θ.toReal ≤ 1 := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top hfactor
  have hpcTheta :
      (c * (X.rpow (-(1 / 2 : ℝ))).toReal) ^ 2 * θ.toReal ≤ c ^ 2 := by
    calc
      _ = c ^ 2 * ((X.rpow (-(1 / 2 : ℝ))).toReal ^ 2 * θ.toReal) := by ring
      _ ≤ c ^ 2 := mul_le_of_le_one_right (sq_nonneg c) hfactorReal
  refine ⟨mul_pos hc hkrealpos, ?_, ?_, hcsmall, hΘreal, ?_⟩
  · exact mul_le_of_le_one_right hc.le hkreal_le
  · exact (mul_le_of_le_one_right hc.le hkreal_le).trans_lt hcquarter
  · exact hpcTheta

end CoarseDeGiorgi.Harnack.Iterations
