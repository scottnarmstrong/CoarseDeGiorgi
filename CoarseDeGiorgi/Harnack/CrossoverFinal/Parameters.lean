module

public import CoarseDeGiorgi.Harnack.Moments.MomentComparison
public import CoarseDeGiorgi.Statements.ChiParam
public import CoarseDeGiorgi.Statements.RStarParam
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta

@[expose] public section

namespace CoarseDeGiorgi.Harnack.CrossoverFinal

open Homogenization MeasureTheory
open scoped ENNReal

/-- The spatial moment assumptions imply the contrast bound Θ ≥ 1 needed in the
crossover, through the whole-cube moment comparison `e.moment.comparison`. -/
theorem contrast_ge_one_of_spatialMomentRange {d : ℕ} (hd : 3 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hrange : spatialMomentRange a ha p q s t) :
    1 ≤ contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq) := by
  rcases hrange with ⟨_, _, _, _, _, _, _, _, _, hupper, hlower⟩
  exact Harnack.Moments.moment_contrast_ge_one (by omega) a ha hs ht
    (le_of_lt hp) (le_of_lt hq) (by simpa using hupper) (by simpa using hlower)

/-- The parameter hypotheses imply χ > 1, hence the range `0 < c ≤ min (1 / 2) (r / (16 χ))`
for the constant of the small exponent `e.small.exponent` has a positive upper endpoint. -/
theorem chiParam_gt_one_of_source_parameters {d : ℕ} (hd : 3 ≤ d)
    (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    1 < chiParam d q t := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hr0 : 0 < paramR q := by
    unfold paramR
    exact div_pos (by positivity) (by linarith)
  have hr1 : 1 < paramR q := by
    unfold paramR
    rw [lt_div_iff₀ (by linarith : 0 < q + 1)]
    nlinarith
  have hr2 : paramR q < 2 := by
    unfold paramR
    rw [div_lt_iff₀ (by linarith : 0 < q + 1)]
    nlinarith
  have hα0 : 0 < alphaParam t := by
    have hterm : 0 ≤ (((d : ℝ) - 1) / 2) * (1 / p + 1 / q) := by
      have hd' : 1 ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
      positivity
    unfold paramTheta at hθ
    unfold alphaParam
    nlinarith
  have hα1 : alphaParam t < 1 := by
    unfold alphaParam
    linarith
  have hαr : 0 < alphaParam t * paramR q := mul_pos hα0 hr0
  have hd' : 3 ≤ (d : ℝ) := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - alphaParam t * paramR q := by
    nlinarith [mul_lt_mul_of_pos_right hα1 hr0]
  have hχ : 1 < rStarParam (d := d) q t / paramR q := by
    rw [rStarParam]
    have hcancel :
        (((d : ℝ) * paramR q) /
          ((d : ℝ) - alphaParam t * paramR q)) / paramR q =
            (d : ℝ) / ((d : ℝ) - alphaParam t * paramR q) := by
      field_simp [ne_of_gt hr0, ne_of_gt hden]
    rw [hcancel]
    apply (lt_div_iff₀ hden).2
    nlinarith
  simpa [chiParam] using hχ

/-- Choose a parameter-only `c ≤ min (1 / 2) (r / (16 χ))` (`e.small.exponent`) with
`c C₂ ≤ 1` for the log-center constant `C₂`. -/
theorem exists_crossover_parameter {d : ℕ} (hd : 3 ≤ d)
    (p q s t C₂ : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) (hC₂ : 0 ≤ C₂) :
    ∃ c : ℝ, 0 < c ∧
      c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) ∧ c * C₂ ≤ 1 := by
  have hr0 : 0 < paramR q := by
    unfold paramR
    exact div_pos (by positivity) (by linarith)
  have hχ : 1 < chiParam d q t :=
    chiParam_gt_one_of_source_parameters hd p q s t hp hq hs ht hθ
  have hcap : 0 < min (1 / 2) (paramR q / (16 * chiParam d q t)) := by
    positivity
  let c := min (min (1 / 2) (paramR q / (16 * chiParam d q t))) (1 / (1 + C₂))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc, ?_, ?_⟩
  · exact min_le_left _ _
  · have hcBound : c ≤ 1 / (1 + C₂) := min_le_right _ _
    have hmul : c * C₂ ≤ C₂ / (1 + C₂) := by
      simpa [div_eq_mul_inv, one_div, mul_comm] using
        (mul_le_mul_of_nonneg_right hcBound hC₂)
    have hratio : C₂ / (1 + C₂) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    exact hmul.trans hratio

end CoarseDeGiorgi.Harnack.CrossoverFinal
