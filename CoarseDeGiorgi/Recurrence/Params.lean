import CoarseDeGiorgi.Assembly.EnergyToSupParameters
import CoarseDeGiorgi.Statements.GammaRec
import CoarseDeGiorgi.Statements.GammaSup
import CoarseDeGiorgi.Statements.GammaLoc
import CoarseDeGiorgi.Statements.SigmaLower
import CoarseDeGiorgi.Statements.SigmaUpper

namespace CoarseDeGiorgi.Recurrence

open CoarseDeGiorgi

/-- `1 - σ_* = α - β`. -/
theorem alpha_sub_beta_eq {d : ℕ} (q t : ℝ) :
    alphaParam t - betaParam (d := d) q = 1 - sigmaLower d q t := by
  unfold alphaParam betaParam sigmaLower
  ring

/-- `d - 1 - 2(α - β) = d - 3 + 2σ_*`. -/
theorem mu_numerator_eq {d : ℕ} (q t : ℝ) :
    (d : ℝ) - 1 - 2 * (alphaParam t - betaParam (d := d) q) =
      (d : ℝ) - 3 + 2 * sigmaLower d q t := by
  unfold alphaParam betaParam sigmaLower
  ring

/-- Exponent range and the level compensation `μ (r_∂^* - 2) = (1 - σ_*)/θ`. -/
theorem sup_parameter_facts {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    0 < paramR q ∧ paramR q < 2 ∧
    2 < rBoundaryParam (d := d) q t ∧
    2 < 2 * rStarParam (d := d) q t / paramR q ∧
    0 < ((d : ℝ) - 3 + 2 * sigmaLower d q t) / (4 * paramTheta d p q s t) ∧
    (((d : ℝ) - 3 + 2 * sigmaLower d q t) / (4 * paramTheta d p q s t)) *
      (rBoundaryParam (d := d) q t - 2) =
      (1 - sigmaLower d q t) / paramTheta d p q s t := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Assembly.energy_to_sup_parameter_facts hd hp hq hs ht hθ
  rw [mu_numerator_eq] at h5 h6
  rw [alpha_sub_beta_eq] at h6
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- `γ₃ > 0`. -/
theorem gammaRec_pos {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) : 0 < gammaRec d p q s t := by
  obtain ⟨hr, hr2, hb, hc, -, -⟩ := sup_parameter_facts hd hp hq hs ht hθ
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have ht1 : t < 1 := by
    unfold paramTheta at hθ
    have hd1 : 0 ≤ (d : ℝ) - 1 := by linarith only [hd3]
    have h1 : 0 ≤ (((d : ℝ) - 1) / 2) * (1 / p + 1 / q) := by positivity
    linarith only [hθ, hs, h1]
  have hα : 0 < alphaParam t := by
    unfold alphaParam
    linarith only [ht1]
  have hl : 0 < gammaLoc p q t := by
    unfold gammaLoc
    have : 0 < 1 / (2 * p) := by positivity
    have : 0 < 1 / (2 * q) := by positivity
    linarith only [ht1, ‹0 < 1 / (2 * p)›, ‹0 < 1 / (2 * q)›]
  have hσ : 0 < sigmaUpper d p s := by
    unfold sigmaUpper
    have : 0 ≤ ((d : ℝ) - 1) / (2 * p) := by
      apply div_nonneg <;> linarith only [hd3, hp0]
    linarith only [hs, this]
  unfold gammaRec
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  have h1 : 0 < 1 / p := by positivity
  have h2 : 0 < (alphaParam t + 1 / paramR q) * rBoundaryParam (d := d) q t := by
    have : 0 < 1 / paramR q := by positivity
    have : 0 < rBoundaryParam (d := d) q t := by linarith only [hb]
    positivity
  have h3 : 0 < 2 * gammaLoc p q t * sigmaUpper d p s / paramTheta d p q s t := by positivity
  linarith only [h1, h2, h3]

end CoarseDeGiorgi.Recurrence
