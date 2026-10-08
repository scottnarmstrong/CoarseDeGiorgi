import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.TwoLevelQuantity
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Assembly.ParameterDefs
import CoarseDeGiorgi.Statements.RBoundaryParam
import CoarseDeGiorgi.Statements.RStarParam
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Assembly.EnergyToSupParameters

namespace CoarseDeGiorgi.Assembly.Hybrid


/-- The standing source assumptions put both embeddings in their critical ranges. -/
theorem embedding_parameter_facts {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    0 < alphaParam t ∧ alphaParam t < 1 ∧
      1 < paramR q ∧ paramR q < 2 ∧
      alphaParam t * paramR q < (d : ℝ) - 1 ∧
      alphaParam t * paramR q < (d : ℝ) ∧
      2 < rBoundaryParam (d := d) q t ∧
      paramR q < rStarParam (d := d) q t := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hq1 : 0 < q + 1 := by linarith only [hq]
  have hr1 : 1 < paramR q := by
    unfold paramR
    rw [lt_div_iff₀ hq1]
    linarith only [hq]
  obtain ⟨hr0, hr2, hb, hstar, _, _⟩ :=
    energy_to_sup_parameter_facts hd hp hq hs ht hθ
  have hm := (caccioppoli_parameter_facts hd hp hq hs ht hθ).1
  have hβ : 0 < betaParam (d := d) q := by
    unfold betaParam
    exact div_pos (by linarith only [hd3]) (by positivity)
  have hid : alphaParam t = paramTheta d p q s t +
      (sigmaParam (d := d) p q s - betaParam (d := d) q) + betaParam (d := d) q := by
    unfold alphaParam paramTheta sigmaParam betaParam
    ring
  have hα : 0 < alphaParam t := by rw [hid]; exact add_pos (add_pos hθ hm) hβ
  have hα1 : alphaParam t < 1 := by unfold alphaParam; linarith only [ht]
  have hprod : alphaParam t * paramR q < 2 :=
    (mul_lt_mul_of_pos_right hα1 hr0).trans (by simpa only [one_mul] using hr2)
  refine ⟨hα, hα1, hr1, hr2, by linarith only [hprod, hd3],
    by linarith only [hprod, hd3], hb, ?_⟩
  have h := (lt_div_iff₀ hr0).mp hstar
  change 2 * paramR q < 2 * rStarParam (d := d) q t at h
  linarith only [h]

/-- The finite-cover Hölder loss is exactly d/(2q), not an extra radius loss. -/
theorem localization_exponent_identity {d : ℕ} {q : ℝ} (hq : 1 < q) :
    (d : ℝ) * (1 - paramR q / 2) = (d : ℝ) / (2 * q) * paramR q := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  have hq1 : q + 1 ≠ 0 := by linarith only [hq]
  unfold paramR
  field_simp [hq0, hq1]
  ring

/-- Both losses of inner localization are bounded by γ₁. -/
theorem localization_exponent_bounds {d : ℕ} {q t : ℝ} (hq : 1 < q) :
    alphaParam t ≤ gammaOneParam (d := d) q t ∧
      (d : ℝ) * (1 - paramR q / 2) ≤ gammaOneParam (d := d) q t * paramR q := by
  refine ⟨le_max_left _ _, ?_⟩
  rw [localization_exponent_identity hq]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by
    unfold paramR
    exact div_nonneg (by linarith only [hq]) (by linarith only [hq]))

end CoarseDeGiorgi.Assembly.Hybrid
