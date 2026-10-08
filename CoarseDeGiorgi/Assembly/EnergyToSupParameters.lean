module

public import CoarseDeGiorgi.Assembly.CaccioppoliParameters

@[expose] public section

namespace CoarseDeGiorgi.Assembly
open Aliases

/-- The exponent range and the exact level compensation `e.level.compensation`. -/
theorem energy_to_sup_parameter_facts {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    0 < paramR q ∧ paramR q < 2 ∧
    2 < rBoundaryParam (d := d) q t ∧
    2 < 2 * rStarParam (d := d) q t / paramR q ∧
    0 < ((d : ℝ) - 1 - 2 * (alphaParam t - betaParam (d := d) q)) /
      (4 * paramTheta d p q s t) ∧
    (((d : ℝ) - 1 - 2 * (alphaParam t - betaParam (d := d) q)) /
      (4 * paramTheta d p q s t)) * (rBoundaryParam (d := d) q t - 2) =
      (alphaParam t - betaParam (d := d) q) / paramTheta d p q s t := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hq1 : 0 < q + 1 := by linarith
  have hr : 0 < paramR q := div_pos (by positivity) hq1
  have hr2 : paramR q < 2 := (div_lt_iff₀ hq1).mpr (by linarith)
  have hm := (caccioppoli_parameter_facts hd hp hq hs ht hθ).1
  have hab : 0 < alphaParam t - betaParam (d := d) q := by
    have : alphaParam t - betaParam (d := d) q = paramTheta d p q s t +
        (sigmaParam (d := d) p q s - betaParam (d := d) q) := by
      unfold alphaParam betaParam paramTheta sigmaParam
      ring
    rw [this]
    positivity
  have hb : 0 < betaParam (d := d) q := by
    unfold betaParam
    exact div_pos (by linarith) (by positivity)
  have ha : 0 < alphaParam t := by linarith
  have ha1 : alphaParam t < 1 := by unfold alphaParam; linarith
  have hprod : alphaParam t * paramR q < 2 :=
    (mul_lt_mul_of_pos_right ha1 hr).trans (by simpa using hr2)
  have hden : 0 < (d : ℝ) - 1 - alphaParam t * paramR q := by linarith
  have hden' : 0 < (d : ℝ) - alphaParam t * paramR q := by linarith
  have hnum : 0 < (d : ℝ) - 1 - 2 * (alphaParam t - betaParam (d := d) q) := by
    have : 0 < betaParam (d := d) q := hb
    linarith
  have heq : (d : ℝ) - 1 - alphaParam t * paramR q =
      q / (q + 1) * ((d : ℝ) - 1 - 2 * (alphaParam t - betaParam (d := d) q)) := by
    unfold paramR betaParam
    field_simp
    ring
  have hboundary : 2 < rBoundaryParam (d := d) q t := by
    unfold rBoundaryParam
    apply (lt_div_iff₀ hden).mpr
    have hh : ((d : ℝ) - 1) * paramR q -
        2 * ((d : ℝ) - 1 - alphaParam t * paramR q) =
        (4 * q / (q + 1)) * (alphaParam t - betaParam (d := d) q) := by
      unfold paramR betaParam
      field_simp
      ring
    have : 0 < (4 * q / (q + 1)) * (alphaParam t - betaParam (d := d) q) := by positivity
    linarith only [hh, this]
  refine ⟨hr, hr2, hboundary, ?_, div_pos hnum (by positivity), ?_⟩
  · unfold rStarParam
    rw [lt_div_iff₀ hr]
    have : (d : ℝ) * paramR q / ((d : ℝ) - alphaParam t * paramR q) > paramR q := by
      apply (lt_div_iff₀ hden').mpr
      have hpos : 0 < alphaParam t * paramR q * paramR q := by positivity
      nlinarith only [hpos]
    linarith only [this]
  · have hbdy : rBoundaryParam (d := d) q t - 2 =
        4 * (alphaParam t - betaParam (d := d) q) /
          ((d : ℝ) - 1 - 2 * (alphaParam t - betaParam (d := d) q)) := by
      dsimp only [rBoundaryParam]
      rw [heq]
      field_simp [hnum.ne', hq0.ne', hq1.ne']
      unfold paramR betaParam
      field_simp
      ring
    rw [hbdy]
    field_simp [hnum.ne', hθ.ne']

end CoarseDeGiorgi.Assembly
