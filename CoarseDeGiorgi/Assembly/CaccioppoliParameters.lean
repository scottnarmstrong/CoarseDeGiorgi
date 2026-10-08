import CoarseDeGiorgi.Assembly.CaccioppoliDefs
import Mathlib.Tactic

namespace CoarseDeGiorgi.Assembly

open Aliases

/-- Positivity and smallness of the exponents used to choose the collar. -/
theorem caccioppoli_parameter_facts {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    0 < sigmaParam (d := d) p q s - betaParam (d := d) q ∧
      paramTheta d p q s t < 1 ∧
      1 < gammaTwoParam (d := d) p q t ∧
      0 < kappaParam (d := d) p q s t := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : 0 < (d : ℝ) - 1 := by linarith only [hd3]
  have hsum : 0 < 1 / p + 1 / q := add_pos (one_div_pos.mpr hp0) (one_div_pos.mpr hq0)
  have hb : 0 < ((d : ℝ) - 1) / (2 * q) := div_pos hd0 (mul_pos (by norm_num) hq0)
  have hm : sigmaParam (d := d) p q s - betaParam (d := d) q =
      s + ((d : ℝ) - 1) / (2 * p) := by
    unfold sigmaParam betaParam
    field_simp
    ring
  have hmpos : 0 < sigmaParam (d := d) p q s - betaParam (d := d) q := by
    rw [hm]
    exact add_pos hs (div_pos hd0 (mul_pos (by norm_num) hp0))
  have hθlt : paramTheta d p q s t < 1 := by
    unfold paramTheta
    have hc := mul_pos (div_pos hd0 (by norm_num : (0 : ℝ) < 2)) hsum
    linarith only [hs, ht, hc]
  have ha : 0 < alphaParam t := by
    have hid : paramTheta d p q s t +
        (sigmaParam (d := d) p q s - betaParam (d := d) q) +
          betaParam (d := d) q = alphaParam t := by
      unfold paramTheta sigmaParam betaParam alphaParam
      ring
    have hb' : 0 < betaParam (d := d) q := hb
    linarith only [hid, hθ, hmpos, hb']
  have hg : 1 < gammaTwoParam (d := d) p q t := by
    have hg1 : alphaParam t ≤ gammaOneParam (d := d) q t := le_max_left _ _
    have hp' : 0 < 1 / (2 * p) := one_div_pos.mpr (mul_pos (by norm_num) hp0)
    have hq' : 0 < 1 / (2 * q) := one_div_pos.mpr (mul_pos (by norm_num) hq0)
    unfold gammaTwoParam
    linarith only [ha, hg1, hp', hq']
  have hab : 0 < alphaParam t - betaParam (d := d) q := by
    have hid : alphaParam t - betaParam (d := d) q =
      paramTheta d p q s t + (sigmaParam (d := d) p q s - betaParam (d := d) q) := by
      unfold alphaParam betaParam paramTheta sigmaParam
      ring
    rw [hid]
    exact add_pos hθ hmpos
  refine ⟨hmpos, hθlt, hg, ?_⟩
  exact div_pos (mul_pos (mul_pos (by norm_num) (lt_trans zero_lt_one hg)) hab) hθ


end CoarseDeGiorgi.Assembly
