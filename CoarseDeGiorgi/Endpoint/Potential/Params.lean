module

public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.RStarParam
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.AuxCube
public import CoarseDeGiorgi.LowerFractional.CubeDomain
public import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Potential

open Homogenization MeasureTheory

theorem one_lt_paramR {q : ℝ} (hq : 1 < q) : 1 < paramR q := by
  unfold paramR
  rw [lt_div_iff₀ (by linarith)]; linarith

theorem paramR_lt_two {q : ℝ} (hq : 1 < q) : paramR q < 2 := by
  unfold paramR
  rw [div_lt_iff₀ (by linarith)]; linarith

theorem lt_one_of_paramTheta_pos {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q)
    (hs : 0 < s) (h : 0 < paramTheta d p q s t) : t < 1 := by
  unfold paramTheta at h
  have hd' : (0 : ℝ) < ((d : ℝ) - 1) / 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have : 0 < (1 / p + 1 / q) := by positivity
  have := mul_pos hd' this
  linarith

/-- The exponent identities of the endpoint parameters, for `0 < t < 1`. -/
theorem rStar_facts {d : ℕ} (hd : 3 ≤ d) {q t : ℝ} (hq : 1 < q) (ht : 0 < t) (ht1 : t < 1) :
    0 < (d : ℝ) / rStarParam (d := d) q t ∧ 1 < rStarParam (d := d) q t ∧
    (d : ℝ) / rStarParam (d := d) q t + (1 - t) = (d : ℝ) / paramR q ∧
    (d : ℝ) / rStarParam (d := d) q t * rStarParam (d := d) q t = d ∧
    paramR q < rStarParam (d := d) q t := by
  have hr1 := one_lt_paramR hq
  have hr2 := paramR_lt_two hq
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set r := paramR q with hr
  have hD : 0 < (d : ℝ) - (1 - t) * r := by nlinarith
  have hrs : rStarParam (d := d) q t = (d : ℝ) * r / ((d : ℝ) - (1 - t) * r) := by
    unfold rStarParam alphaParam; rfl
  have hrs_pos : 0 < rStarParam (d := d) q t := by rw [hrs]; positivity
  have hlt : r < rStarParam (d := d) q t := by
    rw [hrs, lt_div_iff₀ hD]
    nlinarith [mul_pos (sub_pos.2 ht1) (mul_pos (by linarith : 0 < r) (by linarith : 0 < r))]
  refine ⟨?_, by linarith, ?_, ?_, hlt⟩
  · positivity
  · rw [hrs]; field_simp; ring
  · field_simp

theorem originCube_one_domain {d : ℕ} :
    IsOpenBoundedConvexDomain (originCube (d := d) 1) ∧ (originCube (d := d) 1).Nonempty := by
  have hcube : originCube (d := d) 1 = auxCube 1 (fun _ : Fin d => 0) := by
    ext x
    simp [originCube, auxCube, sub_self, sub_zero, Int.cast_zero, zero_mul, abs_lt]
  rw [hcube]
  exact ⟨LowerFractional.auxCube_isOpenBoundedConvexDomain (d := d) 1 (fun _ => 0),
    LowerFractional.auxCube_nonempty (d := d) 1 (fun _ => 0)⟩

end CoarseDeGiorgi.Endpoint.Potential
