module

public import CoarseDeGiorgi.SharpnessExamples.CylinderAveragesGeometry
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

/-- The `v`-moment root of the fractions on one triangulation level. -/
noncomputable def cylinderFractionLevelMoment {n : ℕ} (k : ℕ)
    (epsilon : ℝ) (center : Vec n) (v : ℝ) : ℝ :=
  Real.rpow
    ((((triangulation (d := n + 1) k).attach.sum fun eta =>
        Real.rpow (cylinderFraction (simplexCell k eta) epsilon center) v) /
      ((triangulation (d := n + 1) k).card : ℝ))) (1 / v)

private theorem cylinderPhi_factorization {n : ℕ} {epsilon side v : ℝ}
    (heps : 0 < epsilon) (hv : 1 ≤ v) :
    Real.rpow (epsilon / max epsilon side) ((n : ℝ) * (1 - 1 / v)) *
        Real.rpow (2 * epsilon) ((n : ℝ) / v) =
      Real.rpow 2 ((n : ℝ) / v) *
        Real.rpow epsilon (n : ℝ) *
          Real.rpow (max epsilon side) (-((n : ℝ) * (1 - 1 / v))) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hmax : 0 < max epsilon side := lt_of_lt_of_le heps (le_max_left _ _)
  let a := (n : ℝ) * (1 - 1 / v)
  let b := (n : ℝ) / v
  have hab : a + b = (n : ℝ) := by
    dsimp [a, b]
    field_simp [hvpos.ne']
    ring
  have hmul₁ : Real.rpow (epsilon * (max epsilon side)⁻¹) a =
      Real.rpow epsilon a * Real.rpow ((max epsilon side)⁻¹) a :=
    Real.mul_rpow heps.le (inv_nonneg.mpr hmax.le)
  have hmul₂ : Real.rpow (2 * epsilon) b = Real.rpow 2 b * Real.rpow epsilon b :=
    Real.mul_rpow (by norm_num) heps.le
  have hinv : Real.rpow ((max epsilon side)⁻¹) a =
      Real.rpow (max epsilon side) (-a) := by
    calc
      _ = (Real.rpow (max epsilon side) a)⁻¹ := Real.inv_rpow hmax.le a
      _ = _ := (Real.rpow_neg hmax.le a).symm
  have hEpsPow : Real.rpow epsilon a * Real.rpow epsilon b =
      Real.rpow epsilon (a + b) := (Real.rpow_add heps a b).symm
  calc
    _ = Real.rpow (epsilon * (max epsilon side)⁻¹) a * Real.rpow (2 * epsilon) b := by
      rw [div_eq_mul_inv]
    _ = Real.rpow epsilon a * Real.rpow (max epsilon side) (-a) *
        (Real.rpow 2 b * Real.rpow epsilon b) := by
      rw [hmul₁, hinv, hmul₂]
    _ = Real.rpow 2 b * Real.rpow epsilon (n : ℝ) *
        Real.rpow (max epsilon side) (-a) := by
      calc
        _ = Real.rpow 2 b *
            (Real.rpow epsilon a * Real.rpow epsilon b) *
            Real.rpow (max epsilon side) (-a) := by ring
        _ = _ := by rw [hEpsPow, hab]
    _ = _ := rfl

/-- Upper cell-fraction moment bound in the scale form used in
Lemma `l.sharpness.cylinder.averages`. -/
theorem cylinderFraction_level_moment_upper {n : ℕ}
    {epsilon : ℝ} (heps : 0 < epsilon) (heps4 : epsilon < 1 / 4)
    (center : Vec n) (hcenter : ∀ i, |center i| ≤ 1 / 4)
    (v : ℝ) (hv : 1 ≤ v) (k : ℕ) :
    cylinderFractionLevelMoment k epsilon center v ≤
      Real.rpow ((Nat.factorial (n + 1) : ℝ) * (2 : ℝ) ^ (n + 1))
          (1 - 1 / v) *
        Real.rpow 2 ((n : ℝ) / v) * cylinderPhi n v epsilon k := by
  classical
  let side : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let L : ℝ := max epsilon side
  let K : ℝ := (Nat.factorial (n + 1) : ℝ) * (2 : ℝ) ^ (n + 1)
  let f : SimplexIndex (n + 1) k → ℝ := fun eta =>
    cylinderFraction (simplexCell k eta) epsilon center
  have hside : 0 < side := by dsimp [side]; positivity
  have hL : 0 < L := by dsimp [L]; exact lt_of_lt_of_le heps (le_max_left _ _)
  have hK : 1 ≤ K := by
    dsimp [K]
    have hfact : 1 ≤ (Nat.factorial (n + 1) : ℝ) := by
      have hf : 0 < Nat.factorial (n + 1) := Nat.factorial_pos _
      exact_mod_cast (Nat.succ_le_iff.mpr hf)
    have hpow : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hfnonneg (eta : SimplexIndex (n + 1) k) : 0 ≤ f eta :=
    (cylinderSimplex_fraction_bounds epsilon center eta).1
  have hfunit (eta : SimplexIndex (n + 1) k) : f eta ≤ 1 :=
    (cylinderSimplex_fraction_bounds epsilon center eta).2
  have hfbound (eta : SimplexIndex (n + 1) k) :
      f eta ≤ K * (epsilon / L) ^ n := by
    by_cases hsideleps : side ≤ epsilon
    · have hLval : L = epsilon := by dsimp [L]; exact max_eq_left hsideleps
      rw [hLval]
      have heq : epsilon / epsilon = 1 := div_self heps.ne'
      rw [heq, one_pow]
      exact (hfunit eta).trans (by dsimp [K]; nlinarith [hK])
    · have hepsside : epsilon ≤ side := le_of_not_ge hsideleps
      have hLval : L = side := by dsimp [L]; exact max_eq_right hepsside
      rw [hLval]
      have hbound := cylinderSimplex_fraction_coarse_bound heps.le center eta
      dsimp [K, side]
      exact hbound
  have hNpos : 0 < ((triangulation (d := n + 1) k).card : ℝ) := by
    exact_mod_cast CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.triangulation_card_pos _ _
  have hmean : ((triangulation (d := n + 1) k).attach.sum fun eta => f eta) /
      ((triangulation (d := n + 1) k).card : ℝ) =
      (volume (averagesCylinder epsilon center)).toReal := by
    simpa [f] using cylinderFraction_level_sum k epsilon center
  have hvol : (volume (averagesCylinder epsilon center)).toReal ≤ (2 * epsilon) ^ n :=
    (averagesCylinder_volume_bounds epsilon center heps heps4 hcenter).2
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hvsub : 0 ≤ v - 1 := by linarith
  let cap : ℝ := K * (epsilon / L) ^ n
  have hcap : 0 < cap := by dsimp [cap]; positivity
  have hcapPow : 0 ≤ Real.rpow cap (v - 1) := Real.rpow_nonneg hcap.le _
  have hterm (eta : SimplexIndex (n + 1) k) :
      Real.rpow (f eta) v ≤ f eta * Real.rpow cap (v - 1) := by
    have hfi := hfnonneg eta
    have hfc := hfbound eta
    by_cases hfz : f eta = 0
    · simp [hfz, Real.zero_rpow, hvpos.ne']
    · have hfp : 0 < f eta := lt_of_le_of_ne hfi (Ne.symm hfz)
      have hsplit : Real.rpow (f eta) v =
        f eta * Real.rpow (f eta) (v - 1) := by
        calc
          _ = Real.rpow (f eta) (1 + (v - 1)) :=
            congrArg (Real.rpow (f eta)) (by ring)
          _ = Real.rpow (f eta) 1 * Real.rpow (f eta) (v - 1) :=
            Real.rpow_add hfp _ _
          _ = _ := by
            exact congrArg (fun z : ℝ => z * Real.rpow (f eta) (v - 1))
              (Real.rpow_one (f eta))
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hfi hfc hvsub) hfi
  have hsumPow : ((triangulation (d := n + 1) k).attach.sum fun eta =>
      Real.rpow (f eta) v) ≤ Real.rpow cap (v - 1) *
      ((triangulation (d := n + 1) k).attach.sum fun eta => f eta) := by
    calc
      _ ≤ (triangulation (d := n + 1) k).attach.sum
          (fun eta => f eta * Real.rpow cap (v - 1)) :=
        Finset.sum_le_sum fun eta _ => hterm eta
      _ = ((triangulation (d := n + 1) k).attach.sum fun eta => f eta) *
          Real.rpow cap (v - 1) := by
        rw [Finset.sum_mul]
      _ = _ := by ring
  have hmeanPow :
      ((triangulation (d := n + 1) k).attach.sum fun eta => Real.rpow (f eta) v) /
        ((triangulation (d := n + 1) k).card : ℝ) ≤
        Real.rpow cap (v - 1) * (volume (averagesCylinder epsilon center)).toReal := by
    calc
      _ ≤ (Real.rpow cap (v - 1) *
          ((triangulation (d := n + 1) k).attach.sum fun eta => f eta)) /
          ((triangulation (d := n + 1) k).card : ℝ) :=
        div_le_div_of_nonneg_right hsumPow hNpos.le
      _ = Real.rpow cap (v - 1) *
          (((triangulation (d := n + 1) k).attach.sum fun eta => f eta) /
            ((triangulation (d := n + 1) k).card : ℝ)) := by ring
      _ = _ := by rw [hmean]
  have hmeanPowNonneg :
      0 ≤ ((triangulation (d := n + 1) k).attach.sum fun eta =>
        Real.rpow (f eta) v) / ((triangulation (d := n + 1) k).card : ℝ) := by
    apply div_nonneg
    · exact Finset.sum_nonneg fun eta _ => Real.rpow_nonneg (hfnonneg eta) _
    · exact hNpos.le
  have hroot := Real.rpow_le_rpow hmeanPowNonneg hmeanPow (by positivity : 0 ≤ 1 / v)
  have hexp : (v - 1) * (1 / v) = 1 - 1 / v := by
    field_simp [hvpos.ne']
  have hrootFactor :
      Real.rpow (Real.rpow cap (v - 1) *
        (volume (averagesCylinder epsilon center)).toReal) (1 / v) =
      Real.rpow cap (1 - 1 / v) *
        Real.rpow ((volume (averagesCylinder epsilon center)).toReal) (1 / v) := by
    calc
      _ = Real.rpow (Real.rpow cap (v - 1)) (1 / v) *
          Real.rpow ((volume (averagesCylinder epsilon center)).toReal) (1 / v) :=
        Real.mul_rpow hcapPow ENNReal.toReal_nonneg
      _ = Real.rpow cap ((v - 1) * (1 / v)) *
          Real.rpow ((volume (averagesCylinder epsilon center)).toReal) (1 / v) := by
        exact congrArg (fun z => z *
          Real.rpow ((volume (averagesCylinder epsilon center)).toReal) (1 / v))
          (Real.rpow_mul hcap.le (v - 1) (1 / v)).symm
      _ = _ := by rw [hexp]
  have hvolRoot :
      Real.rpow ((volume (averagesCylinder epsilon center)).toReal) (1 / v) ≤
        Real.rpow ((2 * epsilon) ^ n) (1 / v) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hvol (by positivity)
  have hcapFactor : Real.rpow cap (1 - 1 / v) =
      Real.rpow K (1 - 1 / v) *
        Real.rpow (epsilon / L) ((n : ℝ) * (1 - 1 / v)) := by
    dsimp [cap]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [(Real.rpow_natCast_mul (x := epsilon / L) (by positivity) n
      (1 - 1 / v)).symm]
  have hvolumeFactor : Real.rpow ((2 * epsilon) ^ n) (1 / v) =
      Real.rpow (2 * epsilon) ((n : ℝ) / v) := by
    calc
      _ = Real.rpow (2 * epsilon) ((n : ℝ) * (1 / v)) :=
        (Real.rpow_natCast_mul (x := 2 * epsilon) (by positivity) n (1 / v)).symm
      _ = _ := by congr 1; ring
  have hscale :
      Real.rpow (epsilon / L) ((n : ℝ) * (1 - 1 / v)) *
        Real.rpow (2 * epsilon) ((n : ℝ) / v) =
          Real.rpow 2 ((n : ℝ) / v) * cylinderPhi n v epsilon k := by
    have hfactor := cylinderPhi_factorization (n := n) (side := side) heps hv
    dsimp [L, side] at hfactor ⊢
    calc
      _ = Real.rpow 2 ((n : ℝ) / v) * Real.rpow epsilon (n : ℝ) *
          Real.rpow (max epsilon ((3 : ℝ) ^ (-(k : ℤ))))
            (-((n : ℝ) * (1 - 1 / v))) := hfactor
      _ = _ := by dsimp [cylinderPhi]; ring_nf
  dsimp [cylinderFractionLevelMoment, f]
  calc
    _ = Real.rpow
        ((((triangulation (d := n + 1) k).attach.sum fun eta =>
          Real.rpow (cylinderFraction (simplexCell k eta) epsilon center) v) /
          ((triangulation (d := n + 1) k).card : ℝ))) (1 / v) := rfl
    _ ≤ Real.rpow (Real.rpow cap (v - 1) *
          (volume (averagesCylinder epsilon center)).toReal) (1 / v) := hroot
    _ = Real.rpow cap (1 - 1 / v) *
          Real.rpow ((volume (averagesCylinder epsilon center)).toReal) (1 / v) := hrootFactor
    _ ≤ Real.rpow cap (1 - 1 / v) * Real.rpow ((2 * epsilon) ^ n) (1 / v) :=
      mul_le_mul_of_nonneg_left hvolRoot (Real.rpow_nonneg hcap.le _)
    _ = Real.rpow K (1 - 1 / v) *
        (Real.rpow (epsilon / L) ((n : ℝ) * (1 - 1 / v)) *
          Real.rpow (2 * epsilon) ((n : ℝ) / v)) := by
      rw [hcapFactor, hvolumeFactor]
      ring_nf
    _ = Real.rpow K (1 - 1 / v) *
        (Real.rpow 2 ((n : ℝ) / v) * cylinderPhi n v epsilon k) := by
      rw [hscale]
    _ = _ := by
      have hKeq : K = (Nat.factorial (n + 1) : ℝ) * (2 : ℝ) ^ n * 2 := by
        dsimp [K]
        rw [pow_succ]
        ring
      have hExp : (n : ℝ) / v = (1 / v) * (n : ℝ) := by
        field_simp [hvpos.ne']
      rw [hKeq, hExp]
      let baseL := (Nat.factorial (n + 1) : ℝ) * (2 : ℝ) ^ n * 2
      let baseR := (Nat.factorial (n + 1) : ℝ) * (2 : ℝ) ^ (n + 1)
      have hbase : baseL = baseR := by
        dsimp [baseL, baseR]
        rw [pow_succ]
        ring
      have hpowbase : Real.rpow baseL (1 - 1 / v) =
          Real.rpow baseR (1 - 1 / v) :=
        congrArg (fun x : ℝ => Real.rpow x (1 - 1 / v)) hbase
      change Real.rpow baseL (1 - 1 / v) *
          (Real.rpow 2 ((1 / v) * (n : ℝ)) * cylinderPhi n v epsilon k) =
        Real.rpow baseR (1 - 1 / v) * Real.rpow 2 ((1 / v) * (n : ℝ)) *
          cylinderPhi n v epsilon k
      rw [hpowbase]
      ring

end CoarseDeGiorgi.SharpnessExamples
