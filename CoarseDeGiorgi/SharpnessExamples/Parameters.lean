import CoarseDeGiorgi.Sharpness.Defs
import CoarseDeGiorgi.Foundations.Euclid.Basic
import Mathlib

open Homogenization
open CoarseDeGiorgi.Sharpness

namespace CoarseDeGiorgi.SharpnessExamples

/-- The positive-side exponent allowed by the first coefficient norm. -/
noncomputable def exponentA (d : ℕ) (p s : ℝ) : ℝ :=
  ((d : ℝ) - 1) / p + 2 * s

/-- The positive-side exponent allowed by the inverse coefficient norm. -/
noncomputable def exponentB (d : ℕ) (q t : ℝ) : ℝ :=
  ((d : ℝ) - 1) / q + 2 * t

/-- Below the critical line, choose a scalar-cylinder exponent satisfying both
coefficient norm constraints and the strict bounds zero and two. -/
theorem exists_cylinderExponent {d : ℕ} (hd : 3 ≤ d) {p q s t θ : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hθdef : θ = 1 - s - t - ((d : ℝ) - 1) / 2 * (1 / p + 1 / q))
    (hθ : θ ≤ 0) :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 2 ∧ ζ ≤ exponentA d p s ∧
      2 - ζ ≤ exponentB d q t := by
  let A := exponentA d p s
  let B := exponentB d q t
  have hdR : (2 : ℝ) ≤ (d : ℝ) - 1 := by
    have h : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hApos : 0 < A := by
    dsimp [A, exponentA]
    positivity
  have hBpos : 0 < B := by
    dsimp [B, exponentB]
    positivity
  have hsumEq : A + B = 2 - 2 * θ := by
    dsimp [A, B, exponentA, exponentB]
    rw [hθdef]
    ring
  have hsum : 2 ≤ A + B := by rw [hsumEq]; linarith
  let ζ := max (min A 1) (2 - B)
  have hminpos : 0 < min A 1 := lt_min hApos (by norm_num)
  have hminlt : min A 1 < 2 := (min_le_right A 1).trans_lt (by norm_num)
  have hsecondlt : 2 - B < 2 := by linarith
  have hζlt : ζ < 2 := max_lt_iff.mpr ⟨hminlt, hsecondlt⟩
  have hsecondleA : 2 - B ≤ A := by linarith
  have hζleA : ζ ≤ A := max_le_iff.mpr ⟨min_le_left A 1, hsecondleA⟩
  have hζpos : 0 < ζ := hminpos.trans_le (le_max_left _ _)
  have hζB : 2 - ζ ≤ B := by linarith [le_max_right (min A 1) (2 - B)]
  exact ⟨ζ, hζpos, hζlt, hζleA, hζB⟩

/-- Positive exponent gap in the thin-cylinder energy estimate. -/
def cylinderNu (d : ℕ) (ζ : ℝ) : ℝ := (d : ℝ) - 1 - ζ

theorem cylinderNu_pos {d : ℕ} (hd : 3 ≤ d) {ζ : ℝ} (hζ : ζ < 2) :
    0 < cylinderNu d ζ := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) - 1 := by
    have h : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  dsimp [cylinderNu]
  linarith

/-- The radial normalization in the annular profile. This is the reciprocal
of `∫₁² r^(2-d) dr`, written in closed form. -/
noncomputable def cylinderRadialConstant (d : ℕ) : ℝ :=
  if d = 3 then (Real.log 2)⁻¹ else
    ((d : ℝ) - 3) / (1 - Real.rpow 2 (3 - (d : ℝ)))

theorem cylinderRadialConstant_pos {d : ℕ} (hd : 3 ≤ d) :
    0 < cylinderRadialConstant d := by
  unfold cylinderRadialConstant
  split_ifs with h
  · exact inv_pos.mpr (Real.log_pos (by norm_num))
  · have hd4 : 4 ≤ d := by omega
    have hdR : (3 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 3 < d)
    have hexp : 3 - (d : ℝ) < 0 := by linarith
    have hpow : Real.rpow 2 (3 - (d : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
    have hnum : 0 < (d : ℝ) - 3 := by linarith
    exact div_pos hnum (by linarith)

/-- Dyadic amplitudes, indexed from zero so index n corresponds to source
index j = n + 1. -/
noncomputable def cylinderB (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 3)

theorem cylinderB_pos (n : ℕ) : 0 < cylinderB n := by
  dsimp [cylinderB]
  positivity

/-- Transverse centers embedded into Fin d → ℝ; the first transverse
coordinate is coordinate one in the ambient space. -/
def cylinderCenter {d : ℕ} (b : ℝ) : Vec d :=
  fun i => if i.val = 1 then b else 0

/-- The first transverse coordinate in dimensions at least two. -/
def cylinderCoordOne {d : ℕ} (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩

/-- Axial growth rate of the cylinder profile. -/
noncomputable def cylinderRate (d n : ℕ) (κ : ℝ) : ℝ :=
  Real.sqrt (((d : ℝ) - 1) * κ) / cylinderB n

/-- The power threshold that guarantees summability of the profile norms. -/
noncomputable def cylinderTail (d n : ℕ) (κ : ℝ) : ℝ :=
  (((1 / 2 : ℝ) ^ (n + 1) * cylinderB n) /
    (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (cylinderRate d n κ)))

/-- A small radius chosen uniformly for the field, norm, and energy estimates.
The auxiliary `κ` will be the positive radial normalization constant. -/
noncomputable def cylinderRadius (d n : ℕ) (ζ κ : ℝ) : ℝ :=
  min (cylinderB n / (32 * (1 + Real.sqrt κ)))
    (min (Real.rpow (cylinderB n) (1 / ζ))
      (min (Real.rpow (cylinderB n) (1 / (2 - ζ)))
        (Real.rpow (cylinderTail d n κ) (1 / cylinderNu d ζ))))

/-- All small-radius inequalities used in the construction hold for the
explicit radius above. The slack in the first inequality is reserved for
separating neighboring cylinders. -/
theorem cylinderRadius_data {d n : ℕ} (hd : 3 ≤ d) {ζ κ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) :
    0 < cylinderRadius d n ζ κ ∧
      cylinderRadius d n ζ κ < cylinderB n / (16 * (1 + Real.sqrt κ)) ∧
      1 ≤ cylinderB n * Real.rpow (cylinderRadius d n ζ κ) (-ζ) ∧
      (cylinderB n)⁻¹ * Real.rpow (cylinderRadius d n ζ κ) (2 - ζ) ≤ 1 ∧
      (((n + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (cylinderRate d n κ) * (cylinderB n)⁻¹ *
        Real.rpow (cylinderRadius d n ζ κ) (cylinderNu d ζ) ≤
        (1 / 2 : ℝ) ^ (n + 1) := by
  let b := cylinderB n
  let j : ℝ := (n + 1 : ℕ)
  let rate := cylinderRate d n κ
  let tail := cylinderTail d n κ
  let ε := cylinderRadius d n ζ κ
  have hb : 0 < b := cylinderB_pos n
  have hdR : 0 ≤ (d : ℝ) - 1 := by
    have h : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hrate : 0 ≤ rate := by
    dsimp [rate, cylinderRate]
    positivity
  have hj : 0 < j := by dsimp [j]; positivity
  have htail : 0 < tail := by
    dsimp [tail, cylinderTail, j, rate, cylinderRate]
    positivity
  have hnu : 0 < cylinderNu d ζ := cylinderNu_pos hd hζ2
  have hcoreRoot : 0 < Real.rpow b (1 / ζ) := Real.rpow_pos_of_pos hb _
  have hannRoot : 0 < Real.rpow b (1 / (2 - ζ)) := Real.rpow_pos_of_pos hb _
  have htailRoot : 0 < Real.rpow tail (1 / cylinderNu d ζ) :=
    Real.rpow_pos_of_pos htail _
  have hgeomRoot : 0 < b / (32 * (1 + Real.sqrt κ)) := by positivity
  have hε : 0 < ε := by
    dsimp [ε, cylinderRadius, b, tail]
    exact lt_min hgeomRoot (lt_min hcoreRoot (lt_min hannRoot htailRoot))
  have hgeom : ε ≤ b / (32 * (1 + Real.sqrt κ)) := by
    dsimp [ε, cylinderRadius, b]
    exact min_le_left _ _
  have hrootA : ε ≤ Real.rpow b (1 / ζ) := by
    dsimp [ε, cylinderRadius, b]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrootB : ε ≤ Real.rpow b (1 / (2 - ζ)) := by
    dsimp [ε, cylinderRadius, b]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrootTail : ε ≤ Real.rpow tail (1 / cylinderNu d ζ) := by
    dsimp [ε, cylinderRadius, b, tail]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpowA : Real.rpow ε ζ ≤ b := by
    calc
      Real.rpow ε ζ ≤ Real.rpow (Real.rpow b (1 / ζ)) ζ :=
        Real.rpow_le_rpow hε.le hrootA hζ0.le
      _ = b := by
        calc
          _ = Real.rpow b ((1 / ζ) * ζ) := (Real.rpow_mul hb.le _ _).symm
          _ = b := by
            rw [one_div_mul_cancel hζ0.ne']
            exact Real.rpow_one b
  have hβ : 0 < 2 - ζ := by linarith
  have hpowB : Real.rpow ε (2 - ζ) ≤ b := by
    calc
      Real.rpow ε (2 - ζ) ≤ Real.rpow (Real.rpow b (1 / (2 - ζ))) (2 - ζ) :=
        Real.rpow_le_rpow hε.le hrootB hβ.le
      _ = b := by
        calc
          _ = Real.rpow b ((1 / (2 - ζ)) * (2 - ζ)) := (Real.rpow_mul hb.le _ _).symm
          _ = b := by
            rw [one_div_mul_cancel (sub_ne_zero.mpr (by linarith))]
            exact Real.rpow_one b
  have hpowTail : Real.rpow ε (cylinderNu d ζ) ≤ tail := by
    calc
      Real.rpow ε (cylinderNu d ζ) ≤
          Real.rpow (Real.rpow tail (1 / cylinderNu d ζ)) (cylinderNu d ζ) :=
        Real.rpow_le_rpow hε.le hrootTail hnu.le
      _ = tail := by
        calc
          _ = Real.rpow tail ((1 / cylinderNu d ζ) * cylinderNu d ζ) :=
            (Real.rpow_mul htail.le _ _).symm
          _ = tail := by
            rw [one_div_mul_cancel hnu.ne']
            exact Real.rpow_one tail
  refine ⟨hε, ?_, ?_, ?_, ?_⟩
  · have hstrict : b / (32 * (1 + Real.sqrt κ)) <
        b / (16 * (1 + Real.sqrt κ)) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [hb, Real.sqrt_nonneg κ]
    exact hgeom.trans_lt hstrict
  · have hpowPos : 0 < Real.rpow ε ζ := Real.rpow_pos_of_pos hε ζ
    have hneg : Real.rpow ε (-ζ) = (Real.rpow ε ζ)⁻¹ := by
      change ε ^ (-ζ) = (ε ^ ζ)⁻¹
      exact Real.rpow_neg hε.le ζ
    change 1 ≤ b * Real.rpow ε (-ζ)
    calc
      1 = Real.rpow ε ζ * (Real.rpow ε ζ)⁻¹ := (mul_inv_cancel₀ hpowPos.ne').symm
      _ ≤ b * (Real.rpow ε ζ)⁻¹ :=
        mul_le_mul_of_nonneg_right hpowA (inv_nonneg.mpr hpowPos.le)
      _ = b * Real.rpow ε (-ζ) := by rw [← hneg]
  · calc
      b⁻¹ * Real.rpow ε (2 - ζ) ≤ b⁻¹ * b :=
        mul_le_mul_of_nonneg_left hpowB (inv_nonneg.mpr hb.le)
      _ = 1 := inv_mul_cancel₀ hb.ne'
  · calc
      j ^ 2 * Real.exp rate * b⁻¹ * Real.rpow ε (cylinderNu d ζ) ≤
      j ^ 2 * Real.exp rate * b⁻¹ * tail := by
        exact mul_le_mul_of_nonneg_left hpowTail (by positivity)
      _ = (1 / 2 : ℝ) ^ (n + 1) := by
        dsimp [tail, cylinderTail, rate, cylinderRate, b, cylinderB, j]
        field_simp [ne_of_gt hb, ne_of_gt hj, (Real.exp_pos _).ne']

theorem cylinderB_step (n : ℕ) : cylinderB (n + 1) = cylinderB n / 2 := by
  dsimp [cylinderB]
  rw [show n + 1 + 3 = (n + 3) + 1 by omega, pow_succ]
  norm_num [div_eq_mul_inv]

theorem cylinderB_step_le (n : ℕ) : cylinderB (n + 1) ≤ cylinderB n := by
  rw [cylinderB_step]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  nlinarith [cylinderB_pos n]

theorem cylinderB_le_of_le {i j : ℕ} (hij : i ≤ j) : cylinderB j ≤ cylinderB i := by
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      by_cases hij' : i ≤ j
      · exact (cylinderB_step_le j).trans (ih hij')
      · have hi : i = j + 1 := by omega
        subst i
        exact le_rfl

/-- The outer cylinder around the j-th transverse center. -/
def outerCylinder {d : ℕ} (n : ℕ) (ζ κ : ℝ) : Set (Vec d) :=
  {x | transverseNorm (x - cylinderCenter (cylinderB n)) ≤
    2 * cylinderRadius d n ζ κ}

private theorem transverseCoord_abs_le {d : ℕ} (hd : 2 ≤ d) (x : Vec d) (b : ℝ) :
    |x (cylinderCoordOne hd) - b| ≤ transverseNorm (x - cylinderCenter b) := by
  let i₁ := cylinderCoordOne hd
  have hcoord : transversePart (x - cylinderCenter b) i₁ = x i₁ - b := by
    simp [i₁, transversePart, cylinderCenter, cylinderCoordOne]
  calc
    |x i₁ - b| = ‖transversePart (x - cylinderCenter b) i₁‖ := by
      rw [hcoord, Real.norm_eq_abs]
    _ ≤ ‖transversePart (x - cylinderCenter b)‖ := norm_le_pi_norm _ i₁
    _ ≤ CoarseDeGiorgi.Foundations.Euclid.eNorm2
        (transversePart (x - cylinderCenter b)) :=
      CoarseDeGiorgi.Foundations.Euclid.norm_le_eNorm2 _
    _ = transverseNorm (x - cylinderCenter b) := rfl

/-- The radius schedule gives disjoint closures for the cylinders of radius
2 epsilon used in the coefficient field. -/
theorem outerCylinder_pairwise_disjoint {d i j : ℕ} (hd : 3 ≤ d) {ζ κ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hκ : 0 < κ) (hij : i < j) :
    Disjoint (outerCylinder (d := d) i ζ κ) (outerCylinder j ζ κ) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hiData := cylinderRadius_data (d := d) (n := i) hd hζ0 hζ2 hκ
  have hjData := cylinderRadius_data (d := d) (n := j) hd hζ0 hζ2 hκ
  have hiB : 0 < cylinderB i := cylinderB_pos i
  have hjB : 0 < cylinderB j := cylinderB_pos j
  have hji : cylinderB j ≤ cylinderB (i + 1) := cylinderB_le_of_le (by omega)
  have hstep : cylinderB (i + 1) = cylinderB i / 2 := cylinderB_step i
  have hsmallCenter : cylinderB j ≤ cylinderB i / 2 := by rw [← hstep]; exact hji
  have hcenterAbs : cylinderB i / 2 ≤ |cylinderB i - cylinderB j| := by
    have hdiff : 0 ≤ cylinderB i - cylinderB j := by linarith
    rw [abs_of_nonneg hdiff]
    linarith
  have hden_i : 0 < 16 * (1 + Real.sqrt κ) := by positivity
  have hden_one : (0 : ℝ) < 16 := by norm_num
  have hiScale : cylinderB i / (16 * (1 + Real.sqrt κ)) ≤ cylinderB i / 16 := by
    rw [div_le_div_iff₀ hden_i hden_one]
    nlinarith [Real.sqrt_nonneg κ, hiB]
  have hjScale : cylinderB j / (16 * (1 + Real.sqrt κ)) ≤ cylinderB j / 16 := by
    rw [div_le_div_iff₀ hden_i hden_one]
    nlinarith [Real.sqrt_nonneg κ, hjB]
  have hiRadius : cylinderRadius d i ζ κ < cylinderB i / 16 :=
    hiData.2.1.trans_le hiScale
  have hjRadius : cylinderRadius d j ζ κ < cylinderB j / 16 :=
    hjData.2.1.trans_le hjScale
  have hsumRadius : 2 * cylinderRadius d i ζ κ + 2 * cylinderRadius d j ζ κ <
      cylinderB i / 2 := by
    have hboundj : cylinderB j / 8 ≤ cylinderB i / 16 := by
      calc
        cylinderB j / 8 ≤ (cylinderB i / 2) / 8 :=
          div_le_div_of_nonneg_right hsmallCenter (by norm_num)
        _ = cylinderB i / 16 := by ring
    have hsum : 2 * cylinderRadius d i ζ κ + 2 * cylinderRadius d j ζ κ <
        cylinderB i / 8 + cylinderB j / 8 := by nlinarith [hiRadius, hjRadius]
    calc
      _ < cylinderB i / 8 + cylinderB j / 8 := hsum
      _ = cylinderB j / 8 + cylinderB i / 8 := by ring
      _ ≤ cylinderB i / 16 + cylinderB i / 8 := add_le_add_left hboundj _
      _ = cylinderB i / 8 + cylinderB i / 16 := by ring
      _ < cylinderB i / 2 := by nlinarith [hiB]
  let i₁ := cylinderCoordOne (by omega : 2 ≤ d)
  have hiCoord := transverseCoord_abs_le (by omega : 2 ≤ d) x (cylinderB i)
  have hjCoord := transverseCoord_abs_le (by omega : 2 ≤ d) x (cylinderB j)
  have hxi' : |x i₁ - cylinderB i| ≤ 2 * cylinderRadius d i ζ κ := hiCoord.trans hxi
  have hxj' : |x i₁ - cylinderB j| ≤ 2 * cylinderRadius d j ζ κ := hjCoord.trans hxj
  have htriangle : |cylinderB i - cylinderB j| ≤
      |x i₁ - cylinderB i| + |x i₁ - cylinderB j| := by
    calc
      |cylinderB i - cylinderB j| =
          |(cylinderB i - x i₁) + (x i₁ - cylinderB j)| := by congr 1; ring
      _ ≤ |cylinderB i - x i₁| + |x i₁ - cylinderB j| := abs_add_le _ _
      _ = |x i₁ - cylinderB i| + |x i₁ - cylinderB j| := by rw [abs_sub_comm]
  have hcontr := htriangle.trans (add_le_add hxi' hxj')
  linarith
end CoarseDeGiorgi.SharpnessExamples
