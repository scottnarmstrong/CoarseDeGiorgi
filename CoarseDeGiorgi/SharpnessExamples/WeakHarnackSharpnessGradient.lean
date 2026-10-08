import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessFlux

/-! # The supersolution `u(x) = U(|x|²)`: gradient and flux identity -/

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal ContDiff

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The supersolution `u_ε(x) = U_ε(|x|²)`. -/
def whu (d : ℕ) (q t ε : ℝ) : Vec d → ℝ := fun x => whU d q t ε (vecNormSq x)

/-- The open set `|x|² < d`, on which the profile is smooth. -/
def whO (d : ℕ) : Set (Vec d) := {x | vecNormSq x < d}

theorem isOpen_whO {d : ℕ} : IsOpen (whO d) :=
  isOpen_lt contDiff_vecNormSq.continuous continuous_const

theorem vecNormSq_le {d : ℕ} (x : Vec d) : vecNormSq x ≤ d * ‖x‖ ^ 2 := by
  rw [vecNormSq_eq_sum]
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have := norm_le_pi_norm x i
        rw [Real.norm_eq_abs] at this
        exact sq_le_sq' (by linarith [abs_nonneg (x i), neg_abs_le (x i)])
          (le_trans (le_abs_self _) this)
    _ = d * ‖x‖ ^ 2 := by simp

theorem vecNormSq_lt_of_mem {d : ℕ} [NeZero d] {x : Vec d} (hx : x ∈ originCube 1) :
    vecNormSq x < d / 4 := by
  have hxn : ‖x‖ < 1 / 2 := (mem_originCube_iff x).1 hx
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have h1 := vecNormSq_le x
  have h2 : ‖x‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg x]
  nlinarith

theorem mem_whO_of_mem {d : ℕ} [NeZero d] {x : Vec d} (hx : x ∈ originCube 1) : x ∈ whO d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have := vecNormSq_lt_of_mem hx
  show vecNormSq x < d
  linarith

theorem contDiffOn_whu {d : ℕ} (hd : 1 ≤ d) (q t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (whu d q t ε) (whO d) := by
  have h := (contDiffOn_whU hd q t hε).comp (contDiff_vecNormSq (d := d)).contDiffOn
    (fun x (hx : x ∈ whO d) => (show vecNormSq x < d from hx))
  exact h

theorem smoothGrad_whu {d : ℕ} (hd : 1 ≤ d) (q t : ℝ) {ε : ℝ} (hε : 0 < ε) {x : Vec d}
    (hx : x ∈ whO d) (i : Fin d) :
    smoothGrad (whu d q t ε) x i = -(2 * whk d q t ε (vecNormSq x) * x i) := by
  have hdiff : DifferentiableAt ℝ (whu d q t ε) x :=
    ((contDiffOn_whu hd q t hε).differentiableOn (by simp)).differentiableAt
      (isOpen_whO.mem_nhds hx)
  have hs := hasDerivAt_vecNormSq_line x i
  have hU : HasDerivAt (whU d q t ε) (-whk d q t ε (vecNormSq x))
      (vecNormSq (x + (0 : ℝ) • basisVec i)) := by
    simp only [zero_smul, add_zero]
    exact hasDerivAt_whU hd q t hε hx
  have hc := hU.comp 0 hs
  have hl : HasLineDerivAt ℝ (whu d q t ε) (-whk d q t ε (vecNormSq x) * (2 * x i)) x
      (basisVec i) := by
    unfold HasLineDerivAt
    exact hc
  unfold smoothGrad
  rw [← hdiff.lineDeriv_eq_fderiv, hl.lineDeriv]
  ring

/-- The flux identity on the cube: `a(|x|) (-∇u) = H(|x|²) x`. -/
theorem whFlux_identity {d : ℕ} [NeZero d] {q t : ℝ} {ε : ℝ}
    (hε : 0 < ε) {x : Vec d} (hx : x ∈ originCube 1) :
    matVecMul (whCoeff d q t x) (-(smoothGrad (whu d q t ε) x)) = whF d ε x := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  funext i
  have hx0 := mem_whO_of_mem hx
  have hmv : matVecMul (whCoeff d q t x) (-(smoothGrad (whu d q t ε) x)) =
      whField d q t (euclidNorm x) • (-(smoothGrad (whu d q t ε) x)) := by
    exact matVecMul_scalarMatrix _ _
  rw [hmv, Pi.smul_apply, Pi.neg_apply, smoothGrad_whu hd q t hε hx0, smul_eq_mul]
  unfold whF
  by_cases hxz : x i = 0
  · simp [hxz]
  · have hσ : 0 < vecNormSq x := by
      rw [vecNormSq_eq_sum]
      exact lt_of_lt_of_le (by positivity : 0 < x i ^ 2)
        (Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i))
    have hσd : vecNormSq x ≤ d := le_of_lt hx0
    have hsq : euclidNorm x = Real.sqrt (vecNormSq x) := rfl
    have hAs := whAs_pos (d := d) (q := q) (t := t) hσ hσd
    have hc : whField d q t (euclidNorm x) = whAs d q t (vecNormSq x) := by
      rw [hsq]
      exact whField_eq (Real.sqrt_pos.2 hσ) (by unfold whR; exact Real.sqrt_le_sqrt hσd)
    rw [hc]
    unfold whk whK whH
    field_simp

end

end CoarseDeGiorgi.SharpnessExamples
