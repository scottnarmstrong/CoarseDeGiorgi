module

public import CoarseDeGiorgi.Foundations.Reconstruction.ReflectedIBP
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.MeasureTheory.Function.Floor

/-! # Measurable periodic continuation of the even reflection

Coordinates are reduced to the half-open fundamental interval using toIcoMod.
On the open reflected box this reduction is exactly the identity.
-/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Coordinate reduction to the fundamental interval of length twice the root side. -/
def wrapCoordinate (m : ℤ) (t : ℝ) : ℝ :=
  toIcoMod (mul_pos (by norm_num : (0 : ℝ) < 2) (auxSide_pos m)) (-auxSide m) t

theorem wrapCoordinate_add_period (m : ℤ) (t : ℝ) :
    wrapCoordinate m (t + 2 * auxSide m) = wrapCoordinate m t :=
  toIcoMod_add_right _ _ _

theorem measurable_wrapCoordinate (m : ℤ) : Measurable (wrapCoordinate m) := by
  unfold wrapCoordinate
  simp_rw [toIcoMod_eq_add_fract_mul]
  exact measurable_const.add
    (((measurable_id.sub measurable_const).div_const _).fract.mul_const _)

theorem wrapCoordinate_eq_self (m : ℤ) {t : ℝ} (ht : |t| < auxSide m) :
    wrapCoordinate m t = t := by
  apply (toIcoMod_eq_self _).mpr
  obtain ⟨hlo, hhi⟩ := abs_lt.mp ht
  exact ⟨hlo.le, by linarith only [hhi]⟩

/-- Coordinatewise reduction to the reflected fundamental box. -/
def wrapBox (m : ℤ) (x : Vec d) : Vec d := fun i => wrapCoordinate m (x i)

theorem measurable_wrapBox (m : ℤ) : Measurable (wrapBox (d := d) m) :=
  measurable_pi_iff.mpr fun i => (measurable_wrapCoordinate m).comp (measurable_pi_apply i)

theorem wrapBox_eq_self (m : ℤ) {x : Vec d} (hx : x ∈ reflectionBox m) : wrapBox m x = x := by
  ext i
  exact wrapCoordinate_eq_self m (hx i)

theorem wrapBox_add_period_basisVec (m : ℤ) (i : Fin d) (x : Vec d) :
    wrapBox m (x + (2 * auxSide m) • basisVec i) = wrapBox m x := by
  ext j
  simp only [wrapBox, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply]
  by_cases hj : j = i
  · subst j
    simp only [ite_true, mul_one, wrapCoordinate_add_period]
  · simp only [hj, ite_false, mul_zero, add_zero]

/-- Globally periodic even reflection of the scalar field. -/
def periodicReflectedScalar (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (x : Vec d) : ℝ :=
  reflectedScalar m z w (wrapBox m x)

theorem periodicReflectedScalar_add_period (m : ℤ) (z : Fin d → ℤ)
    (w : Vec d → ℝ) (i : Fin d) (x : Vec d) :
    periodicReflectedScalar m z w (x + (2 * auxSide m) • basisVec i) =
      periodicReflectedScalar m z w x := by
  unfold periodicReflectedScalar
  rw [wrapBox_add_period_basisVec]

theorem periodicReflectedScalar_eq_on_box (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ)
    {x : Vec d} (hx : x ∈ reflectionBox m) :
    periodicReflectedScalar m z w x = reflectedScalar m z w x := by
  unfold periodicReflectedScalar
  rw [wrapBox_eq_self m hx]

end

end CoarseDeGiorgi.Foundations.Reconstruction
