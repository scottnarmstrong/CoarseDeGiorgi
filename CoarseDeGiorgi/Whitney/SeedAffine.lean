module

public import CoarseDeGiorgi.Whitney.SeedBarycentric
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! # Explicit affine interpolation on a Kuhn cell -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization

noncomputable section

variable {d : ℕ}

/-- The affine function determined by the ordered vertex values. -/
def seedKuhnAffine (k : ℕ) (q : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (c : (Fin d → ℤ) → ℝ) (x : Vec d) : ℝ :=
  c (seedKuhnVertexIndex q π (Fin.last d)) + ∑ i : Fin d,
    (c (seedKuhnVertexIndex q π i.castSucc) - c (seedKuhnVertexIndex q π i.succ)) *
      seedUnitCoordinate k q π x i

private theorem weighted_break_sum (k : ℕ) (q : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (c : (Fin d → ℤ) → ℝ) (x : Vec d) :
    (∑ t : Fin (d + 1), c (seedKuhnVertexIndex q π t) *
      (seedKuhnBreak k q π x (t.val + 1) - seedKuhnBreak k q π x t.val)) =
      seedKuhnAffine k q π c x := by
  have hnext (i : Fin d) : seedKuhnBreak k q π x (i.val + 1) = seedUnitCoordinate k q π x i := by
    simp only [seedKuhnBreak, dite_eq_right (by omega : i.val + 1 ≠ 0),
      dite_eq_left (by have := i.isLt; omega : i.val + 1 ≤ d), Nat.add_sub_cancel]
  have hfirst : (∑ t : Fin (d + 1), c (seedKuhnVertexIndex q π t) * seedKuhnBreak k q π x (t.val + 1)) =
      (∑ i : Fin d, c (seedKuhnVertexIndex q π i.castSucc) * seedUnitCoordinate k q π x i) +
      c (seedKuhnVertexIndex q π (Fin.last d)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, hnext, Fin.val_last]
    simp [seedKuhnBreak]
  have hsecond : (∑ t : Fin (d + 1), c (seedKuhnVertexIndex q π t) * seedKuhnBreak k q π x t.val) =
      ∑ i : Fin d, c (seedKuhnVertexIndex q π i.succ) * seedUnitCoordinate k q π x i := by
    rw [Fin.sum_univ_succ]
    have hzero : seedKuhnBreak k q π x 0 = 0 := by simp [seedKuhnBreak]
    simp only [Fin.val_zero, hzero, mul_zero, Fin.val_succ, hnext, zero_add]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hfirst, hsecond]
  unfold seedKuhnAffine
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem seedWeightedHat_eq_affine {k : ℕ} {q : Fin d → ℤ} {π : Equiv.Perm (Fin d)}
    {x : Vec d} (hx : x ∈ Foundations.Simplex.kuhnSimplex (-(k : ℤ)) π
      (fun i => seedScale k * (q i : ℝ))) (c : (Fin d → ℤ) → ℝ) :
    (∑' m : Fin d → ℤ, c m * seedHat k m x) = seedKuhnAffine k q π c x := by
  rw [seedWeightedHat_kuhnInterpolation hx c]
  exact weighted_break_sum k q π c x

end

end CoarseDeGiorgi.Whitney

