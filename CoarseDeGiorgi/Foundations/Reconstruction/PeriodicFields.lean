module

public import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicKernelSmooth

/-! # Coordinate-periodic fields and their derivatives -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization
open scoped BigOperators

noncomputable section

variable {d : ℕ} {E : Type*}

/-- Coordinate periodicity extends to every integer lattice shift. -/
theorem periodicField_add_integerShift (m : ℤ) (F : Vec d → E)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x)
    (n : Fin d → ℤ) (x : Vec d) :
    F (x + ∑ i : Fin d, n i • ((2 * auxSide m) • basisVec i)) = F x := by
  classical
  have hs (s : Finset (Fin d)) :
      F (x + ∑ i ∈ s, n i • ((2 * auxSide m) • basisVec i)) = F x := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, add_zero]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,
        show x + (n i • ((2 * auxSide m) • basisVec i) +
          ∑ j ∈ s, n j • ((2 * auxSide m) • basisVec j)) =
          (x + ∑ j ∈ s, n j • ((2 * auxSide m) • basisVec j)) +
            n i • ((2 * auxSide m) • basisVec i) by abel]
      exact (Function.Periodic.zsmul (hp i) (n i) _).trans ih
  exact hs Finset.univ

/-- A coordinate-periodic field is determined by its wrapped values. -/
theorem periodicField_wrapBox (m : ℤ) (F : Vec d → E)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) (x : Vec d) :
    F (wrapBox m x) = F x := by
  classical
  let n : Fin d → ℤ := fun i => toIcoDiv
    (mul_pos (by norm_num : (0 : ℝ) < 2) (auxSide_pos m)) (-auxSide m) (x i)
  have heq : wrapBox m x + ∑ i : Fin d, n i • ((2 * auxSide m) • basisVec i) = x := by
    funext j
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul,
      basisVec_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact toIcoMod_add_toIcoDiv_mul
      (mul_pos (by norm_num : (0 : ℝ) < 2) (auxSide_pos m)) (-auxSide m) (x j)
  exact (periodicField_add_integerShift m F hp n (wrapBox m x)).symm.trans
    (congrArg F heq)

/-- All iterated derivatives retain coordinate periodicity. -/
theorem iteratedFDeriv_periodicField [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℤ) (F : Vec d → E)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x)
    (a : ℕ) (i : Fin d) (x : Vec d) :
    iteratedFDeriv ℝ a F (x + (2 * auxSide m) • basisVec i) =
      iteratedFDeriv ℝ a F x := by
  have heq : (fun y => F (y + (2 * auxSide m) • basisVec i)) = F := funext (hp i)
  rw [← iteratedFDeriv_comp_add_right, heq]

/-- Smooth periodic fields have a uniform bound on finitely many derivative orders. -/
theorem exists_bound_periodicField_jets [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℤ) (F : Vec d → E) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) (N : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ a ≤ N, ∀ x : Vec d, ‖iteratedFDeriv ℝ a F x‖ ≤ A := by
  have hb (a : ℕ) : ∃ B : ℝ, ∀ x : Vec d, ‖iteratedFDeriv ℝ a F x‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Vec d) (auxSide m)).exists_bound_of_continuousOn
      ((hF.continuous_iteratedFDeriv (by simp)).continuousOn)
    refine ⟨B, fun x => ?_⟩
    have hnorm : ‖wrapBox m x‖ ≤ auxSide m := by
      apply (pi_norm_le_iff_of_nonneg (auxSide_pos m).le).mpr
      intro i
      rw [Real.norm_eq_abs]
      obtain ⟨hlo, hhi⟩ := wrapCoordinate_mem_Ico m (x i)
      exact abs_le.mpr ⟨hlo, hhi.le⟩
    rw [← periodicField_wrapBox m (iteratedFDeriv ℝ a F)
      (iteratedFDeriv_periodicField m F hp a) x]
    exact hB _ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm)
  choose B hB using hb
  refine ⟨max 1 (∑ a ∈ Finset.range (N + 1), max 0 (B a)), le_max_left _ _, ?_⟩
  intro a ha x
  exact (hB a x).trans ((le_max_right 0 (B a)).trans
    ((Finset.single_le_sum (fun i _ => le_max_left 0 (B i))
      (show a ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))).trans
      (le_max_right _ _)))

end

end CoarseDeGiorgi.Foundations.Reconstruction
