module

public import CoarseDeGiorgi.LowerFractional.MeanCube
public import CoarseDeGiorgi.LowerFractional.Aliases

/-! Domain bridges for the auxiliary cubes. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory
open Foundations.Reconstruction

/-- Auxiliary cubes are open bounded convex domains in every dimension. -/
theorem auxCube_isOpenBoundedConvexDomain {d : ℕ} (m : ℤ) (z : Fin d → ℤ) :
    IsOpenBoundedConvexDomain (CoarseDeGiorgi.auxCube m z) := by
  refine ⟨isOpen_auxCube m z, ?_, ?_⟩
  · let c : Vec d := fun i => (z i : ℝ) * (3 : ℝ) ^ (-m)
    refine ⟨‖c‖ + auxSide m, add_pos_of_nonneg_of_pos (norm_nonneg _) (auxSide_pos m), ?_⟩
    intro x hx i
    have hi : |x i - c i| < auxSide m / 2 := hx i
    have hc : |c i| ≤ ‖c‖ := norm_le_pi_norm c i
    have hb := abs_add_le (x i - c i) (c i)
    rw [sub_add_cancel] at hb
    have hs := auxSide_pos m
    linarith
  · rw [← auxCube_eq_statement, auxCube_eq_pi_Ioo]
    exact convex_pi fun i _ => convex_Ioo _ _

/-- The exact auxiliary center belongs to the open cube. -/
theorem auxCube_nonempty {d : ℕ} (m : ℤ) (z : Fin d → ℤ) :
    (CoarseDeGiorgi.auxCube m z).Nonempty := by
  refine ⟨fun i => (z i : ℝ) * (3 : ℝ) ^ (-m), ?_⟩
  intro i
  simp only [sub_self, abs_zero]
  exact half_pos (auxSide_pos m)

end CoarseDeGiorgi.LowerFractional
