module

public import CoarseDeGiorgi.Whitney.SeedAffine
public import CoarseDeGiorgi.Whitney.SeedRefinement

/-! # Refinement of arbitrary nodal interpolants -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization Set

noncomputable section

variable {d : ℕ}

def seedInterpolation (k : ℕ) (c : (Fin d → ℤ) → ℝ) (x : Vec d) : ℝ :=
  ∑' m : Fin d → ℤ, c m * seedHat k m x

theorem seedInterpolation_refinement (k : ℕ) (c : (Fin d → ℤ) → ℝ) (x : Vec d) :
    seedInterpolation k c x = seedInterpolation (k + 1)
      (fun m => seedInterpolation k c (seedNode (k + 1) m)) x := by
  classical
  have hf : (⋃ m ∈ Function.support (fun m => seedHat (k + 1) m x),
      Function.support (fun M => seedHat k M (seedNode (k + 1) m)) ×ˢ {m}).Finite :=
    (finite_seedHat_support (k + 1) x).biUnion (fun m _ =>
      (finite_seedHat_support k (seedNode (k + 1) m)).prod (Set.finite_singleton m))
  have hsum : Summable (Function.uncurry (fun M m : Fin d → ℤ =>
      c M * seedHat k M (seedNode (k + 1) m) * seedHat (k + 1) m x)) := by
    apply summable_of_hasFiniteSupport
    apply hf.subset
    intro p hp
    have hm := (mul_ne_zero_iff.mp hp).2
    have hM := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).2
    exact Set.mem_iUnion.mpr ⟨p.2, Set.mem_iUnion.mpr ⟨hm, hM, rfl⟩⟩
  unfold seedInterpolation
  calc
    _ = ∑' M : Fin d → ℤ, ∑' m : Fin d → ℤ,
        c M * seedHat k M (seedNode (k + 1) m) * seedHat (k + 1) m x := by
      apply tsum_congr
      intro M
      rw [seedHat_refinement, ← tsum_mul_left]
      apply tsum_congr
      intro m
      ring
    _ = ∑' m : Fin d → ℤ, ∑' M : Fin d → ℤ,
        c M * seedHat k M (seedNode (k + 1) m) * seedHat (k + 1) m x := hsum.tsum_comm.symm
    _ = _ := by simp only [tsum_mul_right]

end

end CoarseDeGiorgi.Whitney

