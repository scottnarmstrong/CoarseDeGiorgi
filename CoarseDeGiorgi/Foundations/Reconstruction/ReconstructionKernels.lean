import CoarseDeGiorgi.Foundations.Reconstruction.LowestBounds
import CoarseDeGiorgi.Foundations.Reconstruction.AssemblyInputs

/-! # The concrete kernel sequence consumed by the committed assembly -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Each auxiliary side is three times the next absolute side. -/
theorem auxSide_eq_three_mul_next (m : ℤ) : auxSide m = 3 * auxSide (m + 1) := by
  unfold auxSide
  rw [show 1 - m = (1 : ℤ) + (1 - (m + 1)) by omega, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]

/-- The explicit lowest kernel followed by the wrapped fine kernels. -/
def reconstructionKernel (m : ℤ) : ℕ → Vec d → Vec d
  | 0 => lowestKernel m d
  | n + 1 => periodicFineKernel m (auxSide (m + (n + 1 : ℕ)))

theorem reconstruction_fine_side_small (m : ℤ) (n : ℕ) :
    3 * auxSide (m + (n + 1 : ℕ)) ≤ auxSide m := by
  rw [show m + (n + 1 : ℕ) = (m + n) + 1 by omega, ← auxSide_eq_three_mul_next]
  exact assembly_side_le m n

theorem contDiff_reconstructionKernel (m : ℤ) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (reconstructionKernel (d := d) m j) := by
  cases j with
  | zero => exact contDiff_lowestKernel m d
  | succ n => exact contDiff_periodicFineKernel (auxSide_pos _) (reconstruction_fine_side_small m n)

theorem reconstructionKernel_add_period (m : ℤ) (j : ℕ) (i : Fin d) (x : Vec d) :
    reconstructionKernel m j (x + (2 * auxSide m) • basisVec i) = reconstructionKernel m j x := by
  cases j with
  | zero => exact lowestKernel_add_period m d i x
  | succ n => exact periodicFineKernel_add_period m _ i x

/-- Both block types have the same scale-uniform first three jet bounds. -/
theorem exists_bound_reconstructionKernel_jets : ∃ A : ℝ, 1 ≤ A ∧ ∀ (m : ℤ) (j : ℕ),
    (∀ v : Vec d, ‖reconstructionKernel m j v‖ ≤
      A * auxSide (m + j) * (auxSide (m + j) ^ d)⁻¹) ∧
    (∀ v : Vec d, ‖fderiv ℝ (reconstructionKernel m j) v‖ ≤ A * (auxSide (m + j) ^ d)⁻¹) ∧
    (∀ v : Vec d, ‖fderiv ℝ (fderiv ℝ (reconstructionKernel m j)) v‖ ≤
      A * (auxSide (m + j) ^ d)⁻¹ * (auxSide (m + j))⁻¹) := by
  obtain ⟨Af, hAf, hf⟩ := exists_bound_periodicFineKernel_jets (d := d)
  obtain ⟨Al, hAl, hl⟩ := exists_bound_lowestKernel_jets (d := d)
  refine ⟨max Af Al, hAf.trans (le_max_left _ _), fun m j => ?_⟩
  have hside := auxSide_pos (m + j)
  cases j with
  | zero =>
    simp only [Nat.cast_zero, add_zero] at hside ⊢
    obtain ⟨h0, h1, h2⟩ := hl m
    exact ⟨fun v => (h0 v).trans (by gcongr; exact le_max_right Af Al),
      fun v => (h1 v).trans (by gcongr; exact le_max_right Af Al),
      fun v => (h2 v).trans (by gcongr; exact le_max_right Af Al)⟩
  | succ n =>
    obtain ⟨h0, h1, h2⟩ := hf m _ hside (reconstruction_fine_side_small m n)
    exact ⟨fun v => (h0 v).trans (by gcongr; exact le_max_left Af Al),
      fun v => (h1 v).trans (by gcongr; exact le_max_left Af Al),
      fun v => (h2 v).trans (by gcongr; exact le_max_left Af Al)⟩

/-- The committed assembly blocks are exactly the convolutions of these kernels with the weak gradient. -/
theorem assemblyBlock_eq_reconstructionKernel_pairing {m : ℤ} {z : Fin d → ℤ}
    {w : Vec d → ℝ} {Dw : Vec d → Vec d}
    (hweak : HasWeakGradientOn (auxCube m z) w Dw)
    (hw : IntegrableOn w (auxCube m z) volume) (hDw : IntegrableOn Dw (auxCube m z) volume)
    (j : ℕ) (x : Vec d) :
    assemblyBlock m z w j x = kernelPairing m z (reconstructionKernel m j) Dw x := by
  cases j with
  | zero => exact smoothAverage_sub_mean_eq_lowestKernelPairing hweak hw hDw x
  | succ n =>
    have h := smoothAverage_sub_eq_fineKernelPairing (auxSide_pos _)
      (reconstruction_fine_side_small m n) hweak hw hDw x
    change smoothAverage m (auxSide (m + (n + 1 : ℕ))) z w x -
      smoothAverage m (3 * auxSide (m + (n + 1 : ℕ))) z w x = _ at h
    rw [show m + (n + 1 : ℕ) = (m + n) + 1 by omega, ← auxSide_eq_three_mul_next] at h
    simpa only [assemblyBlock, reconstructionKernel, Nat.cast_add, Nat.cast_one, add_assoc] using h

end

end CoarseDeGiorgi.Foundations.Reconstruction
