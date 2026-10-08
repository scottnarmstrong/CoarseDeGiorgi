module

public import CoarseDeGiorgi.Whitney.Extension.Lipschitz
public import CoarseDeGiorgi.Statements.EuclidLipConst

/-!
# The Lipschitz conjunct of Proposition `p.affine.extension`
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

theorem norm_ge_of_notMem_originCube (τ : ℝ) (_hτ : 0 ≤ τ) {x : Vec d}
    (hx : x ∈ (originCube (d := d) τ)ᶜ) : τ / 2 ≤ ‖x‖ := by
  by_contra hcon
  push Not at hcon
  apply hx
  intro i
  have : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have h2 := abs_lt.mp (lt_of_le_of_lt this hcon)
  constructor <;> linarith only [h2.1, h2.2]

theorem euclidLipConst_le_of_bound {S : Set (Vec d)} {F : Vec d → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x ∈ S, ∀ y ∈ S, |F x - F y| ≤ M * euclidDist x y) :
    euclidLipConst S F ≤ ENNReal.ofReal M := by
  unfold euclidLipConst
  have hK : ∀ x ∈ S, ∀ y ∈ S, ENNReal.ofReal |F x - F y| ≤
      ((M.toNNReal : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (euclidDist x y) := by
    intro x hx y hy
    have : ((M.toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal M := rfl
    rw [this, ← ENNReal.ofReal_mul hM]
    exact ENNReal.ofReal_le_ofReal (h x hx y hy)
  exact iInf₂_le (M.toNNReal) hK

theorem LipConst_pos (d : ℕ) (hd : 1 ≤ d) : 0 < LipConst d := by
  have := C32_nonneg d
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold LipConst; positivity

end

end CoarseDeGiorgi.WhitneyExt
