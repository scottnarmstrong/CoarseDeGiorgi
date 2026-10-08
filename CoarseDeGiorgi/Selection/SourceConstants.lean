module

public import CoarseDeGiorgi.Selection.SourceResponses

@[expose] public section

namespace CoarseDeGiorgi.Selection
open scoped ENNReal

theorem source_selection_gap_factor {δ : ℝ} (hδ : 0 < δ) (e : ℝ) :
    ENNReal.ofReal (32 / δ) ^ e =
      ENNReal.ofReal (32 : ℝ) ^ e * ENNReal.ofReal (δ ^ (-e)) := by
  have he : (32 / δ) ^ e = (32 : ℝ) ^ e * δ ^ (-e) := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 32) hδ.le,
      Real.rpow_neg hδ.le, div_eq_mul_inv]
  rw [ENNReal.ofReal_rpow_of_pos (div_pos (by norm_num : (0 : ℝ) < 32) hδ), he,
    ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 32) _),
    ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 32)]

end CoarseDeGiorgi.Selection
