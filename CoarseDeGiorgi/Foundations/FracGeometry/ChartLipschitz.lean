module

public import CoarseDeGiorgi.Foundations.FracGeometry.TranslationComparison

@[expose] public section

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory Set Metric
open scoped ENNReal NNReal

noncomputable section

theorem abs_div_sub_div_le_normalized {a b c e : ℝ} (hb : 1 ≤ b) (he : 1 ≤ e)
    (hc : |c| ≤ e) : |a / b - c / e| ≤ |a - c| + |b - e| := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have he0 : 0 < e := zero_lt_one.trans_le he
  rw [div_sub_div a c hb0.ne' he0.ne']
  rw [abs_div, abs_of_pos (mul_pos hb0 he0), div_le_iff₀ (mul_pos hb0 he0)]
  calc
    |a * e - b * c| = |(a - c) * e + c * (e - b)| := by congr 1; ring
    _ ≤ |(a - c) * e| + |c * (e - b)| := abs_add_le _ _
    _ = |a - c| * e + |c| * |b - e| := by
      rw [abs_mul, abs_mul, abs_of_pos he0, abs_sub_comm e b]
    _ ≤ |a - c| * e + e * |b - e| := by gcongr
    _ = (|a - c| + |b - e|) * e := by ring
    _ ≤ (|a - c| + |b - e|) * (b * e) := by
      gcongr
      nlinarith only [hb, he0]

variable {n : ℕ}

end

end CoarseDeGiorgi.Foundations.FracGeometry
