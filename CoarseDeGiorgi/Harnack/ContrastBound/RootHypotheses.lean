import CoarseDeGiorgi.Assembly.TwoSidedUniformSelection
import CoarseDeGiorgi.Harnack.ContrastBound.CellPositivity
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Harnack.Moments.MomentComparison

namespace CoarseDeGiorgi.Harnack.ContrastBound

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- The quotient is zero at an infinite lower moment; positive cell responses rule out that
case by forcing the negative-power input in `lowerMoment` to be nonzero. -/
theorem contrast_ge_one_of_root_hypotheses {d : ℕ} (hd : 3 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hUfin : upperMoment a ha s p hs hp.le < ⊤)
    (hLpos : 0 < lowerMoment a ha t q ht hq.le) :
    1 ≤ contrast a ha s t p q hs ht hp.le hq.le := by
  have hd1 : 1 ≤ d := by omega
  have hUpos : 0 < upperMoment a ha s p hs hp.le :=
    Assembly.two_sided_upper_moment_pos (by omega) a ha hs hp.le
  have hLfin : lowerMoment a ha t q ht hq.le < ⊤ :=
    Harnack.ContrastBound.lower_moment_lt_top hd a ha ht hq.le
  have hcomparison := Harnack.Moments.moment_matrix_sandwich hd1 a ha hs ht
    hp.le hq.le hUpos hUfin hLpos hLfin
  have hLleU : lowerMoment a ha t q ht hq.le ≤ upperMoment a ha s p hs hp.le := by
    exact (ENNReal.toReal_le_toReal hLfin.ne hUfin.ne).mp hcomparison.2
  rw [contrast]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hLpos.ne') (Or.inl hLfin.ne)).2
    (by simpa using hLleU)

end CoarseDeGiorgi.Harnack.ContrastBound
