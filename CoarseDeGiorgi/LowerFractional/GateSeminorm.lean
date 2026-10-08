module

public import CoarseDeGiorgi.LowerFractional.Core

/-! Exact seminorm clause used in the lower-fractional proof. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Aliases
open scoped ENNReal

lemma lower_range_t_lt_one {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    {a : CoeffField d} {ha : IsWeightedCoeffOn (Aliases.originCube 1) a}
    (hrange : spatialMomentRange a ha p q s t) : t < 1 := by
  obtain ⟨hp, hq, hs, ht, hp', hq', _, _, htheta, _⟩ := hrange
  have hd' : 3 ≤ (d : ℝ) := Nat.cast_le.mpr hd
  have hloss : 0 ≤ (((d : ℝ) - 1) / 2) * (1 / p + 1 / q) :=
    mul_nonneg (by linarith) (add_nonneg (by positivity) (by positivity))
  unfold paramTheta at htheta
  linarith


end CoarseDeGiorgi.LowerFractional
