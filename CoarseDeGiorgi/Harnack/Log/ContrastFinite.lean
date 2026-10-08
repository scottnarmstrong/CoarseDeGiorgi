module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.SpatialMomentRange

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization

/-- The moment-range hypothesis makes the contrast finite. -/
theorem contrast_lt_top_of_spatialMomentRange
    {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hs : 0 < s) (ht : 0 < t)
    (hrange : spatialMomentRange a ha p q s t) :
    contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq) < ⊤ := by
  rcases hrange with
    ⟨_hp₁, _hq₁, _hs₁, _ht₁, _hp', _hq', _hs', _ht', _hθ, hUpper, hLower⟩
  unfold contrast
  exact ENNReal.div_lt_top hUpper.ne hLower.ne'

end CoarseDeGiorgi.Harnack.Log
