module

public import CoarseDeGiorgi.Weighted.Truncation.Algebra

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The scalar truncation `T_N t = max {-N, min {t,N}}` of `i.weighted.chain`. -/
def truncate (N t : ℝ) : ℝ := max (-N) (min t N)

/-- The positive-part decomposition of `T_N`, used in the proof of `i.weighted.chain`. -/
theorem truncate_eq_posParts {N : ℝ} (hN : 0 ≤ N) (t : ℝ) :
    truncate N t = -N + max (t - -N) 0 - max (t - N) 0 := by
  unfold truncate
  rcases le_or_gt t (-N) with ht | ht
  · rw [min_eq_left (by linarith), max_eq_left ht,
      max_eq_right (sub_nonpos.mpr ht), max_eq_right (by linarith)]
    ring
  · rcases le_or_gt t N with h | h
    · rw [min_eq_left h, max_eq_right ht.le, max_eq_left (by linarith),
        max_eq_right (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h.le, max_eq_right (by linarith),
        max_eq_left (by linarith), max_eq_left (sub_nonneg.mpr h.le)]
      ring

/-- Locality identifies the difference of level gradients with the strict truncation gradient. -/
theorem truncation_gradient_ae (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G) {N : ℝ} (hN : 0 < N) :
    ({x | -N < u x}.indicator G - {x | N < u x}.indicator G)
      =ᵐ[volume.restrict V] {x | |u x| < N}.indicator G := by
  filter_upwards [MemH1a.gradient_zero_on_level hV hne ha hu N] with x hx
  by_cases heq : u x = N
  · have hz : G x = 0 := by simpa [heq] using hx
    simp [Set.indicator_apply, heq, hz]
  · by_cases hlo : -N < u x
    · by_cases hhi : N < u x
      · have habs : ¬ |u x| < N := by
          intro h
          exact (abs_lt.mp h).2.not_gt hhi
        simp [hlo, hhi, habs]
      · have hlt : u x < N := lt_of_le_of_ne (le_of_not_gt hhi) heq
        have habs : |u x| < N := abs_lt.mpr ⟨hlo, hlt⟩
        simp [hlo, hhi, habs]
    · have hhi : ¬ N < u x := by linarith only [hN, hlo]
      have habs : ¬ |u x| < N := by
        intro h
        exact hlo (abs_lt.mp h).1
      simp [hlo, hhi, habs]

/-- The exact truncation gradient display `e.weighted.truncation.gradients`, with membership. -/
theorem MemH1a.truncation (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G) {N : ℝ} (hN : 0 < N) :
    CoarseDeGiorgi.MemH1a a V (fun x => truncate N (u x))
      ({x | |u x| < N}.indicator G) := by
  have hp := MemH1a.max_sub_const hV hne ha hu (-N)
  have hm := MemH1a.max_sub_const hV hne ha hu N
  have hd := MemH1a.add hV hne ha hp (MemH1a.neg hV hne ha hm)
  have ht := MemH1a.add_const hV hne ha hd (-N)
  apply MemH1a.congr_ae ht _ (truncation_gradient_ae hV hne ha hu hN)
  filter_upwards with x
  change max (u x - -N) 0 + -max (u x - N) 0 + -N = truncate N (u x)
  rw [truncate_eq_posParts hN.le]
  ring

omit [NeZero d] in
/-- Truncation does not increase the literal weighted energy. -/
theorem energy_truncate_le (ha : IsWeightedCoeffOn V a) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (N : ℝ) :
    weightedEnergy a V ({x | |u x| < N}.indicator G) ≤ weightedEnergy a V G := by
  have hh := energy_mul_le ha (G := G) (b := fun x => if |u x| < N then 1 else 0)
    (M := 1) (Eventually.of_forall fun x => by split_ifs <;> norm_num)
  have heq : (fun x => (if |u x| < N then (1 : ℝ) else 0) • G x) =
      {x | |u x| < N}.indicator G := by
    funext x
    by_cases hx : |u x| < N <;> simp [hx]
  rw [heq] at hh
  simpa only [one_pow, ENNReal.ofReal_one, one_mul] using hh

end CoarseDeGiorgi.Weighted
