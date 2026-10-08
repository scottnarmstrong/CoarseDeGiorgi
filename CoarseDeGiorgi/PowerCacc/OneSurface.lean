module

public import CoarseDeGiorgi.PowerCacc.SelectedCap
public import CoarseDeGiorgi.PowerCacc.CapApprox
public import CoarseDeGiorgi.PowerCacc.Hypotheses
public import CoarseDeGiorgi.Harnack.PowerCaccioppoli.SignedSurface
public import CoarseDeGiorgi.Harnack.PowerCaccioppoli.SurfaceArithmetic
public import CoarseDeGiorgi.Harnack.PowerCaccioppoli.SurfaceParameters
public import CoarseDeGiorgi.Selection.SourceNonnegative
public import CoarseDeGiorgi.Selection.SourceRadius
public import CoarseDeGiorgi.Whitney.SourceWitnessCore
public import CoarseDeGiorgi.Statements.PositiveCap
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.GammaLoc
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution

/-! # The one-surface estimate for powers (Proposition `p.power.caccioppoli`, Step 1)

One smooth sequence `v_i → v`, one good radius from `p.good.radius` (independent of the cap `N`), the caps
`ṽ_i = v_i ∧ N`, and the extension of `p.whitney.extension`,
with the exterior integral bound of `l.exterior.integral`. -/

@[expose] public section

namespace CoarseDeGiorgi.PowerCacc

open Homogenization MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Classical

open Harnack.PowerCaccioppoli

theorem exponent_identity_loc {p q t : ℝ} (hq : 1 < q) :
    1 / (2 * p) + 1 / 2 + (alphaParam t + 1 / paramR q) = gammaLoc p q t := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  have hq1 : q + 1 ≠ 0 := by linarith only [hq]
  unfold paramR gammaLoc alphaParam
  field_simp [hq0, hq1]
  ring

theorem positiveCap_eq_cap {d : ℕ} (v : Vec d → ℝ) (N : ℝ≥0∞) :
    positiveCap v 0 N = Harnack.Selection.selectionCap 0 N v := by
  funext x
  simp [Harnack.Selection.selectionCap, positiveCap, positivePart]

/-- Basic parameter facts: `0 < 1 - t`, `1 - t < 1`, and `-σ' ≤ θ`. -/
theorem power_surface_parameters {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    0 < alphaParam t ∧ alphaParam t < 1 ∧ 0 ≤ sigmaUpper d p s + sigmaLower d q t - t ∧
      -(sigmaUpper d p s + sigmaLower d q t - t) ≤ paramTheta d p q s t := by
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hd']
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have h1 : 0 ≤ ((d : ℝ) - 1) / (2 * p) := by positivity
  have h2 : 0 ≤ ((d : ℝ) - 1) / (2 * q) := by positivity
  have hsum : paramTheta d p q s t + (sigmaUpper d p s + sigmaLower d q t - t) =
      alphaParam t := by
    unfold paramTheta sigmaUpper sigmaLower alphaParam
    ring
  have hσ : 0 ≤ sigmaUpper d p s + sigmaLower d q t - t := by
    unfold sigmaUpper sigmaLower
    linarith only [hs, h1, h2]
  refine ⟨by linarith only [hsum, hθ, hσ], ?_, hσ, by linarith only [hθ, hσ]⟩
  unfold alphaParam
  linarith only [ht]

theorem cap_bounds {d : ℕ} (N : ℝ≥0∞) (hNtop : N ≠ ⊤) (f : Vec d → ℝ) (x : Vec d) :
    0 ≤ Harnack.Selection.selectionCap 0 N f x ∧
      Harnack.Selection.selectionCap 0 N f x ≤ N.toReal := by
  simp only [Harnack.Selection.selectionCap, ite_eq_right hNtop, sub_zero]
  exact ⟨le_min (le_max_right _ _) ENNReal.toReal_nonneg, min_le_right _ _⟩

end CoarseDeGiorgi.PowerCacc
