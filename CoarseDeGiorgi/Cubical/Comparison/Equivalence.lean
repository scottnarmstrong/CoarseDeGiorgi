module

public import CoarseDeGiorgi.Cubical.Comparison.Compare
public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.CubeUpperMoment
public import CoarseDeGiorgi.Statements.CubeLowerMoment
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube

/-!
# Proposition `p.cubical.simplicial.equivalence` from Lemma `l.cubical.simplicial.moments` (conditional)

The helpers take the statement of Lemma `l.cubical.simplicial.moments` (`CoarseDeGiorgi.cubical_simplicial_moments d`) as a hypothesis,
`CubicalSimplicialMoments d`, supplied by `CoarseDeGiorgi.cubical_simplicial_moments d`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Cubical

/-- The statement of Lemma `l.cubical.simplicial.moments`, copied verbatim (the proposition after the colon). -/
abbrev CubicalSimplicialMoments (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
        (p : ℝ), 1 ≤ p → ∀ k : ℕ,
      ((ENNReal.ofReal (cubeUpperCellAverage a ha k p)).rpow (1 / p) ≤
          (ENNReal.ofReal (upperCellAverage a ha k p)).rpow (1 / p) ∧
        (ENNReal.ofReal (upperCellAverage a ha k p)).rpow (1 / p) ≤
          ENNReal.ofReal C *
            ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
              (ENNReal.ofReal (cubeUpperCellAverage a ha (k + l) p)).rpow (1 / p)) ∧
      ((ENNReal.ofReal (cubeLowerCellAverage a ha k p)).rpow (1 / p) ≤
          (ENNReal.ofReal (lowerCellAverage a ha k p)).rpow (1 / p) ∧
        (ENNReal.ofReal (lowerCellAverage a ha k p)).rpow (1 / p) ≤
          ENNReal.ofReal C *
            ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
              (ENNReal.ofReal (cubeLowerCellAverage a ha (k + l) p)).rpow (1 / p))

/-- The weighted sum `∑_k 3^{-ks} (X k)^{1/(2p)}` in `ℝ≥0∞`. -/
noncomputable def wsum (s p : ℝ) (X : ℕ → ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * (ENNReal.ofReal (X k)) ^ (1 / (2 * p))

theorem wsum_mono (s p : ℝ) (hp : 1 ≤ p) (X Y : ℕ → ℝ)
    (h : ∀ k, (ENNReal.ofReal (Y k)).rpow (1 / p) ≤ (ENNReal.ofReal (X k)).rpow (1 / p)) :
    wsum s p Y ≤ wsum s p X := by
  have hp0 : 0 < p := by linarith
  refine ENNReal.tsum_le_tsum fun k => ?_
  have h1 : ENNReal.ofReal (Y k) ≤ ENNReal.ofReal (X k) :=
    (ENNReal.rpow_le_rpow_iff (by positivity : 0 < 1 / p)).1 (h k)
  exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow h1 (by positivity))

theorem sq_inv_anti {x y : ℝ≥0∞} (h : x ≤ y) : (y ^ 2)⁻¹ ≤ (x ^ 2)⁻¹ :=
  ENNReal.inv_le_inv.2 (pow_le_pow_left' h 2)

theorem sq_inv_const {x y : ℝ≥0∞} {K : ℝ} (hK : 0 < K) (h : x ≤ ENNReal.ofReal K * y) :
    ENNReal.ofReal (K ^ 2)⁻¹ * (y ^ 2)⁻¹ ≤ (x ^ 2)⁻¹ := by
  have h1 : (ENNReal.ofReal K * y) ^ 2 ≥ x ^ 2 := pow_le_pow_left' h 2
  have h2 := ENNReal.inv_le_inv.2 h1
  refine le_trans (le_of_eq ?_) h2
  rw [mul_pow, ENNReal.mul_inv (Or.inl (by simp [hK])) (Or.inl (by simp)),
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow hK.le]

/-- Proposition `p.cubical.simplicial.equivalence`, conditional on Lemma `l.cubical.simplicial.moments`. -/
theorem cubical_simplicial_equivalence_of_moments (d : ℕ) (hC1 : CubicalSimplicialMoments d)
    (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        (cubeUpperMoment a ha s p hs hp.le ≤ upperMoment a ha s p hs hp.le ∧
          upperMoment a ha s p hs hp.le ≤
            ENNReal.ofReal C * cubeUpperMoment a ha s p hs hp.le) ∧
        (ENNReal.ofReal C⁻¹ * cubeLowerMoment a ha t q ht hq.le ≤ lowerMoment a ha t q ht hq.le ∧
          lowerMoment a ha t q ht hq.le ≤ cubeLowerMoment a ha t q ht hq.le) := by
  obtain ⟨C0, hC0, hall⟩ := hC1
  obtain ⟨Ku, hKu, hu⟩ := sum_le_const_mul p s C0 hp hs _hsp hC0
  obtain ⟨Kl, hKl, hl⟩ := sum_le_const_mul q t C0 hq ht _htq hC0
  refine ⟨max (Ku ^ 2) (Kl ^ 2), lt_max_of_lt_left (by positivity), fun a ha => ?_⟩
  have hCpos : 0 < max (Ku ^ 2) (Kl ^ 2) := lt_max_of_lt_left (by positivity)
  set cs : ℝ≥0∞ := ENNReal.ofReal (1 - Real.rpow 3 (-s)) with hcs
  set ct : ℝ≥0∞ := ENNReal.ofReal (1 - Real.rpow 3 (-t)) with hct
  have hU1 : wsum s p (cubeUpperCellAverage a ha · p) ≤ wsum s p (upperCellAverage a ha · p) :=
    wsum_mono s p hp.le _ _ fun k => ((hall a ha p hp.le k).1.1)
  have hU2 : wsum s p (upperCellAverage a ha · p) ≤
      ENNReal.ofReal Ku * wsum s p (cubeUpperCellAverage a ha · p) :=
    hu _ _ fun k => (hall a ha p hp.le k).1.2
  have hL1 : wsum t q (cubeLowerCellAverage a ha · q) ≤ wsum t q (lowerCellAverage a ha · q) :=
    wsum_mono t q hq.le _ _ fun k => ((hall a ha q hq.le k).2.1)
  have hL2 : wsum t q (lowerCellAverage a ha · q) ≤
      ENNReal.ofReal Kl * wsum t q (cubeLowerCellAverage a ha · q) :=
    hl _ _ fun k => (hall a ha q hq.le k).2.2
  have hUp : upperMoment a ha s p hs hp.le = (cs * wsum s p (upperCellAverage a ha · p)) ^ 2 := rfl
  have hUt : cubeUpperMoment a ha s p hs hp.le =
      (cs * wsum s p (cubeUpperCellAverage a ha · p)) ^ 2 := rfl
  have hLo : lowerMoment a ha t q ht hq.le =
      (ct * wsum t q (lowerCellAverage a ha · q)).rpow (-2) := rfl
  have hLt : cubeLowerMoment a ha t q ht hq.le =
      (ct * wsum t q (cubeLowerCellAverage a ha · q)).rpow (-2) := rfl
  have hneg : ∀ z : ℝ≥0∞, z.rpow (-2) = (z ^ 2)⁻¹ := fun z => by
    show z ^ (-2 : ℝ) = _
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, ENNReal.rpow_neg, ENNReal.rpow_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hUp, hUt]; gcongr
  · rw [hUp, hUt]
    calc (cs * wsum s p (upperCellAverage a ha · p)) ^ 2
        ≤ (cs * (ENNReal.ofReal Ku * wsum s p (cubeUpperCellAverage a ha · p))) ^ 2 := by gcongr
      _ = ENNReal.ofReal (Ku ^ 2) * (cs * wsum s p (cubeUpperCellAverage a ha · p)) ^ 2 := by
          rw [ENNReal.ofReal_pow hKu.le]; ring
      _ ≤ ENNReal.ofReal (max (Ku ^ 2) (Kl ^ 2)) *
            (cs * wsum s p (cubeUpperCellAverage a ha · p)) ^ 2 := by
          gcongr; exact le_max_left _ _
  · rw [hLo, hLt, hneg, hneg]
    have h := sq_inv_const hKl (x := ct * wsum t q (lowerCellAverage a ha · q))
      (y := ct * wsum t q (cubeLowerCellAverage a ha · q)) (by
        calc ct * wsum t q (lowerCellAverage a ha · q)
            ≤ ct * (ENNReal.ofReal Kl * wsum t q (cubeLowerCellAverage a ha · q)) := by gcongr
          _ = ENNReal.ofReal Kl * (ct * wsum t q (cubeLowerCellAverage a ha · q)) := by ring)
    refine le_trans ?_ h
    gcongr
    exact le_max_right _ _
  · rw [hLo, hLt, hneg, hneg]
    exact sq_inv_anti (by gcongr)

/-- Proposition `p.cubical.simplicial.equivalence`, constant one, conditional on Lemma `l.cubical.simplicial.moments`. -/
theorem cubical_simplicial_equivalence_const_one_of_moments (d : ℕ) (hC1 : CubicalSimplicialMoments d)
    (p q s t : ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 0 < s) (ht : 0 < t)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) :
    cubeUpperMoment a ha s p hs hp ≤ upperMoment a ha s p hs hp ∧
      lowerMoment a ha t q ht hq ≤ cubeLowerMoment a ha t q ht hq := by
  obtain ⟨C0, hC0, hall⟩ := hC1
  have hU1 : wsum s p (cubeUpperCellAverage a ha · p) ≤ wsum s p (upperCellAverage a ha · p) :=
    wsum_mono s p hp _ _ fun k => ((hall a ha p hp k).1.1)
  have hL1 : wsum t q (cubeLowerCellAverage a ha · q) ≤ wsum t q (lowerCellAverage a ha · q) :=
    wsum_mono t q hq _ _ fun k => ((hall a ha q hq k).2.1)
  have hneg : ∀ z : ℝ≥0∞, z.rpow (-2) = (z ^ 2)⁻¹ := fun z => by
    show z ^ (-2 : ℝ) = _
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, ENNReal.rpow_neg, ENNReal.rpow_two]
  constructor
  · show (ENNReal.ofReal (1 - Real.rpow 3 (-s)) * wsum s p (cubeUpperCellAverage a ha · p)) ^ 2 ≤
      (ENNReal.ofReal (1 - Real.rpow 3 (-s)) * wsum s p (upperCellAverage a ha · p)) ^ 2
    gcongr
  · show (ENNReal.ofReal (1 - Real.rpow 3 (-t)) * wsum t q (lowerCellAverage a ha · q)).rpow (-2) ≤
      (ENNReal.ofReal (1 - Real.rpow 3 (-t)) * wsum t q (cubeLowerCellAverage a ha · q)).rpow (-2)
    rw [hneg, hneg]
    exact sq_inv_anti (by gcongr)

end CoarseDeGiorgi.Cubical
