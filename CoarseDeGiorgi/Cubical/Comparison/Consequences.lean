import CoarseDeGiorgi.Statements.CubicalSimplicialEquivalence
import CoarseDeGiorgi.Statements.CubicalSimplicialEquivalenceConstOne
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.CubeContrast
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.CubeSpatialMomentRange

/-!
# Consequences of Proposition `p.cubical.simplicial.equivalence`

The inequalities with constant one, the equivalence of the conditions `e.spatial.moment.range`, and `e.cubical.simplicial.ratio`.
-/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Cubical

/-- The condition `e.spatial.moment.range` is equivalent to its cubical version from Proposition `p.cubical.simplicial.equivalence`. -/
theorem cubical_condition_iff_of_equivalence (d : ℕ)
    (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q))
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) :
    spatialMomentRange a ha p q s t ↔ cubeSpatialMomentRange a ha p q s t := by
  obtain ⟨C, hC, h⟩ := CoarseDeGiorgi.cubical_simplicial_equivalence d p q s t hp hq hs ht _hsp _htq
  obtain ⟨⟨_, hU2⟩, hL1, _⟩ := h a ha
  obtain ⟨hU1, hL2⟩ := CoarseDeGiorgi.cubical_simplicial_equivalence_const_one
    d p q s t hp.le hq.le hs ht a ha
  have hCt : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hup : upperMoment a ha s p hs hp.le < ⊤ ↔ cubeUpperMoment a ha s p hs hp.le < ⊤ := by
    constructor
    · intro h; exact lt_of_le_of_lt hU1 h
    · intro h; exact lt_of_le_of_lt hU2 (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top) h)
  have hlo : 0 < lowerMoment a ha t q ht hq.le ↔ 0 < cubeLowerMoment a ha t q ht hq.le := by
    constructor
    · intro h; exact lt_of_lt_of_le h hL2
    · intro h
      refine lt_of_lt_of_le ?_ hL1
      exact ENNReal.mul_pos (by simp [hC]) h.ne'
  constructor
  · rintro ⟨hp', hq', hs', ht', h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨hp', hq', hs', ht', h1, h2, h3, h4, h5, hup.1 h6, hlo.1 h7⟩
  · rintro ⟨hp', hq', hs', ht', h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨hp', hq', hs', ht', h1, h2, h3, h4, h5, hup.2 h6, hlo.2 h7⟩

/-- `e.cubical.simplicial.ratio` from Proposition `p.cubical.simplicial.equivalence`. -/
theorem cubical_ratio_comparison_of_equivalence (d : ℕ)
    (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        cubeContrast a ha s t p q hs ht hp.le hq.le ≤ contrast a ha s t p q hs ht hp.le hq.le ∧
          contrast a ha s t p q hs ht hp.le hq.le ≤
            ENNReal.ofReal C * cubeContrast a ha s t p q hs ht hp.le hq.le := by
  obtain ⟨C, hC, h⟩ := CoarseDeGiorgi.cubical_simplicial_equivalence d p q s t hp hq hs ht _hsp _htq
  refine ⟨C * C, mul_pos hC hC, fun a ha => ?_⟩
  obtain ⟨⟨_, hU2⟩, hL1, _⟩ := h a ha
  obtain ⟨hU1, hL2⟩ := CoarseDeGiorgi.cubical_simplicial_equivalence_const_one
    d p q s t hp.le hq.le hs ht a ha
  constructor
  · exact ENNReal.div_le_div hU1 hL2
  · show _ / _ ≤ ENNReal.ofReal (C * C) * (_ / _)
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    have hinv : (ENNReal.ofReal C⁻¹ * cubeLowerMoment a ha t q ht hq.le)⁻¹ =
        ENNReal.ofReal C * (cubeLowerMoment a ha t q ht hq.le)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl (by simp [hC])) (Or.inl ENNReal.ofReal_ne_top),
        ← ENNReal.ofReal_inv_of_pos (by positivity), inv_inv]
    calc (lowerMoment a ha t q ht hq.le)⁻¹ * upperMoment a ha s p hs hp.le
        ≤ (ENNReal.ofReal C⁻¹ * cubeLowerMoment a ha t q ht hq.le)⁻¹ *
            (ENNReal.ofReal C * cubeUpperMoment a ha s p hs hp.le) := by
          gcongr
      _ = ENNReal.ofReal (C * C) * ((cubeLowerMoment a ha t q ht hq.le)⁻¹ *
            cubeUpperMoment a ha s p hs hp.le) := by
          rw [hinv, ENNReal.ofReal_mul hC.le]; ring

end CoarseDeGiorgi.Cubical
