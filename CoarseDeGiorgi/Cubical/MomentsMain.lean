import CoarseDeGiorgi.Cubical.MomentsFirst
import CoarseDeGiorgi.Statements.UpperCellAverage
import CoarseDeGiorgi.Statements.LowerCellAverage
import CoarseDeGiorgi.Statements.CubeUpperCellAverage
import CoarseDeGiorgi.Statements.CubeLowerCellAverage

/-! # Lemma `l.cubical.simplicial.moments`: cubical and simplicial moments -/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The two-sided comparison for any response interface, with constant `10 d (d+1) + 1`. -/
theorem RespData.moments (D : RespData d) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {p : ℝ} (hp : 1 ≤ p) (k : ℕ) :
    (ENNReal.ofReal (D.cubeAvg a ha k p)).rpow (1 / p) ≤
        (ENNReal.ofReal (D.simplexAvg a ha k p)).rpow (1 / p) ∧
      (ENNReal.ofReal (D.simplexAvg a ha k p)).rpow (1 / p) ≤
        ENNReal.ofReal (10 * d * (d + 1) + 1) *
          ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
            (ENNReal.ofReal (D.cubeAvg a ha (k + l) p)).rpow (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 ≤ 1 / p := by positivity
  refine ⟨ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (first_avg D a ha hp k)) hp1, ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- dimension zero: all norms vanish
    have h0 : ∀ A : Mat 0, ‖A‖ = 0 := fun A => by
      have : A = 0 := Subsingleton.elim _ _
      rw [this, norm_zero]
    have hs : D.simplexAvg a ha k p = 0 := by
      unfold RespData.simplexAvg
      simp [h0, Real.zero_rpow hp0.ne']
    rw [hs, ENNReal.ofReal_zero]
    exact le_of_eq_of_le (ENNReal.zero_rpow_of_pos (by positivity)) bot_le
  · refine (D.second hd a ha hp k).trans ?_
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

/-- Lemma `l.cubical.simplicial.moments` for both responses, with one constant. -/
theorem cubical_simplicial_moments_main (d : ℕ) :
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
              (ENNReal.ofReal (cubeLowerCellAverage a ha (k + l) p)).rpow (1 / p)) := by
  refine ⟨10 * d * (d + 1) + 1, by positivity, fun a ha p hp k => ⟨?_, ?_⟩⟩
  · exact (upperData d).moments a ha hp k
  · exact (lowerData d).moments a ha hp k

end CoarseDeGiorgi.Cubical
