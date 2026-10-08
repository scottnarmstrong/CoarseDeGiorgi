import CoarseDeGiorgi.Statements.CubicalSimplicialEquivalence
import CoarseDeGiorgi.Statements.CubicalRatioComparison
import CoarseDeGiorgi.Statements.LocalBoundedness
import CoarseDeGiorgi.Statements.Harnack
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.IsWeightedSubsolution
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.LocallyBoundedAbove
import CoarseDeGiorgi.Statements.NonnegativeEssInf
import CoarseDeGiorgi.Statements.NormalizedLpMoment
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.PositivePart
import CoarseDeGiorgi.Statements.RStarParam

/-!
# Theorems A, C and Corollary B with `Θ̃`

The moment conditions transfer by Proposition `p.cubical.simplicial.equivalence`, and the contrast
by `e.cubical.simplicial.ratio`. The weak Harnack helper additionally takes the statement of
`weak_harnack_range` as the hypothesis `hW`.
-/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Cubical

/-- Transfer of the moment conditions and of the contrast from cubes to simplices. -/
theorem transfer (d : ℕ) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hsp : s < (1 / 2) * (1 - 1 / p)) (htq : t < (1 / 2) * (1 - 1 / q)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        cubeUpperMoment a ha s p hs hp.le < ⊤ → 0 < cubeLowerMoment a ha t q ht hq.le →
          upperMoment a ha s p hs hp.le < ⊤ ∧ 0 < lowerMoment a ha t q ht hq.le ∧
          cubeContrast a ha s t p q hs ht hp.le hq.le < ⊤ ∧
          contrast a ha s t p q hs ht hp.le hq.le ≤
            ENNReal.ofReal C * cubeContrast a ha s t p q hs ht hp.le hq.le := by
  obtain ⟨Ce, hCe, he⟩ := CoarseDeGiorgi.cubical_simplicial_equivalence d p q s t hp hq hs ht hsp htq
  obtain ⟨Cr, hCr, hr⟩ := CoarseDeGiorgi.cubical_ratio_comparison d p q s t hp hq hs ht hsp htq
  refine ⟨Cr, hCr, fun a ha h1 h2 => ⟨?_, ?_, ?_, (hr a ha).2⟩⟩
  · exact lt_of_le_of_lt (he a ha).1.2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1)
  · refine lt_of_lt_of_le ?_ (he a ha).2.1
    exact ENNReal.mul_pos (by simp [hCe]) h2.ne'
  · exact ENNReal.div_lt_top h1.ne h2.ne'

theorem rhs_le (CA C e : ℝ) (hCA : 0 ≤ CA) (hC : 0 < C) (he : 0 ≤ e) (R T T' N : ℝ≥0∞)
    (h : T ≤ ENNReal.ofReal C * T') :
    ENNReal.ofReal CA * R * T ^ e * N ≤ ENNReal.ofReal (CA * C ^ e) * R * T' ^ e * N := by
  have hT : T ^ e ≤ ENNReal.ofReal (C ^ e) * T' ^ e := by
    calc T ^ e ≤ (ENNReal.ofReal C * T') ^ e := ENNReal.rpow_le_rpow h he
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ he, ENNReal.ofReal_rpow_of_pos hC]
  calc ENNReal.ofReal CA * R * T ^ e * N
      ≤ ENNReal.ofReal CA * R * (ENNReal.ofReal (C ^ e) * T' ^ e) * N := by gcongr
    _ = _ := by rw [ENNReal.ofReal_mul hCA]; ring

/-- Theorem A and Corollary B with `Θ̃` from Proposition `p.cubical.simplicial.equivalence`. -/
theorem local_boundedness_cubical_of_equivalence (d : ℕ)
    (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q)) :
    ∃ γ : ℝ, 0 < γ ∧
      ((∃ C_A : ℝ, 0 ≤ C_A ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          cubeUpperMoment a ha s p hs hp.le < ⊤ →
          0 < cubeLowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (originCube 1) u G →
          LocallyBoundedAbove (originCube 1) u ∧
          ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
          let rhs := ENNReal.ofReal C_A *
            (ENNReal.ofReal (R - ρ)).rpow (-γ) *
            (cubeContrast a ha s t p q hs ht hp.le hq.le).rpow ((d - 1 : ℝ) / (4 * paramTheta d p q s t)) *
            eLpNorm (positivePart u) 2 (volume.restrict (originCube R))
          eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤ rhs ∧
            (R < 1 → eLpNorm (positivePart u) 2
              (volume.restrict (originCube R)) < ⊤)) ∧
      (∀ η : ℝ, 0 < η → η < 2 →
        ∃ C_η : ℝ, 0 ≤ C_η ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          cubeUpperMoment a ha s p hs hp.le < ⊤ →
          0 < cubeLowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (originCube 1) u G →
          ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
          let rhs := ENNReal.ofReal C_η *
            (ENNReal.ofReal (R - ρ)).rpow (-(2 * γ / η)) *
            (cubeContrast a ha s t p q hs ht hp.le hq.le).rpow ((d - 1 : ℝ) / (2 * η * paramTheta d p q s t)) *
            eLpNorm (positivePart u) (ENNReal.ofReal η) (volume.restrict (originCube R))
          eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤ rhs ∧
            (R < 1 → eLpNorm (positivePart u) (ENNReal.ofReal η)
              (volume.restrict (originCube R)) < ⊤))) := by
  obtain ⟨C, hC, hT⟩ := transfer d p q s t hp hq hs ht _hsp _htq
  obtain ⟨γ, hγ, ⟨CA, hCA, hA⟩, hB⟩ := local_boundedness d _hd p q s t hp hq hs ht _hθ
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast _hd
    linarith
  refine ⟨γ, hγ, ⟨CA * C ^ ((d - 1 : ℝ) / (4 * paramTheta d p q s t)), ?_, ?_⟩, ?_⟩
  · positivity
  · intro a ha h1 h2 u G hsub
    obtain ⟨hU, hL, -, hΘ⟩ := hT a ha h1 h2
    obtain ⟨hlb, hrest⟩ := hA a ha hU hL u G hsub
    refine ⟨hlb, fun ρ R h h' h'' => ?_⟩
    have key := hrest ρ R h h' h''
    dsimp only at key ⊢
    refine ⟨le_trans key.1 (rhs_le _ _ _ hCA hC (by positivity) _ _ _ _ hΘ), key.2⟩
  · intro η h0 h2
    obtain ⟨Cη, hCη, hA'⟩ := hB η h0 h2
    refine ⟨Cη * C ^ ((d - 1 : ℝ) / (2 * η * paramTheta d p q s t)), by positivity, ?_⟩
    intro a ha h1 h3 u G hsub ρ R h h' h''
    obtain ⟨hU, hL, -, hΘ⟩ := hT a ha h1 h3
    have key := hA' a ha hU hL u G hsub ρ R h h' h''
    dsimp only at key ⊢
    exact ⟨le_trans key.1 (rhs_le _ _ _ hCη hC (by positivity) _ _ _ _ hΘ), key.2⟩

/-- The Harnack inequality with `Θ̃` from Proposition `p.cubical.simplicial.equivalence`. -/
theorem harnack_cubical_of_equivalence (d : ℕ)
    (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q)) :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          cubeUpperMoment a ha s p hs hp.le < ⊤ →
          0 < cubeLowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSolution a (originCube 1) u G →
          eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (cubeContrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u := by
  obtain ⟨C, hC, hT⟩ := transfer d p q s t hp hq hs ht _hsp _htq
  obtain ⟨C0, hC0, hH⟩ := harnack d _hd p q s t hp hq hs ht _hθ
  refine ⟨C0 * Real.sqrt C, by positivity, fun a ha h1 h2 u G hu hsol => ?_⟩
  obtain ⟨hU, hL, hfin, hΘ⟩ := hT a ha h1 h2
  refine le_trans (hH a ha hU hL u G hu hsol) ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
  have h3 : (contrast a ha s t p q hs ht hp.le hq.le).toReal ≤
      C * (cubeContrast a ha s t p q hs ht hp.le hq.le).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hΘ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] at this
  calc C0 * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal
      ≤ C0 * Real.sqrt (C * (cubeContrast a ha s t p q hs ht hp.le hq.le).toReal) := by
        gcongr
    _ = C0 * Real.sqrt C * Real.sqrt (cubeContrast a ha s t p q hs ht hp.le hq.le).toReal := by
        rw [Real.sqrt_mul hC.le]; ring

/-- The weak Harnack inequality with `Θ̃`, conditional on the statement of
`weak_harnack_range` at the arguments `d p q s t`. -/
theorem weak_harnack_cubical_of_equivalence (d : ℕ)
    (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q))
    (hW : ∀ (η : ℝ) (hη : 0 < η), η ≤ rStarParam (d := d) q t / 2 →
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          normalizedLpMoment η hη (originCube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u) :
    ∀ (η : ℝ) (hη : 0 < η), η ≤ rStarParam (d := d) q t / 2 →
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          cubeUpperMoment a ha s p hs hp.le < ⊤ →
          0 < cubeLowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          normalizedLpMoment η hη (originCube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (cubeContrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u := by
  intro η hη hηr
  obtain ⟨C, hC, hT⟩ := transfer d p q s t hp hq hs ht _hsp _htq
  obtain ⟨C0, hC0, hH⟩ := hW η hη hηr
  refine ⟨C0 * Real.sqrt C, by positivity, fun a ha h1 h2 u G hu hsol => ?_⟩
  obtain ⟨hU, hL, hfin, hΘ⟩ := hT a ha h1 h2
  refine le_trans (hH a ha hU hL u G hu hsol) ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
  have h3 : (contrast a ha s t p q hs ht hp.le hq.le).toReal ≤
      C * (cubeContrast a ha s t p q hs ht hp.le hq.le).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hΘ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] at this
  calc C0 * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal
      ≤ C0 * Real.sqrt (C * (cubeContrast a ha s t p q hs ht hp.le hq.le).toReal) := by
        gcongr
    _ = C0 * Real.sqrt C * Real.sqrt (cubeContrast a ha s t p q hs ht hp.le hq.le).toReal := by
        rw [Real.sqrt_mul hC.le]; ring

end CoarseDeGiorgi.Cubical
