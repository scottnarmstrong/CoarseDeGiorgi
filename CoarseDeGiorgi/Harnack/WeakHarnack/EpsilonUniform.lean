module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.CrossoverExponent
public import CoarseDeGiorgi.Statements.ChiParam
public import CoarseDeGiorgi.Statements.HarnackEtaParam
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import CoarseDeGiorgi.Statements.NormalizedLpMoment
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Harnack.Calculus.EssentialValues
public import CoarseDeGiorgi.Harnack.ContrastBound.RootHypotheses
public import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas
public import CoarseDeGiorgi.Harnack.WeakHarnack.EpsilonLimit
public import CoarseDeGiorgi.Harnack.Iterations.ExponentRange

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.WeakHarnack

/-- Compose the source crossover product and the opposite moment iteration outputs.
The two source contracts are stated explicitly in normalized-moment form; their
constants are fixed before coefficient and solution data.
-/
theorem weak_harnack_of_uniform_crossover_and_iterations {d : ℕ}
    (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (hcross : ∃ c : ℝ, 0 < c ∧
      c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) ∧
      ∃ Kcross : ℝ, 0 ≤ Kcross ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        upperMoment a ha s p hs hp.le < ⊤ →
        0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
          ∀ (hpC : 0 < pC),
            normalizedLpMoment pC hpC (originCube (3 / 4))
                (fun x => u x + ε) *
              normalizedLpMoment pC hpC (originCube (3 / 4))
                (fun x => (u x + ε)⁻¹) ≤
              ENNReal.ofReal (Real.exp (Kcross / pC)))
    (hiterations : ∀ (c : ℝ), 0 < c →
      c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) →
      ∃ Kiter : ℝ, 0 ≤ Kiter ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        upperMoment a ha s p hs hp.le < ⊤ →
        0 < lowerMoment a ha t q ht hq.le →
        1 ≤ contrast a ha s t p q hs ht hp.le hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
          ∀ (hpC : 0 < pC),
            let Mp := normalizedLpMoment pC hpC (originCube (3 / 4))
              (fun x => u x + ε)
            let Mn := normalizedLpMoment pC hpC (originCube (3 / 4))
              (fun x => (u x + ε)⁻¹)
            0 < Mn ∧ Mn < ⊤ ∧
              Mn⁻¹ ≤ ENNReal.ofReal (Real.exp (Kiter / pC)) *
                nonnegativeEssInf (originCube (1 / 2)) (fun x => u x + ε) ∧
              normalizedLpMoment (harnackEtaParam q) (by
                  dsimp [harnackEtaParam, paramR]
                  positivity)
                (originCube (5 / 8)) (fun x => u x + ε) ≤
                ENNReal.ofReal (Real.exp (Kiter / pC)) * Mp) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        upperMoment a ha s p hs hp.le < ⊤ →
        0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          normalizedLpMoment (harnackEtaParam q) (by
              have _hq0 : 0 < q := lt_trans (by norm_num) hq
              dsimp [harnackEtaParam, paramR]
              positivity)
            (originCube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt
              (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u := by
  rcases hcross with ⟨c, hc, hcRange, Kcross, hKcross, hcross⟩
  obtain ⟨Kiter, hKiter, hiterations⟩ := hiterations c hc hcRange
  let K : ℝ := max Kcross Kiter
  let C : ℝ := 3 * K * Real.sqrt 2 / c
  have hK : 0 ≤ K := by dsimp [K]; exact le_max_of_le_left hKcross
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) (Real.sqrt_nonneg _)) hc.le
  have hη : 0 < harnackEtaParam q := by
    have hq0 : 0 < q := lt_trans (by norm_num) hq
    dsimp [harnackEtaParam, paramR]
    positivity
  have hη1 : harnackEtaParam q ≤ 1 := by
    unfold harnackEtaParam paramR
    have hq0 : 0 < q := lt_trans (by norm_num) hq
    rw [div_le_one (by norm_num : (0 : ℝ) < 4)]
    rw [div_le_iff₀ (by linarith : 0 < q + 1)]
    nlinarith
  have hVpos : 0 < volume (originCube (d := d) (5 / 8)) :=
    Harnack.Scalar.volume_originCube_pos (by norm_num)
  have hVtop : volume (originCube (d := d) (5 / 8)) < ⊤ :=
    lt_of_le_of_lt (Harnack.Scalar.volume_originCube_le_one (by norm_num)) ENNReal.one_lt_top
  refine ⟨C, hC, ?_⟩
  intro a ha hupper hlower u G hu_nonneg hu
  have hNeZero : NeZero d := ⟨by omega⟩
  let Θ : ℝ≥0∞ := contrast a ha s t p q hs ht hp.le hq.le
  have hΘone : 1 ≤ Θ := by
    simpa [Θ] using Harnack.ContrastBound.contrast_ge_one_of_root_hypotheses
      hd a ha hp hq hs ht hupper hlower
  have hΘtop : Θ < ⊤ := by
    dsimp [Θ, contrast]
    exact ENNReal.div_lt_top hupper.ne hlower.ne'
  have hΘreal : 1 ≤ Θ.toReal := ENNReal.toReal_mono hΘtop.ne hΘone
  have hpc : 0 < crossoverExponent c a ha s t p q hs ht hp.le hq.le :=
    crossoverExponent_pos c hc a ha s t p q hs ht hp.le hq.le hΘtop
  have hpceq := crossoverExponent_eq_div_sqrt c a ha s t p q hs ht hp.le hq.le hΘtop
  have hroot : Real.sqrt (1 + Θ.toReal) ≤ Real.sqrt 2 * Real.sqrt Θ.toReal := by
    calc
      Real.sqrt (1 + Θ.toReal) ≤ Real.sqrt (2 * Θ.toReal) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      _ = Real.sqrt 2 * Real.sqrt Θ.toReal :=
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Θ.toReal
  have harg : 3 * K / crossoverExponent c a ha s t p q hs ht hp.le hq.le ≤
      C * Real.sqrt Θ.toReal := by
    have hargEq : 3 * K / crossoverExponent c a ha s t p q hs ht hp.le hq.le =
        (3 * K / c) * Real.sqrt (1 + Θ.toReal) := by
      rw [hpceq]
      have hsqrtpos : 0 < Real.sqrt (1 + Θ.toReal) := by positivity
      field_simp [hc.ne', hsqrtpos.ne']
      ring
    calc
      _ = (3 * K / c) * Real.sqrt (1 + Θ.toReal) := hargEq
      _ ≤ (3 * K / c) * (Real.sqrt 2 * Real.sqrt Θ.toReal) := by
        exact mul_le_mul_of_nonneg_left hroot (div_nonneg (mul_nonneg (by norm_num) hK) hc.le)
      _ = C * Real.sqrt Θ.toReal := by dsimp [C]; ring
  have hcoef : ENNReal.ofReal
      (Real.exp (3 * K / crossoverExponent c a ha s t p q hs ht hp.le hq.le)) ≤
      ENNReal.ofReal (Real.exp (C * Real.sqrt Θ.toReal)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr harg)
  have hhalfSubset : originCube (d := d) (1 / 2) ⊆ originCube 1 := by
    intro x hx i
    dsimp [originCube] at hx ⊢
    constructor <;> linarith [hx i]
  have huHalf : 0 ≤ᵐ[volume.restrict (originCube (1 / 2))] u :=
    ae_restrict_of_ae_restrict_of_subset hhalfSubset hu_nonneg
  let m := nonnegativeEssInf (originCube (1 / 2)) u
  have hconstant (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
      normalizedLpMoment (harnackEtaParam q) hη
          (originCube (5 / 8)) (fun x => u x + ε) ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt Θ.toReal)) *
          (m + ENNReal.ofReal ε) := by
    let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
    have hpc' : 0 < pC := by simpa [pC] using hpc
    have hpctop : pC < 1 := by
      have hrange := Iterations.ruled_exponent_range_of_moment_comparison hd p q s t
        hp hq hs ht _hθ a ha ⟨hΘone, hΘtop⟩ c hc hcRange
      dsimp [pC]
      exact lt_trans hrange.2.2.1 (by
        have hq0 : 0 < q := lt_trans (by norm_num) hq
        unfold paramR
        rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
        rw [div_lt_iff₀ (by linarith : 0 < q + 1)]
        nlinarith)
    have hCross := hcross a ha hupper hlower u G hu_nonneg hu ε hε hε1 hpc'
    have hIter := hiterations a ha hupper hlower hΘone
      u G hu_nonneg hu ε hε hε1 hpc'
    obtain ⟨hMnpos, hMntop, hneg, hpos⟩ := hIter
    let Mp := normalizedLpMoment pC hpc' (originCube (3 / 4)) (fun x => u x + ε)
    let Mn := normalizedLpMoment pC hpc' (originCube (3 / 4)) (fun x => (u x + ε)⁻¹)
    have hMnCancel : Mn * Mn⁻¹ = 1 := ENNReal.mul_inv_cancel (ne_of_gt hMnpos) hMntop.ne
    have hMp : Mp ≤ ENNReal.ofReal (Real.exp (Kcross / pC)) * Mn⁻¹ := by
      calc
        Mp = Mp * (Mn * Mn⁻¹) := by simp [hMnCancel]
        _ = (Mp * Mn) * Mn⁻¹ := by rw [mul_assoc]
        _ ≤ ENNReal.ofReal (Real.exp (Kcross / pC)) * Mn⁻¹ :=
          by gcongr
    let Ex : ℝ≥0∞ := ENNReal.ofReal (Real.exp (Kcross / pC))
    let Ei : ℝ≥0∞ := ENNReal.ofReal (Real.exp (Kiter / pC))
    let E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (K / pC))
    have hEx : Ex ≤ E := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hpc'.le
      exact le_max_left _ _
    have hEi : Ei ≤ E := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ hpc'.le
      exact le_max_right _ _
    have hQ := calc
      normalizedLpMoment (harnackEtaParam q) hη (originCube (5 / 8))
          (fun x => u x + ε) ≤ Ei * Mp := by simpa [Ei, Mp] using hpos
      _ ≤ Ei * (Ex * Mn⁻¹) := by gcongr
      _ ≤ Ei * (Ex * (Ei * nonnegativeEssInf (originCube (1 / 2))
          (fun x => u x + ε))) := by gcongr
      _ ≤ E * (E * (E * nonnegativeEssInf (originCube (1 / 2))
          (fun x => u x + ε))) := by gcongr
      _ = E * E * E * nonnegativeEssInf (originCube (1 / 2))
          (fun x => u x + ε) := by ac_rfl
    have hE3 : E * E * E =
        ENNReal.ofReal (Real.exp (3 * K / pC)) := by
      dsimp [E]
      calc
        _ = ENNReal.ofReal
            (Real.exp (K / pC) * Real.exp (K / pC) * Real.exp (K / pC)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal (Real.exp (3 * K / pC)) := by
          congr 1
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1; ring
    have hessShift := Harnack.Calculus.nonnegativeEssInf_add_const
      (originCube (d := d) (1 / 2)) u huHalf ε hε.le
    have hQ' : normalizedLpMoment (harnackEtaParam q) hη
        (originCube (5 / 8)) (fun x => u x + ε) ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt Θ.toReal)) *
          (m + ENNReal.ofReal ε) := by
      calc
        _ ≤ E * E * E * nonnegativeEssInf (originCube (1 / 2))
            (fun x => u x + ε) := hQ
        _ = ENNReal.ofReal (Real.exp (3 * K / pC)) *
            nonnegativeEssInf (originCube (1 / 2)) (fun x => u x + ε) := by rw [hE3]
        _ ≤ ENNReal.ofReal (Real.exp (C * Real.sqrt Θ.toReal)) *
            nonnegativeEssInf (originCube (1 / 2)) (fun x => u x + ε) :=
          mul_le_mul_of_nonneg_right (by simpa [pC] using hcoef) (by positivity)
        _ = ENNReal.ofReal (Real.exp (C * Real.sqrt Θ.toReal)) *
            (m + ENNReal.ofReal ε) := by rw [hessShift]
    exact hQ'
  have hlim := normalizedLpMoment_epsilon_limit (originCube (d := d) (5 / 8)) u
    (harnackEtaParam q) hη hη1 hVpos hVtop
    (ae_restrict_of_ae_restrict_of_subset
      (by
        intro x hx i
        dsimp [originCube] at hx ⊢
        constructor <;> linarith [hx i]) hu_nonneg)
    (weightedSupersolution_integrable_fiveEighths ha hu)
    (ENNReal.ofReal (Real.exp (C * Real.sqrt Θ.toReal))) m
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)) ENNReal.ofReal_lt_top
    hconstant
  simpa [m, Θ] using hlim

end CoarseDeGiorgi.Harnack.WeakHarnack
