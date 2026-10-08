import CoarseDeGiorgi.Whitney.Harmonic.Eq66Wide

/-! The energy estimate `e.extension.scale` with the extra factor `A_j(τ)`. -/

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Matrix.Norms.L2Operator
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

theorem tsum_energy_le [NeZero d] (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    {a : CoeffField d} (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {f : Vec d → ℝ} {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH)
    (j : ℕ) (R : ℝ≥0∞)
    (hsum : ∑' cell : CoarseDeGiorgi.whitneySimplicesNearSize (d := d) τ h j,
      ∫⁻ x in CoarseDeGiorgi.exteriorCellSet cell.1,
        ENNReal.ofReal (vecNormSq (CoarseDeGiorgi.smoothGrad
          (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x)) ≤ R) :
    ∑' cell : CoarseDeGiorgi.whitneySimplicesNearSize (d := d) τ h j,
      weightedEnergy a (CoarseDeGiorgi.exteriorCellSet cell.1) GH ≤
      CoarseDeGiorgi.sampledUpperResponse a ha j τ * R := by
  have hpoint : ∀ cell : CoarseDeGiorgi.whitneySimplicesNearSize (d := d) τ h j,
      weightedEnergy a (CoarseDeGiorgi.exteriorCellSet cell.1) GH ≤
        CoarseDeGiorgi.sampledUpperResponse a ha j τ *
          ∫⁻ x in CoarseDeGiorgi.exteriorCellSet cell.1,
            ENNReal.ofReal (vecNormSq (CoarseDeGiorgi.smoothGrad
              (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x)) := by
    intro cell
    obtain ⟨η, heq, hx⟩ := eq66_statement hd hτ0 hτ1 hρ₂ hτρ hh hwidth ha hHGH j cell.1 cell.2
    have hne : (CoarseDeGiorgi.exteriorCellSet cell.1).Nonempty := by
      rw [cellSet_eq_whitney]
      exact Whitney.source_cell_nonempty (whitneyCell cell.1)
    obtain ⟨x0, hx0⟩ := hne
    obtain ⟨e, c, hL, hG, -⟩ := near_cell_data hd hτ0 hτ1 hρ₂ hτρ hh hwidth hHGH cell.1 cell.2.1
    have hconst : ∫⁻ x in CoarseDeGiorgi.exteriorCellSet cell.1,
        ENNReal.ofReal (vecNormSq (CoarseDeGiorgi.smoothGrad
          (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x)) =
        ENNReal.ofReal (vecNormSq (CoarseDeGiorgi.smoothGrad
          (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x0)) *
          volume (CoarseDeGiorgi.exteriorCellSet cell.1) := by
      have : ∫⁻ x in CoarseDeGiorgi.exteriorCellSet cell.1,
          ENNReal.ofReal (vecNormSq (CoarseDeGiorgi.smoothGrad
            (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x)) =
          ∫⁻ x in CoarseDeGiorgi.exteriorCellSet cell.1,
            ENNReal.ofReal (vecNormSq (CoarseDeGiorgi.smoothGrad
              (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x0)) := by
        apply setLIntegral_congr_fun
        · rw [cellSet_eq_whitney]
          exact (Whitney.source_cell_domain (whitneyCell cell.1)).isOpen.measurableSet
        · intro x hx
          show ENNReal.ofReal _ = ENNReal.ofReal _
          rw [hG x hx, hG x0 hx0]
      rw [this, setLIntegral_const]
    obtain ⟨h1, h2⟩ := hx x0 hx0
    rw [hconst]
    calc _ ≤ _ := h1.le.trans h2
      _ = _ := by ring
  calc ∑' cell : CoarseDeGiorgi.whitneySimplicesNearSize (d := d) τ h j,
        weightedEnergy a (CoarseDeGiorgi.exteriorCellSet cell.1) GH
      ≤ ∑' cell : CoarseDeGiorgi.whitneySimplicesNearSize (d := d) τ h j,
        CoarseDeGiorgi.sampledUpperResponse a ha j τ *
          ∫⁻ x in CoarseDeGiorgi.exteriorCellSet cell.1,
            ENNReal.ofReal (vecNormSq (CoarseDeGiorgi.smoothGrad
              (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x)) :=
        ENNReal.tsum_le_tsum hpoint
    _ = CoarseDeGiorgi.sampledUpperResponse a ha j τ * ∑' cell :
        CoarseDeGiorgi.whitneySimplicesNearSize (d := d) τ h j,
        ∫⁻ x in CoarseDeGiorgi.exteriorCellSet cell.1,
          ENNReal.ofReal (vecNormSq (CoarseDeGiorgi.smoothGrad
            (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x)) := ENNReal.tsum_mul_left
    _ ≤ _ := by gcongr

end CoarseDeGiorgi.Whitney.Harmonic.Wide
