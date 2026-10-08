module

public import CoarseDeGiorgi.Whitney.Harmonic.LevelWide
public import CoarseDeGiorgi.Whitney.Harmonic.Eq66
public import CoarseDeGiorgi.Whitney.Harmonic.Sampling
public import CoarseDeGiorgi.Whitney.Harmonic.Cellwise2Wide
public import CoarseDeGiorgi.Statements.UpperResponseOnCell
public import CoarseDeGiorgi.Statements.UpperResponseSpec
public import CoarseDeGiorgi.Weighted.LowerSpecNorm
public import CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
public import CoarseDeGiorgi.Statements.SimplexCellNonempty
public import CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell

/-! The energy identity `e.harmonic.energy` on a Whitney simplex. -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Matrix.Norms.L2Operator
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

theorem eq66_statement [NeZero d] (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    {a : CoeffField d} (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {f : Vec d → ℝ} {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH)
    (j : ℕ) (cell : CoarseDeGiorgi.ExteriorCell d τ)
    (hcell : cell ∈ CoarseDeGiorgi.whitneySimplicesNearSize τ h j) :
    ∃ η : CoarseDeGiorgi.SimplexIndex d j,
      CoarseDeGiorgi.exteriorCellSet cell = CoarseDeGiorgi.simplexCell j η ∧
        ∀ x ∈ CoarseDeGiorgi.exteriorCellSet cell,
          weightedEnergy a (CoarseDeGiorgi.exteriorCellSet cell) GH =
              volume (CoarseDeGiorgi.exteriorCellSet cell) *
                ENNReal.ofReal
                  (vecDot (CoarseDeGiorgi.smoothGrad
                      (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x)
                    (matVecMul (CoarseDeGiorgi.upperResponseOnCell j a ha η)
                      (CoarseDeGiorgi.smoothGrad
                        (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x))) ∧
            volume (CoarseDeGiorgi.exteriorCellSet cell) *
                ENNReal.ofReal
                  (vecDot (CoarseDeGiorgi.smoothGrad
                      (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x)
                    (matVecMul (CoarseDeGiorgi.upperResponseOnCell j a ha η)
                      (CoarseDeGiorgi.smoothGrad
                        (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x))) ≤
              CoarseDeGiorgi.sampledUpperResponse a ha j τ *
                (volume (CoarseDeGiorgi.exteriorCellSet cell) *
                  ENNReal.ofReal (vecNormSq
                    (CoarseDeGiorgi.smoothGrad
                      (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x))) := by
  have hτpos : 0 < τ := by linarith
  obtain ⟨η, heq⟩ := cell_eq_simplexCell hτ0 hτ1 hρ₂ hτρ hwidth (by omega) j cell hcell
  refine ⟨η, heq, fun x hx => ?_⟩
  obtain ⟨e, c, hL, hG, hUV, hsol, h0⟩ :=
    near_cell_data hd hτ0 hτ1 hρ₂ hτρ hh hwidth hHGH cell hcell.1
  have hV : IsOpenBoundedConvexDomain (CoarseDeGiorgi.exteriorCellSet cell) := by
    rw [cellSet_eq_whitney]
    exact Whitney.source_cell_domain (whitneyCell cell)
  have hne : (CoarseDeGiorgi.exteriorCellSet cell).Nonempty := ⟨x, hx⟩
  have haV := Whitney.lift_coeff_mono ha hUV
  have hid := cell_identification hV hne haV e c hL hsol h0
  have hg : CoarseDeGiorgi.smoothGrad (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x = e :=
    hG x hx
  rw [hg]
  have hηV := CoarseDeGiorgi.simplexCell_isOpenBoundedConvexDomain j η
  have hηne := CoarseDeGiorgi.simplexCell_nonempty j η
  have hηa := CoarseDeGiorgi.weightedCoeffOn_simplexCell j a ha η
  have hA : CoarseDeGiorgi.upperResponseOnCell j a ha η =
      CoarseDeGiorgi.upperResponse a (CoarseDeGiorgi.exteriorCellSet cell) hV hne haV := by
    unfold CoarseDeGiorgi.upperResponseOnCell
    exact (upperResponse_congr heq hV hne haV hηV hηne hηa).symm
  have hresp := (CoarseDeGiorgi.upperResponse_spec hV hne haV).2.2.1 e
  have hr : (upperDirectionalResponseSol a (CoarseDeGiorgi.exteriorCellSet cell) e).toReal =
      vecDot e (matVecMul (CoarseDeGiorgi.upperResponseOnCell j a ha η) e) := by
    rw [hA, ← EReal.toReal_coe (vecDot e (matVecMul _ e)), hresp]
  have henergy : weightedEnergy a (CoarseDeGiorgi.exteriorCellSet cell) GH =
      volume (CoarseDeGiorgi.exteriorCellSet cell) *
        ENNReal.ofReal (vecDot e (matVecMul (CoarseDeGiorgi.upperResponseOnCell j a ha η) e)) := by
    have h1 : weightedEnergy a (CoarseDeGiorgi.exteriorCellSet cell) GH =
        weightedEnergy a (CoarseDeGiorgi.exteriorCellSet cell)
          (Whitney.liftCellPair hV hne haV e).2 := Weighted.energy_congr_ae hid.2
    rw [h1, Whitney.liftCellPair_energy hV hne haV e, hr]
  refine ⟨henergy, ?_⟩
  -- sampled response bound
  have hsamp : ENNReal.ofReal ‖CoarseDeGiorgi.upperResponseOnCell j a ha η‖ ≤
      CoarseDeGiorgi.sampledUpperResponse a ha j τ := by
    unfold CoarseDeGiorgi.sampledUpperResponse
    refine le_iSup_of_le η (le_iSup_of_le ?_ le_rfl)
    rw [← heq]
    exact euclideanSetDistance_cell_le hτ0 hτ1 (by omega) j cell hcell.2
  have hq := Weighted.LowerResponseImpl.lower_quadratic_le_norm
    (CoarseDeGiorgi.upperResponseOnCell j a ha η) e
  calc volume (CoarseDeGiorgi.exteriorCellSet cell) *
        ENNReal.ofReal (vecDot e (matVecMul (CoarseDeGiorgi.upperResponseOnCell j a ha η) e))
      ≤ volume (CoarseDeGiorgi.exteriorCellSet cell) *
        (ENNReal.ofReal ‖CoarseDeGiorgi.upperResponseOnCell j a ha η‖ *
          ENNReal.ofReal (vecNormSq e)) := by
        gcongr
        rw [← ENNReal.ofReal_mul (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hq
    _ ≤ volume (CoarseDeGiorgi.exteriorCellSet cell) *
        (CoarseDeGiorgi.sampledUpperResponse a ha j τ * ENNReal.ofReal (vecNormSq e)) := by
        gcongr
    _ = _ := by ring

end CoarseDeGiorgi.Whitney.Harmonic.Wide
