import CoarseDeGiorgi.Statements.WhitneyAffineExtensionDef
import CoarseDeGiorgi.Statements.WhitneySimplicesNear
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.MemH1a0

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `(H, GH)` is the piecewise harmonic extension `H_h f` with its gradient: on each
`△ ∈ 𝒲_h`, `H` is the harmonic representative `H_△(L_h f|_△)` (a weak solution in `△` with
`H - L_h f ∈ H¹_{a,0}(△)`, whose gradient is `GH - ∇L_h f`), and on every other Whitney simplex
`H = 0`, `GH = 0` almost everywhere.  The harmonic representative is unique almost everywhere
(Proposition `p.harmonic.replacement`), so this relation determines `(H, GH)` up to null sets on each simplex. -/
noncomputable def IsPiecewiseHarmonicExtension {d : ℕ} (a : CoeffField d) (τ h : ℝ)
    (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (f : Vec d → ℝ)
    (H : Vec d → ℝ) (GH : Vec d → Vec d) : Prop :=
  ∀ cell : ExteriorCell d τ,
    (cell ∈ whitneySimplicesNear τ h →
      IsWeightedSolution a (exteriorCellSet cell) H GH ∧
      MemH1a0 a (exteriorCellSet cell)
        (fun x => H x - whitneyAffineExtension τ h f hτ0 hτ1 x)
        (fun x => GH x - smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)) ∧
    (cell ∉ whitneySimplicesNear τ h →
      ∀ᵐ x ∂(volume.restrict (exteriorCellSet cell)), H x = 0 ∧ GH x = 0)

end CoarseDeGiorgi
