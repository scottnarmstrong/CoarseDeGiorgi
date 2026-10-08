import CoarseDeGiorgi.Statements.SobolevNorm
import Homogenization.Ambient.CoefficientField
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- The negative Sobolev norm `e.negative.sobolev.norm`: for an open `U`, `β ≥ 0`, `1 < p < ∞`, `p' = p / (p - 1)`, and
a matrix field `b` with `|b| ∈ L¹(U)` (entrywise integrability on `U`, as in `besovCubeNorm`),
`‖b‖_{W^{-β,p}(U)} = sup {|∫_U g b| : g ∈ L^∞(U), ‖g‖_{W^{β,p'}(U)} ≤ 1}`,
the dual norm tested on bounded functions. `∫_U g b` is the entrywise integral and `|·|` is
the ℓ²→ℓ² operator norm. The order of the space is `-β`. The value lies in `[0, ∞]`; the
case `p = ∞` (`p' = 1`) is not formalized. -/
noncomputable def negSobolevNorm {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (b : Vec d → Mat d)
    (_hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U))
    (β p : ℝ) (hβ : 0 ≤ β) (hp : 1 < p) : ℝ≥0∞ :=
  ⨆ (g : Vec d → ℝ) (_ : MemLp g ⊤ (volume.restrict U))
    (_ : sobolevNorm U hU β (p / (p - 1)) hβ
      ((le_div_iff₀ (sub_pos.mpr hp)).mpr (by linarith)) g ≤ 1),
    ENNReal.ofReal ‖Matrix.of fun i j => ∫ x in U, g x * b x i j ∂volume‖

end CoarseDeGiorgi
