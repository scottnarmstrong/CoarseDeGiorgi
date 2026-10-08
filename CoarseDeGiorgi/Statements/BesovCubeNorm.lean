module

public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.GridOffset
public import Homogenization.CoarseGraining.Definitions
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `e.negative.regularity.norm`: the cube quasi-norm `‖b‖_{B̊^{-2s}_{p,1/2}(□₀)}` for `1 ≤ p < ∞`:
`(∑_{k ≥ 0} 3^{-ks} (avsum_{z ∈ 3^{-k}ℤ^d ∩ □₀} |(b)_{z + □_{-k}}|^p)^{1/(2p)})^2`,
with `|·|` the operator norm and `(b)_U` the entrywise volume average. The centres
`z ∈ 3^{-k}ℤ^d ∩ □₀` are `3^{-k} • gridOffset k j`, `j : Fin d → Fin (3^k)` (there are `3^{kd}`
of them), `□_{-k} = 3^{-k}□₀ = originCube (3^{-k})`, and `avsum` is the arithmetic mean over
the `3^{kd}` centres. The value lies in `[0, ∞]`. The case `p = ∞` is not formalized. -/
noncomputable def besovCubeNorm {d : ℕ} (b : Vec d → Mat d)
    (_hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict (originCube 1)))
    (s p : ℝ) (_hs : 0 < s) (_hp : 1 ≤ p) : ℝ≥0∞ := by
  classical
  exact
    (∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal
          ((∑ j : Fin d → Fin (3 ^ k),
              Real.rpow ‖volumeAverageMat
                {x : Vec d | x - (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) ∈
                  originCube ((3 : ℝ) ^ (-(k : ℤ)))} b‖ p) /
            ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ))).rpow (1 / (2 * p))) ^ 2

end CoarseDeGiorgi
