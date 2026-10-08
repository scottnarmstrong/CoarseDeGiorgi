module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.CoarseGraining.Definitions
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.CubeCell
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Statements.Triangulation
public import CoarseDeGiorgi.Statements.GaussianKernel

public import CoarseDeGiorgi.NegSobolev.BesovAverages

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.besov.averages`, finite `1 ≤ p < ∞`: there is
`C = C(d) > 0` such that for every `1 ≤ p < ∞`, every matrix field `b` on `□₀`, symmetric and
positive semidefinite a.e. with `|b| ∈ L¹(□₀)`, and every `k ≥ 0`, for both families `𝒫_k`
(the simplices of `𝒯_k`, and the cubes `z + □_{-k}`, `z ∈ 3^{-k}ℤ^d ∩ □₀`),
`C⁻¹ (avsum_{Q ∈ 𝒫_k} |(b)_Q|^p)^{1/p} ≤ ‖G_{3^{-2k}} * b̃‖_{L^p(ℝ^d)} ≤ C (avsum …)^{1/p}`
(e.besov.heat), and consequently, for every `s > 0`, each of the sums
`∑_k 3^{-ks} (avsum_{Q ∈ 𝒫_k} |(b)_Q|^p)^{1/(2p)}` and `∑_k 3^{-ks} ‖G_{3^{-2k}} * b̃‖_{L^p}^{1/2}`
is at most `C^{1/2}` times the other (e.besov.averages). Here `b̃` is the extension of `b` by
zero (`(originCube 1).indicator b`), `G_t * b̃` is the entrywise convolution
`x ↦ ∫ G_t(x - y) b̃(y) dy`, `|·|` is the operator norm (the `L^p` norm of a matrix field is that
of its operator norm), and the means are the arithmetic means over the `3^{kd} d!`
simplices (normalized as in `upperCellAverage`) and over the `3^{kd}` cubes (as in
`besovCubeNorm`, whose cube sum squared is the first sum for the cubes). The case `p = ∞`
(maxima) is not formalized. -/
theorem besov_averages (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℝ), 1 ≤ p →
      ∀ (b : Vec d → Mat d),
        (∀ᵐ x ∂(volume.restrict (originCube 1)), (b x).PosSemidef) →
        (∀ i j, Integrable (fun x => b x i j) (volume.restrict (originCube 1))) →
        let heat : ℕ → ℝ≥0∞ := fun k =>
          eLpNorm
            (fun x => ‖Matrix.of fun i j =>
              ∫ y, gaussianKernel ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (zpow_pos (by norm_num) _) (x - y) *
                (originCube 1).indicator b y i j ∂volume‖)
            (ENNReal.ofReal p) volume
        let simplexMean : ℕ → ℝ := fun k =>
          ((triangulation (d := d) k).attach.sum fun η =>
              Real.rpow ‖volumeAverageMat (simplexCell k η) b‖ p) /
            ((triangulation (d := d) k).card : ℝ)
        let cubeMean : ℕ → ℝ := fun k =>
          (∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖volumeAverageMat (cubeCell k j) b‖ p) /
            ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)
        (∀ k : ℕ,
          ENNReal.ofReal C⁻¹ * (ENNReal.ofReal (simplexMean k)).rpow (1 / p) ≤ heat k ∧
            heat k ≤ ENNReal.ofReal C * (ENNReal.ofReal (simplexMean k)).rpow (1 / p)) ∧
        (∀ k : ℕ,
          ENNReal.ofReal C⁻¹ * (ENNReal.ofReal (cubeMean k)).rpow (1 / p) ≤ heat k ∧
            heat k ≤ ENNReal.ofReal C * (ENNReal.ofReal (cubeMean k)).rpow (1 / p)) ∧
        ∀ s : ℝ, 0 < s →
          let heatSum := ∑' k : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * (heat k).rpow (1 / 2)
          let simplexSum := ∑' k : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
              (ENNReal.ofReal (simplexMean k)).rpow (1 / (2 * p))
          let cubeSum := ∑' k : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
              (ENNReal.ofReal (cubeMean k)).rpow (1 / (2 * p))
          (simplexSum ≤ ENNReal.ofReal (Real.sqrt C) * heatSum ∧
            heatSum ≤ ENNReal.ofReal (Real.sqrt C) * simplexSum) ∧
          (cubeSum ≤ ENNReal.ofReal (Real.sqrt C) * heatSum ∧
            heatSum ≤ ENNReal.ofReal (Real.sqrt C) * cubeSum)
:=
  by exact CoarseDeGiorgi.NegSobolev.besov_averages_proved d

end CoarseDeGiorgi
