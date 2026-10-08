import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.Csol
import CoarseDeGiorgi.Statements.NonnegativeEssInf
import CoarseDeGiorgi.Statements.BesovCubeNorm

import CoarseDeGiorgi.SharpnessExamples.BesovSharpness
open Homogenization MeasureTheory Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem sharpness (d : ℕ) (_hd : 3 ≤ d) (ξ ζ α β : ℝ)
    (hξ : 1 < ξ) (hζ : 1 < ζ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (θ₀ : ℝ) (_hθ₀def : θ₀ = 1 - (α + β) / 2 - ((d : ℝ) - 1) / 2 * (1 / ξ + 1 / ζ))
    (_hθ₀ : θ₀ ≤ 0) :
    ∃ a : Vec d → ℝ,
      Measurable[borel (Vec d)] a ∧ (∀ x, 0 < a x) ∧
      (∀ x x' : Vec d, (∀ i : Fin d, (i : ℕ) ≠ 0 → x i = x' i) → a x = a x') ∧
      ∃ (_ha : IsWeightedCoeffOn (originCube 1) (fun x => a x • (1 : Mat d)))
        (hA : ∀ i j, Integrable (fun x => (a x • (1 : Mat d)) i j)
          (volume.restrict (originCube 1)))
        (hAinv : ∀ i j, Integrable (fun x => (a x • (1 : Mat d))⁻¹ i j)
          (volume.restrict (originCube 1))),
        (∀ hα' : 0 < α,
          besovCubeNorm (fun x => a x • (1 : Mat d)) hA (α / 2) ξ (half_pos hα') hξ.le < ⊤) ∧
        (α = 0 →
          eLpNorm (fun x => ‖a x • (1 : Mat d)‖) (ENNReal.ofReal ξ)
            (volume.restrict (originCube 1)) < ⊤) ∧
        (∀ hβ' : 0 < β,
          besovCubeNorm (fun x => (a x • (1 : Mat d))⁻¹) hAinv (β / 2) ζ (half_pos hβ')
            hζ.le < ⊤) ∧
        (β = 0 →
          eLpNorm (fun x => ‖(a x • (1 : Mat d))⁻¹‖) (ENNReal.ofReal ζ)
            (volume.restrict (originCube 1)) < ⊤) ∧
        ∃ u : Vec d → ℝ,
          u ∈ Csol (fun x => a x • (1 : Mat d)) (originCube 1) ∧
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 1 ≤ u x) ∧
          eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) = ⊤ ∧
          0 < nonnegativeEssInf (originCube (1 / 2)) u ∧
          nonnegativeEssInf (originCube (1 / 2)) u < ⊤ ∧
          ∀ x : Vec d, |x ⟨0, by omega⟩| < 1 / 2 → (∀ i : Fin d, (i : ℕ) ≠ 0 → x i = 0) →
            ∀ N ∈ 𝓝 x, eLpNorm u ⊤ (volume.restrict (N ∩ originCube 1)) = ⊤
:=
  by
  obtain ⟨a, ha, hrest⟩ := CoarseDeGiorgi.SharpnessExamples.sharpness_besov_proved d _hd ξ ζ α β hξ hζ hα
    hβ θ₀ _hθ₀def _hθ₀
  refine ⟨a, ?_, hrest⟩
  rw [← BorelSpace.measurable_eq]
  exact ha

end CoarseDeGiorgi
