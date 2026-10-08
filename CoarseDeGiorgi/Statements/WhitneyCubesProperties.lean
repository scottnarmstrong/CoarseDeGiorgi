module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Multiscale.CubeAverage
public import CoarseDeGiorgi.Foundations.Triadic.WhitneyCubesProof

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

theorem whitney_cubes {d : ℕ} {τ : ℝ}
    (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) :
    (∀ D : TriadicCube d, D ∈ whitneyCubes (d := d) τ →
      ∀ E : TriadicCube d, E ∈ whitneyCubes (d := d) τ → D ≠ E →
      Disjoint (openCubeSet D) (openCubeSet E)) ∧
    (∀ x : Vec d, x ∉ closedReferenceCube (d := d) τ →
      ∃ D : TriadicCube d, D ∈ whitneyCubes (d := d) τ ∧
        x ∈ closedTriadicCube (d := d) D) ∧
    (∀ K : Set (Vec d), IsCompact K → K ⊆ (closedReferenceCube τ)ᶜ →
      {D : TriadicCube d | D ∈ whitneyCubes τ ∧
        (closedTriadicCube (d := d) D ∩ K).Nonempty}.Finite) ∧
    (∀ D : TriadicCube d, D ∈ whitneyCubes (d := d) τ →
      ∀ x : Vec d, x ∈ closedTriadicCube (d := d) D →
        2 * cubeScaleFactor D <
            infSupDist (d := d) (closedTriadicCube (d := d) D)
              (closedReferenceCube (d := d) τ) ∧
          infSupDist (d := d) (closedTriadicCube (d := d) D)
              (closedReferenceCube (d := d) τ) ≤
            pointSupDist (d := d) x (closedReferenceCube (d := d) τ) ∧
          pointSupDist (d := d) x (closedReferenceCube (d := d) τ) ≤
            9 * cubeScaleFactor D) :=
  CoarseDeGiorgi.Foundations.Triadic.whitney_cubes_proved hτ0 hτ1

end CoarseDeGiorgi
