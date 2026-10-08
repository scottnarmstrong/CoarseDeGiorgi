module

public import CoarseDeGiorgi.Statements.IsWhitneyInterpolant
public import CoarseDeGiorgi.Statements.EuclidNorm

public import CoarseDeGiorgi.Whitney.Interpolation.UniquenessMain
public import CoarseDeGiorgi.Whitney.Interpolation.BoundsGrad

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Lemma `l.whitney.interpolation`: every continuous function on the exterior of `τ□̄₀` that is affine on
each Whitney simplex and takes the values `vals` at the free vertices agrees there with the interpolant `g`; on the
closure of every Whitney cube `D`, `g` lies between values at free vertices of `D̄`, and on each simplex of `D` the
Euclidean norm of its gradient is at most `C(d) ℓ(D)^{-1}` times any bound `M` for the differences of its values at
the free vertices of `D̄` (this is the `L^∞(D)` bound of the paper, `g` being affine on each simplex). -/
theorem whitney_interpolation {d : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (τ : ℝ), (1 / 2 : ℝ) ≤ τ → τ < 1 →
        ∀ (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) (g : Vec d → ℝ),
          IsWhitneyInterpolant τ vals g →
          (∀ g' : Vec d → ℝ, ContinuousOn g' (closedReferenceCube (d := d) τ)ᶜ →
            (∀ cell : ExteriorCell d τ, ∃ (e : Vec d) (c : ℝ),
              ∀ x ∈ exteriorCellSet cell, g' x = vecDot e x + c) →
            (∀ z : {z : Vec d // IsFreeVertex τ z}, g' z.1 = vals z) →
            Set.EqOn g' g (closedReferenceCube (d := d) τ)ᶜ) ∧
          ∀ D : TriadicCube d, D ∈ whitneyCubes (d := d) τ →
            (∀ x ∈ closedTriadicCube D,
              ∃ z z' : {z : Vec d // IsFreeVertex τ z},
                z.1 ∈ closedTriadicCube D ∧ z'.1 ∈ closedTriadicCube D ∧
                vals z ≤ g x ∧ g x ≤ vals z') ∧
            (∀ M : ℝ,
              (∀ z z' : {z : Vec d // IsFreeVertex τ z},
                z.1 ∈ closedTriadicCube D → z'.1 ∈ closedTriadicCube D →
                |g z.1 - g z'.1| ≤ M) →
              ∀ cell : ExteriorCell d τ, cell.1.val = D →
                ∀ x ∈ exteriorCellSet cell,
                  euclidNorm (smoothGrad g x) ≤ C / cubeScaleFactor D * M)
:=
  by
  refine ⟨3 * (d : ℝ), by positivity, ?_⟩
  intro τ hτ0 hτ1 vals g hg
  refine ⟨fun g' hc ha hv => WhitneyInterp.eqOn_of_interpolant hτ0 hτ1 hg g' hc ha hv, ?_⟩
  intro D hD
  refine ⟨fun x hx => WhitneyInterp.range_bound hτ0 hτ1 hg hD hx, ?_⟩
  intro M hM cell hcell x hx
  exact WhitneyInterp.grad_bound hτ0 hτ1 hg hD hM cell hcell hx

end CoarseDeGiorgi
