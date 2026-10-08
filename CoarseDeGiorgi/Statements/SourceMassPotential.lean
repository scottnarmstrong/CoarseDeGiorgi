module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution
public import CoarseDeGiorgi.Statements.IsWeightedSolution
public import CoarseDeGiorgi.Statements.MemH1a0
public import CoarseDeGiorgi.Statements.NonnegativeEssInf

public import CoarseDeGiorgi.Endpoint.Source.SourceMassPotential

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Lemma `l.source.mass`: the source measure `μ = -∇·a∇u` of a nonnegative supersolution is a
nonnegative Radon measure on `□₀` (finite on compact subsets, carried by `□₀`) with the displayed representation and
the bound `e.source.mass` on `(3/4) □₀`; its restriction `ν` to `(3/4) □₀` is finite and acts continuously on
`H¹_{a,0}(□₀)` (in the form of the hypothesis of Proposition `p.endpoint.potential`), and the potential `V` of `ν` (`V ∈ H¹_{a,0}(□₀)` with `∫ ∇φ·a∇V = ∫ φ dν` for
`φ ∈ C_c^∞(□₀)`) satisfies
`0 ≤ V ≤ u` almost everywhere in `□₀` and `u - V ∈ C_sol((3/4) □₀)`. -/
theorem source_mass_potential (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∃ μ : Measure (Vec d),
            μ (originCube 1)ᶜ = 0 ∧
            (∀ K : Set (Vec d), IsCompact K → K ⊆ originCube 1 → μ K < ⊤) ∧
            (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ originCube 1 →
                ∫ x, φ x ∂μ =
                  ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) ∂volume) ∧
            μ (originCube (3 / 4)) ≤
              ENNReal.ofReal C * upperMoment a ha s p hs hp.le *
                ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
                nonnegativeEssInf (originCube (1 / 2)) u ∧
            IsFiniteMeasure (μ.restrict (originCube (3 / 4))) ∧
            (∃ M : ℝ, 0 ≤ M ∧
              ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ originCube 1 →
                ENNReal.ofReal |∫ x, φ x ∂(μ.restrict (originCube (3 / 4)))| ≤
                  ENNReal.ofReal M *
                    (weightedEnergy a (originCube 1) (smoothGrad φ)).rpow (1 / 2)) ∧
            ∃ (V : Vec d → ℝ) (Gv : Vec d → Vec d),
              MemH1a0 a (originCube 1) V Gv ∧
              (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ originCube 1 →
                ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume =
                  ∫ x, φ x ∂(μ.restrict (originCube (3 / 4)))) ∧
              (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ V x ∧ V x ≤ u x) ∧
              IsWeightedSolution a (originCube (3 / 4)) (fun x => u x - V x)
                (fun x => G x - Gv x)
:=
  by exact CoarseDeGiorgi.Endpoint.source_mass_potential_of_mass d _hd p q s t hp hq hs ht _hθ

end CoarseDeGiorgi
