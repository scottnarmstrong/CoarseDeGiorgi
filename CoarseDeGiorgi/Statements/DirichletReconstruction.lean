module

public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.MemH1a0
public import CoarseDeGiorgi.Statements.LowerCellAverage
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.RStarParam
public import CoarseDeGiorgi.Statements.WeightedEnergy

public import CoarseDeGiorgi.Endpoint.Reconstruction.Main

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Lemma `l.dirichlet.reconstruction`: scale decomposition of `v ∈ H¹_{a,0}(□₀)`,
with the bounds `e.dirichlet.blocks`; `b_k = 3^{-kt} (avg_{𝒯_k} |a_*⁻¹|^q)^{1/(2q)}`. -/
theorem dirichlet_reconstruction (d : ℕ) (_hd : 3 ≤ d) (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p s t : ℝ) (hp : 1 < p) (hs : 0 < s) (ht : 0 < t),
        0 < paramTheta d p q s t →
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
          MemH1a0 a (originCube 1) v G →
          ∃ vk : ℕ → Vec d → ℝ,
            Filter.Tendsto
              (fun N : ℕ => eLpNorm (fun x => v x - ∑ k ∈ Finset.Icc 1 N, vk k x)
                (ENNReal.ofReal (paramR q)) (volume.restrict (originCube 1)))
              Filter.atTop (nhds 0) ∧
            ∀ k : ℕ, 1 ≤ k →
              AEStronglyMeasurable (vk k) (volume.restrict (originCube 1)) ∧
              eLpNorm (vk k) (ENNReal.ofReal (paramR q)) (volume.restrict (originCube 1)) ≤
                ENNReal.ofReal C * ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * (1 - t)))) *
                  (ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
                    (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q))) *
                  (weightedEnergy a (originCube 1) G).rpow (1 / 2) ∧
              eLpNorm (vk k) ⊤ (volume.restrict (originCube 1)) ≤
                ENNReal.ofReal C *
                  ENNReal.ofReal (Real.rpow 3 ((d : ℝ) / rStarParam (d := d) q t * (k : ℝ))) *
                  (ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
                    (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q))) *
                  (weightedEnergy a (originCube 1) G).rpow (1 / 2)
:=
  Endpoint.Reconstruction.dirichlet_reconstruction_proof d _hd q hq

end CoarseDeGiorgi
