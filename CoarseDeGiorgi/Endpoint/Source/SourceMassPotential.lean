import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.MemH1a0
import CoarseDeGiorgi.Statements.NonnegativeEssInf
import CoarseDeGiorgi.Endpoint.Capacitary.Main
import CoarseDeGiorgi.Endpoint.Rescaling.RemoteBound
import CoarseDeGiorgi.Statements.InteriorWeakHarnack
import CoarseDeGiorgi.Endpoint.Source.Main

/-! The source mass estimate together with the potential of the restricted source measure:
`l.source.mass`, including its final sentence. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Endpoint

theorem source_mass_potential_of_mass (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
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
  by
    let : NeZero d := ⟨by omega⟩
    obtain ⟨C, hC, hmass⟩ := source_mass_of_interior d _hd p q s t hp hq hs ht _hθ
      (CoarseDeGiorgi.interior_weak_harnack d _hd p q s t hp hq hs ht _hθ)
      (remoteLocalBoundedness_holds d _hd p q s t hp hq hs ht _hθ)
    refine ⟨C, hC, ?_⟩
    intro a ha hupper hlower u G hu0 hu
    obtain ⟨μ, hμ0, hμK, hμrep, hμmass⟩ := hmass a ha hupper hlower u G hu0 hu
    obtain ⟨hνfin, _, hνbd, V, Gv, hVmem, hVrep, hV0, hVu, hwsol, _⟩ :=
      source_potential a ha u G hu0 hu μ hμ0 hμK hμrep
        (μ.restrict (originCube (3 / 4))) rfl
    refine ⟨μ, hμ0, hμK, hμrep, hμmass, hνfin, hνbd, V, Gv, hVmem, hVrep, ?_, hwsol⟩
    exact hV0.and hVu

end CoarseDeGiorgi.Endpoint
