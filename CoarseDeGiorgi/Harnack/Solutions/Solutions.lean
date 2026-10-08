import CoarseDeGiorgi.Harnack.LEta.LocalEta
import CoarseDeGiorgi.Harnack.Calculus.Supersolution
import CoarseDeGiorgi.LowerFractional.CubeDomain
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.IsWeightedSubsolution
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.NormalizedLpMoment
import CoarseDeGiorgi.Statements.NonnegativeEssInf
import CoarseDeGiorgi.Statements.HarnackEtaParam
import CoarseDeGiorgi.Statements.PositivePart
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.EssSup

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

end CoarseDeGiorgi

namespace CoarseDeGiorgi.Harnack.Solutions

/-- Adding a constant to a weighted solution gives a weighted subsolution. -/
theorem solution_add_const_subsolution {d : ℕ} [NeZero d] {V : Set (Vec d)}
    {a : CoeffField d} (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSolution a V u G) (c : ℝ) :
    IsWeightedSubsolution a V (fun x => u x + c) G := by
  have hs := CoarseDeGiorgi.Harnack.Calculus.IsWeightedSolution.addConst
    hV hne ha hu c
  refine ⟨hs.1, ?_⟩
  intro φ hφ hc hsupp hnonneg
  exact ⟨(hs.2 φ hφ hc hsupp).1, (hs.2 φ hφ hc hsupp).2.le⟩

/-- The exponent `η = r / 4` lies in `(0, 2)`. -/
theorem harnack_eta_parameter_facts {q : ℝ} (hq : 1 < q) :
    0 < paramR q / 4 ∧ paramR q / 4 < 2 := by
  unfold paramR
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  constructor
  · apply div_pos
    · apply div_pos <;> positivity
    · norm_num
  · have hden : 0 < q + 1 := by linarith
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)]
    rw [div_lt_iff₀ hden]
    nlinarith

private lemma originCube_mono {d : ℕ} {ρ R : ℝ} (hρR : ρ ≤ R) :
    originCube (d := d) ρ ⊆ originCube R := by
  intro x hx i
  dsimp [originCube] at hx ⊢
  constructor <;> linarith [hx i]

private lemma originCube_one_eq_auxCube {d : ℕ} :
    originCube (d := d) 1 = auxCube 1 (fun _ : Fin d => 0) := by
  ext x
  simp [originCube, auxCube, sub_self, sub_zero, Int.cast_zero, zero_mul, abs_lt]

private lemma originCube_one_domain {d : ℕ} :
    IsOpenBoundedConvexDomain (originCube (d := d) 1) ∧
      (originCube (d := d) 1).Nonempty := by
  rw [originCube_one_eq_auxCube]
  exact ⟨LowerFractional.auxCube_isOpenBoundedConvexDomain 1 (fun _ => 0),
    LowerFractional.auxCube_nonempty 1 (fun _ => 0)⟩

/-- Corollary B at `η = r / 4` for `u + ε`, with `u` a nonnegative solution: the sup on the
cube of side `1/2` is bounded by the `L^η` norm on the cube of side `5/8`. -/
theorem solution_local_upper_eta0 (d : ℕ) (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ γ : ℝ, 0 < γ ∧
      ∃ Cη : ℝ≥0∞, Cη < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x) →
            IsWeightedSolution a (originCube 1) u G →
            ∀ ε : ℝ, 0 < ε →
              eLpNorm (fun x => u x + ε) ⊤ (volume.restrict (originCube (1 / 2))) ≤
                Cη * (ENNReal.ofReal (1 / 8)).rpow (-2 * γ / (paramR q / 4)) *
                  (1 + contrast a ha s t p q hs ht hp.le hq.le).rpow
                    (((d : ℝ) - 1) / (2 * (paramR q / 4) * paramTheta d p q s t)) *
                  eLpNorm (fun x => u x + ε) (ENNReal.ofReal (paramR q / 4))
                    (volume.restrict (originCube (5 / 8))) ∧
              eLpNorm (fun x => u x + ε) (ENNReal.ofReal (paramR q / 4))
                (volume.restrict (originCube (5 / 8))) < ⊤ := by
  obtain ⟨γ, hγ, _, hBfamily⟩ :=
    CoarseDeGiorgi.Harnack.LEta.cg_local_boundedness_eta_of_local_boundedness d hd p q s t hp hq hs ht hθ
  have hηfacts := harnack_eta_parameter_facts hq
  let η : ℝ := paramR q / 4
  have hη : 0 < η := by simpa [η] using hηfacts.1
  have hη2 : η < 2 := by simpa [η] using hηfacts.2
  obtain ⟨Cη, hCη, hB⟩ := hBfamily η hη hη2
  have hgeom := originCube_one_domain (d := d)
  let : NeZero d := ⟨by omega⟩
  refine ⟨γ, hγ, Cη, hCη, ?_⟩
  intro a ha hupper hlower u G hu_nonneg hu ε hε
  let U : Vec d → ℝ := fun x => u x + ε
  have hsub : IsWeightedSubsolution a (originCube 1) U G := by
    exact solution_add_const_subsolution hgeom.1 hgeom.2 ha hu ε
  have hsubmem : U ∈ Csub a (originCube 1) := ⟨G, hsub⟩
  have hBfunction := hB a ha hupper hlower U hsubmem
  have hBresult := hBfunction.2 (1 / 2) (5 / 8)
    (by norm_num) (by norm_num) (by norm_num)
  have hU_nonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ U x :=
    hu_nonneg.mono (fun _ hx => add_nonneg hx hε.le)
  have hsubset_half : originCube (d := d) (1 / 2) ⊆ originCube 1 :=
    originCube_mono (by norm_num)
  have hsubset_outer : originCube (d := d) (5 / 8) ⊆ originCube 1 :=
    originCube_mono (by norm_num)
  have hUhalf : ∀ᵐ x ∂volume.restrict (originCube (1 / 2)), 0 ≤ U x :=
    ae_restrict_of_ae_restrict_of_subset hsubset_half hU_nonneg
  have hUouter : ∀ᵐ x ∂volume.restrict (originCube (5 / 8)), 0 ≤ U x :=
    ae_restrict_of_ae_restrict_of_subset hsubset_outer hU_nonneg
  have hposHalf : positivePart U =ᵐ[volume.restrict (originCube (1 / 2))] U := by
    filter_upwards [hUhalf] with x hx
    simp [positivePart, max_eq_left hx]
  have hposOuter : positivePart U =ᵐ[volume.restrict (originCube (5 / 8))] U := by
    filter_upwards [hUouter] with x hx
    simp [positivePart, max_eq_left hx]
  have hbound := hBresult.1
  rw [eLpNorm_congr_ae hposHalf, eLpNorm_congr_ae hposOuter] at hbound
  have hfinite := hBresult.2 (by norm_num : (5 / 8 : ℝ) < 1)
  rw [eLpNorm_congr_ae hposOuter] at hfinite
  have hgap : ENNReal.ofReal ((5 / 8 : ℝ) - 1 / 2) = ENNReal.ofReal (1 / 8) := by
    congr 1
    norm_num
  rw [hgap] at hbound
  have hnormbound : eLpNorm U (ENNReal.ofReal η)
      (volume.restrict (originCube (5 / 8))) < ⊤ := by
    simpa [U, η] using hfinite
  constructor
  · simpa [U, η] using hbound
  · simpa [U, η] using hnormbound

end CoarseDeGiorgi.Harnack.Solutions
