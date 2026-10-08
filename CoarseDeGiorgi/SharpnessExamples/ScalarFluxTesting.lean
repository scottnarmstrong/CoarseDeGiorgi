import CoarseDeGiorgi.SharpnessExamples.ScalarFluxAxial
import CoarseDeGiorgi.SharpnessExamples.ScalarFluxSign

/-! # The weak subsolution inequality for the cutoff cylinder flux -/

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- Coordinate integration by parts and nonnegative divergence give the
subsolution sign for every outer-cutoff flux. -/
theorem scalarCutoffFlux_test_nonpos {m : ℕ} (hm : 2 ≤ m)
    {n : ℕ} {ζ δ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hδ0 : 0 < δ)
    (hδε : δ < cylinderRadius (m + 1) n ζ (cylinderRadialConstant (m + 1)))
    {φ : Vec (m + 1) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ originCube 1) (hn : ∀ x, 0 ≤ φ x) :
    Integrable (fun x => vecDot (smoothGrad φ x) (scalarCutoffFlux n ζ δ x)) volume ∧
    (∫ x, vecDot (smoothGrad φ x) (scalarCutoffFlux n ζ δ x) ∂volume) ≤ 0 := by
  classical
  let F := scalarCutoffFlux (d := m + 1) n ζ δ
  let L := fun i (x : Vec (m + 1)) => fderiv ℝ φ x (basisVec i) * F x i
  let R := fun i (x : Vec (m + 1)) => φ x * lineDeriv ℝ (fun y => F y i) x (basisVec i)
  have hi : ∀ i : Fin (m + 1), Integrable (L i) volume ∧ Integrable (R i) volume ∧
      (∫ x, L i x ∂volume) = -(∫ x, R i x ∂volume) := by
    intro i
    by_cases hi0 : i = 0
    · subst i
      exact integral_test_mul_scalarCutoffFlux_axial (by omega) hζ0 hζ2 δ hφ hc
    · obtain ⟨K, hK⟩ := scalarCutoffFlux_transverse_exists_lipschitzOn (by omega) n ζ δ hi0
      exact integral_test_mul_lipschitzOn_flux (Whitney.source_cube_domain
        (d := m + 1) (by norm_num : (0 : ℝ) < 1)).isOpen hφ hc hs hK (basisVec i)
  have hiL : Integrable (fun x => ∑ i : Fin (m + 1), L i x) volume := by
    have h := integrable_finsetSum Finset.univ (fun i _ => (hi i).1)
    simpa only [Finset.sum_fn] using h
  have heq : (fun x => vecDot (smoothGrad φ x) (F x)) = fun x => ∑ i : Fin (m + 1), L i x := rfl
  have hIBP : (∫ x, ∑ i : Fin (m + 1), L i x ∂volume) =
      -(∫ x, ∑ i : Fin (m + 1), R i x ∂volume) := by
    rw [integral_finsetSum _ (fun i _ => (hi i).1), integral_finsetSum _ (fun i _ => (hi i).2.1)]
    simp_rw [(hi _).2.2]
    simp only [Finset.sum_neg_distrib]
  have hnonneg : 0 ≤ ∫ x, ∑ i : Fin (m + 1), R i x ∂volume := by
    apply integral_nonneg_of_ae
    filter_upwards [scalarCutoffFlux_divergence_nonneg_ae hm hζ0 hζ2 hδ0 hδε] with x hx
    change 0 ≤ ∑ i : Fin (m + 1), φ x * lineDeriv ℝ (fun y => F y i) x (basisVec i)
    rw [← Finset.mul_sum]
    exact mul_nonneg (hn x) hx
  refine ⟨?_, ?_⟩
  · rwa [← heq] at hiL
  · rw [heq, hIBP]
    exact neg_nonpos.mpr hnonneg

end

end CoarseDeGiorgi.SharpnessExamples
