import CoarseDeGiorgi.Endpoint.Chaining.Geometry
import CoarseDeGiorgi.Endpoint.Source.Geometry
import CoarseDeGiorgi.LowerFractional.Restriction

/-! Restriction of solutions and supersolutions to the grid cubes. -/
namespace CoarseDeGiorgi.Endpoint
open Homogenization MeasureTheory

theorem gridCube_domain {d : ℕ} (y : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    IsOpenBoundedConvexDomain (gridCube d y ρ) := by
  have hset : gridCube d y ρ = Metric.ball y (ρ / 54) := by
    ext x
    rw [mem_gridCube_iff, Metric.mem_ball, dist_eq_norm]
    simp only [pi_norm_lt_iff (by positivity : 0 < ρ / 54), Pi.sub_apply, Real.norm_eq_abs]
  rw [hset]
  exact isOpenBoundedConvexDomain_ball y (by positivity)

theorem chaining_test_integral {d : ℕ} {V U : Set (Vec d)} {a : CoeffField d}
    (hV : MeasurableSet V) (hUV : U ⊆ V) {φ : Vec d → ℝ}
    (hs : tsupport φ ⊆ U) (G : Vec d → Vec d) :
    (∫ x in V, vecDot (smoothGrad φ x) (matVecMul (a x) (G x))) =
      ∫ x in U, vecDot (smoothGrad φ x) (matVecMul (a x) (G x)) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hV hUV
  intro x hx
  have hφ : smoothGrad φ x = 0 := by
    funext i
    simp only [smoothGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hx.2 (hs h)),
      zero_apply, Pi.zero_apply]
  rw [hφ]
  simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

theorem weighted_solution_restrict {d : ℕ} [NeZero d] {a : CoeffField d}
    {V U : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (hU : IsOpenBoundedConvexDomain U) (hUV : U ⊆ V)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : IsWeightedSolution a V u G) :
    IsWeightedSolution a U u G := by
  refine ⟨LowerFractional.memH1a_restrict hV hne ha hU hUV hu.1, ?_⟩
  intro φ hφ hc hs
  have ht := hu.2 φ hφ hc (hs.trans hUV)
  exact ⟨ht.1.mono_set hUV, (chaining_test_integral hV.isOpen.measurableSet hUV hs G) ▸ ht.2⟩

theorem weighted_supersolution_restrict {d : ℕ} [NeZero d] {a : CoeffField d}
    {V U : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (hU : IsOpenBoundedConvexDomain U) (hUV : U ⊆ V)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : IsWeightedSupersolution a V u G) :
    IsWeightedSupersolution a U u G := by
  refine ⟨LowerFractional.memH1a_restrict hV hne ha hU hUV hu.1, ?_⟩
  intro φ hφ hc hs hφ0
  have ht := hu.2 φ hφ hc (hs.trans hUV) hφ0
  exact ⟨ht.1.mono_set hUV,
    (chaining_test_integral hV.isOpen.measurableSet hUV hs (fun x => -G x)) ▸ ht.2⟩

end CoarseDeGiorgi.Endpoint
