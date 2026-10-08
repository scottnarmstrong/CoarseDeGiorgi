import CoarseDeGiorgi.Endpoint.Rescaling.AffineEnergy
import CoarseDeGiorgi.Weighted.TestingApproximation

/-! Transport of the weighted completions by interior affine maps. -/

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal Pointwise

namespace CoarseDeGiorgi.Endpoint.Rescaling

private theorem affine_value_limit {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} {f : ℕ → Vec d → ℝ} {u : Vec d → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (affineImage y r U)))
    (hu : AEStronglyMeasurable u (volume.restrict (affineImage y r U)))
    (hL : Tendsto (fun n => eLpNorm (f n - u) 1
      (volume.restrict (affineImage y r U))) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n ∘ affineMap y r - u ∘ affineMap y r) 1
      (volume.restrict U)) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((r ^ d)⁻¹)) hL
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at h
  convert h using 1
  funext n
  have he : f n ∘ affineMap y r - u ∘ affineMap y r = (f n - u) ∘ affineMap y r := rfl
  rw [he]
  exact eLpNorm_one_affine y hr ((hf n).sub hu)

private theorem affine_energy_limit {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpen U) {a : CoeffField d}
    {f : ℕ → Vec d → ℝ} {G : Vec d → Vec d}
    (hf : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) (affineImage y r U))
    (hE : Tendsto (fun n => weightedEnergy a (affineImage y r U)
      (smoothGrad (f n) - G)) atTop (𝓝 0)) :
    Tendsto (fun n => weightedEnergy (a ∘ affineMap y r) U
      (smoothGrad (f n ∘ affineMap y r) - r • (G ∘ affineMap y r))) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (r ^ 2))
    (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ((r ^ d)⁻¹)) hE
      (Or.inr ENNReal.ofReal_ne_top))
    (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at h
  convert h using 1
  funext n
  have hg : smoothGrad (f n ∘ affineMap y r) - r • (G ∘ affineMap y r) =ᵐ[volume.restrict U]
      r • ((smoothGrad (f n) - G) ∘ affineMap y r) := by
    filter_upwards [smoothGrad_affine_ae y hr hU (hf n)] with x hx
    change smoothGrad (f n ∘ affineMap y r) x - r • G (affineMap y r x) = _
    rw [hx]
    exact (smul_sub r (smoothGrad (f n) (affineMap y r x)) (G (affineMap y r x))).symm
  have he : weightedEnergy (a ∘ affineMap y r) U
      (smoothGrad (f n ∘ affineMap y r) - r • (G ∘ affineMap y r)) =
      weightedEnergy (a ∘ affineMap y r) U
        (r • ((smoothGrad (f n) - G) ∘ affineMap y r)) :=
    Weighted.energy_congr_ae hg
  rw [he, weightedEnergy_const_smul, weightedEnergy_affine y hr]

/-- A weighted pair pulls back with its gradient multiplied by the affine scale. -/
theorem memH1a_affine {d : ℕ} [NeZero d] (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hV : IsOpenBoundedConvexDomain (affineImage y r U))
    (hne : (affineImage y r U).Nonempty) {a : CoeffField d}
    (ha : IsWeightedCoeffOn (affineImage y r U) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a (affineImage y r U) u G) :
    MemH1a (a ∘ affineMap y r) U (u ∘ affineMap y r) (r • (G ∘ affineMap y r)) := by
  obtain ⟨huM, hGM, f, hf, hc, hloc, hE⟩ := hu
  obtain ⟨hui, hL⟩ := Weighted.core_tendsto_l1 hV hne ha hf hc huM hloc
  exact Weighted.memH1a_of_core_tendsto hU (weightedCoeffOn_affine y hr ha)
    (fun n => isSmoothCore_affine y hr hU.isOpen (hf n))
    (integrable_affine y hr hui)
    ((aestronglyMeasurable_affine y hr hGM).const_smul r)
    (affine_value_limit y hr (fun n => (hf n).2.1.1) huM hL)
    (affine_energy_limit y hr hU.isOpen (fun n => (hf n).1) hE)

end CoarseDeGiorgi.Endpoint.Rescaling
