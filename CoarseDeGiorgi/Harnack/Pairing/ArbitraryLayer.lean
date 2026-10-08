import CoarseDeGiorgi.Whitney.LiftSurfaceLayer
import CoarseDeGiorgi.Weighted.Energy

namespace CoarseDeGiorgi.Harnack.Pairing

open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- The arbitrary-function layer-energy bound. The only geometric inputs are the
collar containment and the inclusion of its radius interval; the surface
maximal bound and the weighted density identify the source quantity `D_v`.
-/
theorem exterior_subsolution_layer_of_collar {n : ℕ} {ι : Type*}
    {V : Set (Vec (n + 1))} {a : CoeffField (n + 1)}
    (U : ι → Set (Vec (n + 1))) (S : Finset ι)
    (hmeas : ∀ k ∈ S, MeasurableSet (U k))
    (hdisj : Set.PairwiseDisjoint (↑S) U)
    (hUV : ∀ k, U k ⊆ V)
    {ρ R τ D : ℝ} (hτ : 0 ≤ τ) (hD : 0 ≤ D) (j : ℕ)
    (hinterval : Ioo τ (τ + 54 * (3 : ℝ) ^ (-(j : ℝ))) ⊆ Ioo ρ R)
    (hcollar : ∀ k ∈ S, U k ⊆ Selection.cubicalAnnulus (n + 1) τ
      (τ + 54 * (3 : ℝ) ^ (-(j : ℝ))))
    (g : Vec (n + 1) → ℝ≥0∞) (hg : Measurable g)
    (hmax : Selection.surfaceEnergyMaximal ρ R g τ ≤ ENNReal.ofReal D)
    {G : Vec (n + 1) → Vec (n + 1)}
    (hE : weightedEnergy a V G < ⊤)
    (hdensity : g =ᵐ[volume.restrict V]
      (fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x))))):
    (∑ k ∈ S, (weightedEnergy a (U k) G).toReal) ≤
      54 * (3 : ℝ) ^ (-(j : ℝ)) * D := by
  have he (k : ι) :
      (∫⁻ x in U k, g x) = weightedEnergy a (U k) G := by
    exact lintegral_congr_ae (ae_mono
      (Measure.restrict_mono (hUV k) le_rfl) hdensity)
  have hEcell (k : ι) : weightedEnergy a (U k) G < ⊤ := by
    change (∫⁻ x in U k,
      ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))) < ⊤
    exact (lintegral_mono_set (hUV k)).trans_lt hE
  have hlayer := CoarseDeGiorgi.Whitney.lift_subsolution_layer_of_collar
    U S hmeas hdisj hτ j hinterval hcollar hg
  simp_rw [he] at hlayer
  have htotal := hlayer.trans (mul_le_mul' le_rfl hmax)
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 54 * (3 : ℝ) ^ (-(j : ℝ))) ] at htotal
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal
  rw [ENNReal.toReal_sum (fun k hk => (hEcell k).ne),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 54 * (3 : ℝ) ^ (-(j : ℝ)) * D)] at hreal
  exact hreal

end
end CoarseDeGiorgi.Harnack.Pairing
