import CoarseDeGiorgi.Harnack.Powers.AdmissibleProduct
import CoarseDeGiorgi.Harnack.Powers.SignedTesting

namespace CoarseDeGiorgi.Harnack.Powers

open Homogenization MeasureTheory
open scoped ENNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The source signed-power package: membership and the source `L^r` bound for
`v = (u + ε)^m`, integrability of `v⁻¹ Gv · aGv`, and signed testing against
every bounded nonnegative compactly supported weighted Sobolev test.
-/
theorem signedPower_source_package (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a a V u G)
    (hsup : IsWeightedSubsolution a V (-u) (-G))
    (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x)
    (ε m r : ℝ) (hε : 0 < ε) (hm : m < 1 / 2) (hm0 : m ≠ 0)
    (hr1 : 1 < r) (hr2 : r < 2) :
    MemH1a a V (fun x => (u x + ε) ^ m)
        (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ∧
      MemLp (fun x => (u x + ε) ^ m) (ENNReal.ofReal r) (volume.restrict V) ∧
      IntegrableOn (fun x => m ^ 2 * (u x + ε) ^ (m - 2) *
        vecDot (G x) (matVecMul (a x) (G x))) V ∧
      ((fun x => ((u x + ε) ^ m)⁻¹ *
          vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
            (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) =ᵐ[
        volume.restrict V] (fun x => m ^ 2 * (u x + ε) ^ (m - 2) *
          vecDot (G x) (matVecMul (a x) (G x)))) ∧
      (∀ {φ : Vec d → ℝ} {H : Vec d → Vec d},
        MemH1a a V φ H →
        (∀ᵐ x ∂volume.restrict V, 0 ≤ φ x) →
        (∃ B : ℝ, ∀ᵐ x ∂volume.restrict V, |φ x| ≤ B) →
        ∀ {K : Set (Vec d)}, IsCompact K → K ⊆ V →
          (∀ᵐ x ∂volume.restrict V, x ∉ K → φ x = 0) →
          m * (∫ x in V, vecDot (H x)
              (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) ≥
            (1 - m) * (∫ x in V,
              (φ x / ((u x + ε) ^ m)) *
                vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
                  (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x)))) := by
  have hchain := signedPower_chain hV hne ha hu hnonneg ε m hε hm
  have hsource := signedPower_source_integrability hV hne ha hu hnonneg ε m r
    hε hm hm0 hr1 hr2
  have hdensity := signedPower_source_density_identity (V := V) (a := a)
    (u := u) (G := G) hnonneg ε m hε
  refine ⟨hchain.1, hsource.1, hsource.2, hdensity, ?_⟩
  intro φ H hφ hφnonneg hφbound K hK hKV hφzero
  obtain ⟨Gψ, hψ, hψgrad, _⟩ := signedPower_admissible_product hV hne ha hu
    hnonneg ε m hε hm hφ hφbound hφnonneg hK hKV hφzero
  exact signedPower_signed_test_of_admissible_product hV hne ha hu hsup
    hnonneg ε m hε hm hm0 hφ hφnonneg hφbound hψ hψgrad

end CoarseDeGiorgi.Harnack.Powers
