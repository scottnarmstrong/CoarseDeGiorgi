module

public import CoarseDeGiorgi.Harnack.Powers.Chain
public import CoarseDeGiorgi.Harnack.Calculus.BoundedAlgebra
public import CoarseDeGiorgi.Weighted.TestingCompactSupport

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Powers

open Homogenization MeasureTheory
open scoped ENNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The bounded source test `φ` multiplied by `U^(m-1)` is an admissible
zero-boundary pair, with the explicit product gradient and nonnegative value.
-/
theorem signedPower_admissible_product (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a a V u G)
    (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x)
    (ε m : ℝ) (hε : 0 < ε) (hm : m < 1 / 2)
    {φ : Vec d → ℝ} {H : Vec d → Vec d}
    (hφ : MemH1a a V φ H)
    (hφbound : ∃ B : ℝ, ∀ᵐ x ∂volume.restrict V, |φ x| ≤ B)
    (hφnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ φ x)
    {K : Set (Vec d)} (hK : IsCompact K) (hKV : K ⊆ V)
    (hφzero : ∀ᵐ x ∂volume.restrict V, x ∉ K → φ x = 0) :
    ∃ Gψ : Vec d → Vec d,
      MemH1a0 a V (fun x => (u x + ε) ^ (m - 1) * φ x) Gψ ∧
      Gψ =ᵐ[volume.restrict V]
        (fun x => (u x + ε) ^ (m - 1) • H x +
          φ x • (((m - 1) * (u x + ε) ^ (m - 2)) • G x)) ∧
      (∀ᵐ x ∂volume.restrict V, 0 ≤ (u x + ε) ^ (m - 1) * φ x) := by
  have hchain := signedPower_chain hV hne ha hu hnonneg ε m hε hm
  have hFbound : ∀ᵐ x ∂volume.restrict V,
      |(u x + ε) ^ (m - 1)| ≤ ε ^ (m - 1) := by
    filter_upwards [hnonneg, hchain.2.2] with x hx hbound
    have hU : 0 < u x + ε := by linarith
    rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt hU) _)]
    exact hbound
  obtain ⟨B, hB⟩ := hφbound
  have hproduct := CoarseDeGiorgi.Harnack.Calculus.MemH1a.mul_bounded
    hV hne ha hchain.2.1 hφ hFbound hB
  have hsupport : ∀ᵐ x ∂volume.restrict V,
      x ∉ K → (u x + ε) ^ (m - 1) * φ x = 0 := by
    filter_upwards [hφzero] with x hx xK
    simp [hx xK]
  have hproduct0 := Weighted.MemH1a.memH1a0_of_compact_support
    hV hne ha hproduct hK hKV hsupport
  have hψnonneg : ∀ᵐ x ∂volume.restrict V,
      0 ≤ (u x + ε) ^ (m - 1) * φ x := by
    filter_upwards [hnonneg, hφnonneg] with x hxU hxφ
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) hxφ
  exact ⟨_, hproduct0, Filter.EventuallyEq.rfl, hψnonneg⟩

end CoarseDeGiorgi.Harnack.Powers
