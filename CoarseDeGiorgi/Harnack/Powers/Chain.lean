module

public import CoarseDeGiorgi.Harnack.Powers.Extensions
public import CoarseDeGiorgi.Weighted.Truncation.Closure

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Powers

open Homogenization MeasureTheory
open scoped ENNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The shifted powers and their derivatives belong to the weighted completion when the
underlying represented function is nonnegative almost everywhere.
-/
theorem signedPower_chain (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a V u G)
    (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x)
    (ε m : ℝ) (hε : 0 < ε) (hm : m < 1 / 2) :
    MemH1a a V (fun x => (u x + ε) ^ m)
        (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ∧
      MemH1a a V (fun x => (u x + ε) ^ (m - 1))
        (fun x => ((m - 1) * (u x + ε) ^ (m - 2)) • G x) ∧
      (∀ᵐ x ∂volume.restrict V, (u x + ε) ^ (m - 1) ≤ ε ^ (m - 1)) := by
  obtain ⟨Φ, hΦ, hΦval, hΦderiv, L, hL⟩ :=
    exists_smooth_shifted_rpow_extension ε m hε (by linarith)
  obtain ⟨Ψ, hΨ, hΨval, hΨderiv, M, hM⟩ :=
    exists_smooth_shifted_rpow_extension ε (m - 1) hε (by linarith)
  have hv := Weighted.MemH1a.comp hV hne ha hu hΦ hL
  have hvval : (Φ ∘ u) =ᵐ[volume.restrict V] (fun x => (u x + ε) ^ m) := by
    filter_upwards [hnonneg] with x hx
    exact hΦval (u x) hx
  have hvgrad : (fun x => deriv Φ (u x) • G x) =ᵐ[volume.restrict V]
      (fun x => (m * (u x + ε) ^ (m - 1)) • G x) := by
    filter_upwards [hnonneg] with x hx
    rw [hΦderiv (u x) hx]
  have hpow : Weighted.MemH1a a V (fun x => (u x + ε) ^ m)
      (fun x => (m * (u x + ε) ^ (m - 1)) • G x) :=
    Weighted.MemH1a.congr_ae hv hvval hvgrad
  have hψ := Weighted.MemH1a.comp hV hne ha hu hΨ hM
  have hψval : (Ψ ∘ u) =ᵐ[volume.restrict V]
      (fun x => (u x + ε) ^ (m - 1)) := by
    filter_upwards [hnonneg] with x hx
    exact hΨval (u x) hx
  have hψgrad : (fun x => deriv Ψ (u x) • G x) =ᵐ[volume.restrict V]
      (fun x => ((m - 1) * (u x + ε) ^ (m - 2)) • G x) := by
    filter_upwards [hnonneg] with x hx
    rw [hΨderiv (u x) hx]
    rw [show m - 1 - 1 = m - 2 by ring]
  have hpowPrev := Weighted.MemH1a.congr_ae hψ hψval hψgrad
  have hbound : ∀ᵐ x ∂volume.restrict V,
      (u x + ε) ^ (m - 1) ≤ ε ^ (m - 1) := by
    filter_upwards [hnonneg] with x hx
    exact Real.rpow_le_rpow_of_nonpos hε (le_add_of_nonneg_left hx) (by linarith)
  exact ⟨hpow, hpowPrev, hbound⟩

end CoarseDeGiorgi.Harnack.Powers
