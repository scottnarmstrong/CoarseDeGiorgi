module

public import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
public import Mathlib.Analysis.Convex.Measure

/-! # Signed-test integral splitting -/

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open Homogenization MeasureTheory Set

/-- Split an integrable cube integral into a measurable inner set and its
relative complement. -/
theorem integral_split_of_subset
    {d : ℕ} {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hUV : U ⊆ V) (f : Vec d → ℝ) (hf : IntegrableOn f V) :
    ∫ x in V, f x = (∫ x in U, f x) + ∫ x in V \ U, f x := by
  have hinnerMeasure : (volume.restrict V).restrict U = volume.restrict U := by
    rw [Measure.restrict_restrict hU, inter_eq_left.mpr hUV]
  have houterMeasure : (volume.restrict V).restrict Uᶜ = volume.restrict (V \ U) := by
    rw [Measure.restrict_restrict hU.compl, inter_comm, Set.sdiff_eq]
  have hsplit := integral_add_compl (μ := volume.restrict V) hU hf
  change (∫ x, f x ∂((volume.restrict V).restrict U)) +
      ∫ x, f x ∂((volume.restrict V).restrict Uᶜ) =
        ∫ x, f x ∂(volume.restrict V) at hsplit
  rw [hinnerMeasure, houterMeasure] at hsplit
  calc
    ∫ x in V, f x = ∫ x, f x ∂(volume.restrict V) := by
      rw [← setIntegral_univ]
    _ = _ := hsplit.symm

/-- Removing the boundary of a bounded convex open inner domain does not
change an exterior integral. -/
theorem integral_exterior_eq_closure_exterior
    {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    (f : Vec d → ℝ) :
    ∫ x in V \ U, f x = ∫ x in V \ closure U, f x := by
  have hfrontier : volume (frontier U) = 0 := hU.convex.addHaar_frontier volume
  have hnot : ∀ᵐ x ∂volume, x ∉ frontier U := by
    rw [ae_iff]
    simpa using hfrontier
  have hsets : (V \ U) =ᵐ[volume] (V \ closure U) := by
    filter_upwards [hnot] with x hxnot
    apply propext
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hxV, hxU⟩
      refine ⟨hxV, ?_⟩
      intro hxcl
      apply hxnot
      rw [frontier, hU.isOpen.interior_eq]
      exact ⟨hxcl, hxU⟩
    · rintro ⟨hxV, hxcl⟩
      exact ⟨hxV, fun hxU => hxcl (subset_closure hxU)⟩
  rw [Measure.restrict_congr_set hsets]

/-- Split both integrals in the signed test inequality. -/
theorem signed_test_inequality_of_inner_outer_split
    {d : ℕ} {U V : Set (Vec d)} (hU : MeasurableSet U)
    (hUV : U ⊆ V) (L R : Vec d → ℝ)
    (hL : IntegrableOn L V) (hR : IntegrableOn R V)
    (m : ℝ)
    (htest : m * (∫ x in V, L x) ≥ (1 - m) * (∫ x in V, R x)) :
    m * ((∫ x in U, L x) + (∫ x in V \ U, L x)) ≥
      (1 - m) * ((∫ x in U, R x) + (∫ x in V \ U, R x)) := by
  rw [← integral_split_of_subset hU hUV L hL,
    ← integral_split_of_subset hU hUV R hR]
  exact htest

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
