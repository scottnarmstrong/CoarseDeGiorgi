module

public import CoarseDeGiorgi.Statements.PowerFactor
public import CoarseDeGiorgi.Harnack.Selection.Cap
public import CoarseDeGiorgi.Harnack.PowerLimits.SignedInterior
public import CoarseDeGiorgi.Harnack.PowerLimits.CapRemoval

/-! # Signed-power one-surface estimate -/

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-- Pass a uniform estimate for every positive finite cap to the original energy
using `PowerLimits.positive_cap_energy_tendsto_on_subset`.
Only the elementary order-limit passage is proved here.
-/
theorem uncapped_positive_cap_energy_bound
    {d : ℕ} [NeZero d] (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : MemH1a a (originCube 1) v G)
    (hnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ v x)
    {V : Set (Vec d)} (hV : V ⊆ originCube 1)
    (K : ℝ≥0∞)
    (hbound : ∀ N : ℕ, weightedEnergy a V
      (Selection.selectionCapGradient 0 ((N + 1 : ℕ) : ℝ≥0∞) v G) ≤ K) :
    weightedEnergy a V G ≤ K := by
  exact le_of_tendsto_of_tendsto
    (PowerLimits.positive_cap_energy_tendsto_on_subset a ha hv hnonneg hV)
    tendsto_const_nhds (Eventually.of_forall hbound)

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
