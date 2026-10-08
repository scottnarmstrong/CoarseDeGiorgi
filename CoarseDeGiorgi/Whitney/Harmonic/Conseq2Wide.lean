module

public import CoarseDeGiorgi.Whitney.Harmonic.Conseq2
public import CoarseDeGiorgi.Whitney.Harmonic.ConseqWide
public import CoarseDeGiorgi.Whitney.Harmonic.GaussGreen
public import CoarseDeGiorgi.Weighted.Identification
public import CoarseDeGiorgi.Foundations.Reconstruction.Representatives
public import CoarseDeGiorgi.Statements.CubeFaceMeasure

/-! The `W^{1,1}` and trace assertions of Proposition `p.whitney.extension`. -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

/-- `H_h f ∈ W^{1,1}(□₀ ∖ τ□̄₀)` with finite energy. -/
theorem w11_statement (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    {a : CoeffField d} (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {f : Vec d → ℝ} (hfacts : AffFacts τ h ρ₂ hτ0 hτ1 f)
    (hf : ∃ K : ℝ≥0, LipschitzOnWith K f (CoarseDeGiorgi.cubeSurface (d := d) τ))
    {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH) :
    Integrable H (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1 \
        CoarseDeGiorgi.closedReferenceCube (d := d) τ)) ∧
      Integrable GH (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1 \
        CoarseDeGiorgi.closedReferenceCube (d := d) τ)) ∧
      HasWeakGradientOn (CoarseDeGiorgi.originCube (d := d) 1 \
        CoarseDeGiorgi.closedReferenceCube (d := d) τ) H GH ∧
      weightedEnergy a (CoarseDeGiorgi.originCube (d := d) 1 \
        CoarseDeGiorgi.closedReferenceCube (d := d) τ) GH < ⊤ := by
  have : NeZero d := ⟨by omega⟩
  have hτpos : 0 < τ := by linarith
  obtain ⟨w, K₂, hw, hwf⟩ := exists_lipschitz_extension hf
  obtain ⟨Φ, K, ξ, Gξ, hΦ, hΦB, hξ, hψ, hH, hB⟩ :=
    glued_correction hd hτ0 hτ1 hρ₂ hτρ hh hwidth ha hfacts hHGH
      (hw.lipschitzOnWith) hwf
  have hOd : IsOpenBoundedConvexDomain (CoarseDeGiorgi.originCube (d := d) 1) :=
    Whitney.source_cube_domain (by norm_num)
  have hOne : (CoarseDeGiorgi.originCube (d := d) 1).Nonempty := Whitney.source_cube_nonempty (by norm_num)
  have hBc := isClosed_closedRef (d := d) hτpos.le
  have hSsub : CoarseDeGiorgi.originCube (d := d) 1 \ CoarseDeGiorgi.closedReferenceCube (d := d) τ ⊆
      CoarseDeGiorgi.originCube (d := d) 1 := sdiff_subset
  have hSopen : IsOpen (CoarseDeGiorgi.originCube (d := d) 1 \
      CoarseDeGiorgi.closedReferenceCube (d := d) τ) := hOd.isOpen.sdiff hBc
  obtain ⟨hi, hGi, hweak, -, hE⟩ := Weighted.memH1a_memW11 hOd hOne ha
    (Weighted.MemH1a0.memH1a ha hψ)
  have hHae : H =ᵐ[volume.restrict (CoarseDeGiorgi.originCube (d := d) 1 \
      CoarseDeGiorgi.closedReferenceCube (d := d) τ)] (Φ + ξ) := hH.mono fun x hx => hx.1
  have hGae : GH =ᵐ[volume.restrict (CoarseDeGiorgi.originCube (d := d) 1 \
      CoarseDeGiorgi.closedReferenceCube (d := d) τ)] (CoarseDeGiorgi.smoothGrad Φ + Gξ) :=
    hH.mono fun x hx => hx.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hi.mono_set hSsub).congr hHae.symm
  · have : Integrable (CoarseDeGiorgi.smoothGrad Φ + Gξ)
        (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1 \
          CoarseDeGiorgi.closedReferenceCube (d := d) τ)) :=
      integrable_pi_iff.mpr fun i => (hGi i).mono_set hSsub
    exact this.congr hGae.symm
  · exact Foundations.Reconstruction.hasWeakGradientOn_congr_ae hHae.symm hGae.symm
      (HasWeakGradientOn.restrict hSopen hSsub hweak)
  · rw [show weightedEnergy a (CoarseDeGiorgi.originCube (d := d) 1 \
        CoarseDeGiorgi.closedReferenceCube (d := d) τ) GH =
      weightedEnergy a (CoarseDeGiorgi.originCube (d := d) 1 \
        CoarseDeGiorgi.closedReferenceCube (d := d) τ) (CoarseDeGiorgi.smoothGrad Φ + Gξ) from
      Weighted.energy_congr_ae hGae]
    exact lt_of_le_of_lt (lintegral_mono_set hSsub) hE

end CoarseDeGiorgi.Whitney.Harmonic.Wide
