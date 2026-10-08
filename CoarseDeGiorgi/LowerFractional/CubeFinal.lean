import CoarseDeGiorgi.LowerFractional.CubeGates
import CoarseDeGiorgi.LowerFractional.CubeScaleGate
import CoarseDeGiorgi.LowerFractional.CompactCover
import CoarseDeGiorgi.Statements.FractionalReconstruction

/-! The bounds of `p.lower.fractional` for cubes `Q ⊆ □₀`, and integrability of `H¹_a(□₀)` in `L^r(□₀)`. -/

namespace CoarseDeGiorgi.LowerFractional
open Homogenization MeasureTheory Aliases
open scoped ENNReal

theorem cube_reconstruction : LowerReconstructionHypothesis := by
  intro d α r hα0 hα1 hr
  exact CoarseDeGiorgi.fractional_reconstruction hα0 hα1 hr

theorem lower_fractional_memLr_proved {d : ℕ} (hd : 3 ≤ d) (p q s t : ℝ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (Aliases.originCube 1) a)
    (hrange : spatialMomentRange a ha p q s t)
    (w : Vec d → ℝ) (G : Vec d → Vec d) (hw : MemH1a a (Aliases.originCube 1) w G) :
    MemLp w (ENNReal.ofReal (paramR q)) (volume.restrict (Aliases.originCube 1)) := by
  let : NeZero d := ⟨by omega⟩
  have hq : 1 < q := by
    obtain ⟨_, _, _, _, _, hq, _⟩ := hrange
    exact hq
  have hr : 0 < paramR q := zero_lt_one.trans (lower_paramR_gt_one hq)
  obtain ⟨C, hC, hbound⟩ := lower_fractional_embedding_of_reconstruction
    cube_reconstruction hd p q s t a ha hrange 1 (fun _ => 0)
    (by rw [← lower_unitCube_eq_auxCube])
  have hwQ : MemH1a a (auxCube 1 (fun _ => 0)) w G := by
    rwa [← lower_unitCube_eq_auxCube]
  have hNorm : h1aWeightedNorm a (Aliases.originCube 1) w G < ⊤ := by
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
      Weighted.MemH1a.energy_lt_top lower_unitCube_domain.isOpen ha hw⟩).ne
  have hfinite := (lower_eLpNorm_le_fracNorm (α := alphaParam t) hr w).trans_lt
    ((hbound w G hwQ).trans_lt (ENNReal.mul_lt_top hC
      (by rwa [← lower_unitCube_eq_auxCube])))
  rw [← lower_unitCube_eq_auxCube] at hfinite
  exact hfinite

end CoarseDeGiorgi.LowerFractional
