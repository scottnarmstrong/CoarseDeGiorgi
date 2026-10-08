module

public import CoarseDeGiorgi.SharpnessExamples.HarmonicComparison
public import CoarseDeGiorgi.Weighted.Truncation.Algebra
public import CoarseDeGiorgi.Whitney.ExteriorCells
public import CoarseDeGiorgi.Statements.NonnegativeEssInf

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted
open scoped ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

variable {d : ℕ} {a : CoeffField d}

/-- Add one to the harmonic replacement of a nonnegative subsolution: the result dominates
`1 + v` almost everywhere, and large values of `v` on positive-measure subsets of the half
cube force an infinite essential supremum there. -/
theorem harmonic_replacement_one_plus_dominates
    (hd : 3 ≤ d)
    (hV : IsOpenBoundedConvexDomain (CoarseDeGiorgi.originCube (d := d) 1))
    (hne : (CoarseDeGiorgi.originCube (d := d) 1).Nonempty)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube (d := d) 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : IsWeightedSubsolution a (CoarseDeGiorgi.originCube 1) v G)
    (hvnonneg : 0 ≤ᵐ[volume.restrict (CoarseDeGiorgi.originCube 1)] v)
    (hlarge : ∀ N : ℕ, ∃ E : Set (Vec d),
      E ⊆ CoarseDeGiorgi.originCube (d := d) (1 / 2) ∧
      0 < (volume.restrict E) Set.univ ∧
      ∀ᵐ x ∂(volume.restrict E), (N : ℝ) ≤ v x) :
    ∃ u : Vec d → ℝ, ∃ Gu : Vec d → Vec d,
      IsWeightedSolution a (CoarseDeGiorgi.originCube 1) u Gu ∧
      (∀ᵐ x ∂(volume.restrict (CoarseDeGiorgi.originCube 1)), 1 + v x ≤ u x) ∧
      (∀ᵐ x ∂(volume.restrict (CoarseDeGiorgi.originCube 1)), 1 ≤ u x) ∧
      eLpNorm u ⊤ (volume.restrict (CoarseDeGiorgi.originCube (1 / 2))) = ⊤ ∧
      0 < CoarseDeGiorgi.nonnegativeEssInf (CoarseDeGiorgi.originCube (1 / 2)) u ∧
      CoarseDeGiorgi.nonnegativeEssInf (CoarseDeGiorgi.originCube (1 / 2)) u < ⊤ := by
  have : NeZero d := ⟨by omega⟩
  let V := CoarseDeGiorgi.originCube (d := d) 1
  let W := CoarseDeGiorgi.originCube (d := d) (1 / 2)
  let μ := volume.restrict V
  let μW := volume.restrict W
  let : IsFiniteMeasure μ := hV.isFiniteMeasure_restrict_volume
  have hWdom : IsOpenBoundedConvexDomain W :=
    CoarseDeGiorgi.Whitney.source_cube_domain (by norm_num)
  have hWne : W.Nonempty := CoarseDeGiorgi.Whitney.source_cube_nonempty (by norm_num)
  have hμWpos : 0 < μW Set.univ := by
    simpa [μW, W, hWdom.isOpen.measurableSet] using hWdom.isOpen.measure_pos volume hWne
  have hWsubV : W ⊆ V := by
    intro x hx i
    exact ⟨by have := (hx i).1; linarith, by have := (hx i).2; linarith⟩
  have hμWle : μW ≤ μ := Measure.restrict_mono hWsubV le_rfl
  obtain ⟨U, GU, hU, hU0, hvU⟩ :=
    subsolution_le_harmonic_replacement hV hne ha hv
  let u : Vec d → ℝ := fun x => U x + 1
  have hUge : 0 ≤ᵐ[μ] U := by
    filter_upwards [hvU, hvnonneg] with x hxU hxv
    exact hxv.trans hxU
  have huge : 1 ≤ᵐ[μ] u := by
    filter_upwards [hUge] with x hx
    change 0 ≤ U x at hx
    dsimp [u]
    linarith
  have hsol : IsWeightedSolution a V u GU := by
    refine ⟨?_, ?_⟩
    · simpa [u, add_comm] using Weighted.MemH1a.add_const hV hne ha hU.1 1
    · intro φ hφ hcompact hsupport
      exact hU.2 φ hφ hcompact hsupport
  have huI : Integrable u μ := by
    have hUint : Integrable U μ := (memH1a_memW11 hV hne ha hU.1).1
    have hone : Integrable (fun _ : Vec d => (1 : ℝ)) μ := integrable_const _
    simpa [u] using hUint.add hone
  have huMeas : AEStronglyMeasurable u μW :=
    huI.aestronglyMeasurable.mono_measure hμWle
  let F : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (u x)
  let Nrm : Vec d → ℝ≥0∞ := fun x => ‖u x‖ₑ
  have hpositiveW : 1 ≤ᵐ[μW] u :=
    ae_restrict_of_ae_restrict_of_subset hWsubV huge
  have hNrmEq : Nrm =ᵐ[μW] F := by
    filter_upwards [hpositiveW] with x hx
    simp [Nrm, F, Real.enorm_eq_ofReal_abs, abs_of_nonneg (le_trans (by norm_num) hx)]
  have hInfLower : (1 : ℝ≥0∞) ≤ essInf F μW := by
    apply le_essInf_of_ae_le (f := F) 1
    filter_upwards [hpositiveW] with x hx
    simpa [F] using ENNReal.ofReal_le_ofReal hx
  have hInfNeTop : essInf F μW ≠ ⊤ := by
    intro htop
    have hzero := meas_lt_essInf (f := F) (μ := μW)
    have hset : {x | F x < essInf F μW} = Set.univ := by
      ext x
      simp [htop, F]
    rw [hset] at hzero
    exact (ne_of_gt hμWpos) hzero
  have hEssSupTop : essSup F μW = ⊤ := by
    by_contra hnot
    have hfinite : essSup F μW < ⊤ := lt_top_iff_ne_top.mpr hnot
    let C : ℝ := (essSup F μW).toReal + 1
    obtain ⟨N, hCN⟩ := exists_nat_gt C
    have hBN : essSup F μW < ENNReal.ofReal (N : ℝ) := by
      rw [← ENNReal.ofReal_toReal hfinite.ne]
      have hrealBN : (essSup F μW).toReal < (N : ℝ) := by
        dsimp [C] at hCN
        linarith
      have hCpos : 0 < C := by dsimp [C]; positivity
      have hNpos : 0 < (N : ℝ) := hCpos.trans hCN
      exact (ENNReal.ofReal_lt_ofReal_iff hNpos).mpr hrealBN
    obtain ⟨E, hEW, hEpos, hvE⟩ := hlarge N
    let ν := volume.restrict E
    have hEV : E ⊆ V := hEW.trans hWsubV
    have hNleF : (fun _ => ENNReal.ofReal (N : ℝ)) ≤ᵐ[ν] F := by
      have hvUE := ae_restrict_of_ae_restrict_of_subset hEV hvU
      filter_upwards [hvE, hvUE] with x hxv hxU
      have hx : (N : ℝ) ≤ u x := by
        dsimp [u]
        linarith
      simpa [F] using ENNReal.ofReal_le_ofReal hx
    have hFle : F ≤ᵐ[ν] fun _ => essSup F μW :=
      ae_restrict_of_ae_restrict_of_subset hEW (ENNReal.ae_le_essSup F)
    have hfalse : ∀ᵐ x ∂ν, False := by
      filter_upwards [hNleF, hFle] with x hxN hxF
      exact (not_le_of_gt hBN) (le_trans hxN hxF)
    have hνzero : ν Set.univ = 0 := by simpa using (ae_iff.mp hfalse)
    exact (ne_of_gt hEpos) hνzero
  have hEssSupNorm : essSup Nrm μW = ⊤ := by
    rw [essSup_congr_ae hNrmEq]
    exact hEssSupTop
  have hLpTop : eLpNorm u ⊤ μW = ⊤ := by
    rw [eLpNorm_exponent_top huMeas, eLpNormEssSup_eq_essSup_enorm]
    exact hEssSupNorm
  have hdom : ∀ᵐ x ∂μ, 1 + v x ≤ u x := by
    filter_upwards [hvU] with x hx
    dsimp [u]
    linarith
  refine ⟨u, GU, hsol, hdom, huge, ?_, ?_, ?_⟩
  · simpa [W, μW] using hLpTop
  · simpa [CoarseDeGiorgi.nonnegativeEssInf, F, W, μW] using
      lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1) hInfLower
  · simpa [CoarseDeGiorgi.nonnegativeEssInf, F, W, μW] using
      lt_top_iff_ne_top.mpr hInfNeTop

end CoarseDeGiorgi.SharpnessExamples
