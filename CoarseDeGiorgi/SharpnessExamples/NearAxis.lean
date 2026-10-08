import CoarseDeGiorgi.SharpnessExamples.ScalarLargeSets

/-! # Essential unboundedness near every point of the line segment

Large values of the subsolution sum occupy positive measure in every neighbourhood of every
interior point of the singular segment; the harmonic replacement dominates the subsolution. -/

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem cylinderCenter_tendsto_zero {d : ℕ} :
    Tendsto (fun n => cylinderCenter (d := d) (cylinderB n)) atTop (𝓝 0) := by
  have hb : Tendsto cylinderB atTop (𝓝 0) := by
    have h := (tendsto_add_atTop_iff_nat 3).2
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
    exact h
  apply tendsto_pi_nhds.mpr
  intro i
  by_cases hi : i.val = 1
  · simpa only [cylinderCenter, ite_eq_left hi, Pi.zero_apply] using hb
  · simp only [cylinderCenter, ite_eq_right hi, Pi.zero_apply]
    exact tendsto_const_nhds

/-- Arbitrarily large values occupy positive measure in every neighborhood
of every interior point on the singular line, as in the source's Step 5. -/
theorem scalarSubsolutionSum_large_near_line {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) {x₀ : Vec d}
    (hx₀ : x₀ ∈ originCube 1) (hline : ∀ i : Fin d, i.val ≠ 0 → x₀ i = 0)
    {U : Set (Vec d)} (hU : IsOpen U) (hxU : x₀ ∈ U) (N : ℕ) :
    ∃ E : Set (Vec d), E ⊆ U ∩ originCube 1 ∧
      0 < (volume.restrict E) Set.univ ∧
      ∀ᵐ x ∂volume.restrict E, (N : ℝ) ≤ scalarSubsolutionSum ζ x := by
  let z := fun n => x₀ + cylinderCenter (d := d) (cylinderB n)
  have hzt : Tendsto z atTop (𝓝 x₀) := by
    simpa only [add_zero] using tendsto_const_nhds.add (cylinderCenter_tendsto_zero (d := d))
  have hV := Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1)
  have hzU : ∀ᶠ n in atTop, z n ∈ U ∩ originCube 1 :=
    hzt.eventually ((hU.inter hV.isOpen).mem_nhds ⟨hxU, hx₀⟩)
  obtain ⟨n, hnU, hnN⟩ := (hzU.and (eventually_ge_atTop (2 * N))).exists
  let E := scalarCoreBand (d := d) n ζ (cylinderRadialConstant d) ∩ (U ∩ originCube 1)
  have hrad := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2
    (cylinderRadialConstant_pos hd)).1
  have hcore : z n ∈ scalarCoreBand n ζ (cylinderRadialConstant d) := by
    have hpart : transversePart x₀ = 0 := by
      ext i
      by_cases hi : i.val = 0
      · simp only [transversePart, ite_eq_left hi, Pi.zero_apply]
      · simp only [transversePart, ite_eq_right hi, hline i hi, Pi.zero_apply]
    have hr0 : transverseNorm (z n - cylinderCenter (cylinderB n)) = 0 := by
      have heq : z n - cylinderCenter (cylinderB n) = x₀ := by dsimp only [z]; abel
      rw [heq, transverseNorm, hpart]
      simp only [euclideanNorm, vecNormSq, vecDot, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, Real.sqrt_zero]
    change transverseNorm (z n - cylinderCenter (cylinderB n)) < _
    rw [hr0]
    exact hrad
  have hEc : IsOpen E := (isOpen_lt
    (lineRadius_continuous.comp (continuous_id.sub continuous_const)) continuous_const).inter
    (hU.inter hV.isOpen)
  refine ⟨E, Set.inter_subset_right, ?_, ?_⟩
  · rw [Measure.restrict_apply_univ]
    exact hEc.measure_pos (μ := volume) ⟨z n, hcore, hnU⟩
  · filter_upwards [ae_restrict_mem hEc.measurableSet] with x hx
    rw [scalarSubsolutionSum_eq_on_core hd hζ0 hζ2 hx.1]
    have hh := scalarCylinderSubsolution_core_lower hd hζ0 hζ2 hx.1
    have hN : (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / 2 := by
      have hcast : (2 : ℝ) * (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
      push_cast
      linarith only [hcast]
    exact hN.trans hh

/-- Large sets in every neighbourhood force an infinite `L^∞` norm. -/
theorem eLpNorm_top_eq_top_of_large_sets {d : ℕ} {S : Set (Vec d)} {u : Vec d → ℝ}
    (hu : ∀ N : ℕ, ∃ E : Set (Vec d), E ⊆ S ∧ 0 < (volume.restrict E) Set.univ ∧
      ∀ᵐ x ∂(volume.restrict E), (N : ℝ) ≤ u x) :
    eLpNorm u ⊤ (volume.restrict S) = ⊤ := by
  by_cases hmeas : AEStronglyMeasurable u (volume.restrict S)
  swap
  · exact eLpNorm_of_not_aestronglyMeasurable hmeas
  by_contra hne
  have hfin : eLpNorm u ⊤ (volume.restrict S) < ⊤ := lt_top_iff_ne_top.mpr hne
  obtain ⟨N, hN⟩ := exists_nat_gt (eLpNorm u ⊤ (volume.restrict S)).toReal
  obtain ⟨E, hES, hEpos, hEu⟩ := hu N
  have hlt : eLpNorm u ⊤ (volume.restrict S) < ENNReal.ofReal (N : ℝ) := by
    rw [← ENNReal.ofReal_toReal hne]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hN)).mpr hN
  have hall : ∀ᵐ x ∂(volume.restrict S), ‖u x‖ₑ ≤ eLpNorm u ⊤ (volume.restrict S) := by
    rw [eLpNorm_exponent_top hmeas]
    exact enorm_ae_le_eLpNormEssSup u _
  have hallE := ae_restrict_of_ae_restrict_of_subset hES hall
  have hfalse : ∀ᵐ x ∂(volume.restrict E), False := by
    filter_upwards [hEu, hallE] with x hx1 hx2
    have h1 : ENNReal.ofReal (N : ℝ) ≤ ‖u x‖ₑ :=
      (ENNReal.ofReal_le_ofReal hx1).trans (Real.ofReal_le_enorm _)
    exact absurd (h1.trans hx2) (not_le.mpr hlt)
  have hzero : (volume.restrict E) Set.univ = 0 := by simpa using (ae_iff.mp hfalse)
  exact (ne_of_gt hEpos) hzero

/-- The solution dominating the subsolution sum is essentially unbounded in every neighbourhood
of every point of the singular segment. -/
theorem solution_unbounded_near_axis {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) {u : Vec d → ℝ}
    (hdom : ∀ᵐ x ∂(volume.restrict (originCube 1)), 1 + scalarSubsolutionSum ζ x ≤ u x)
    {x₀ : Vec d} (hx₀ : x₀ ∈ originCube 1) (hline : ∀ i : Fin d, i.val ≠ 0 → x₀ i = 0)
    {N : Set (Vec d)} (hN : N ∈ 𝓝 x₀) :
    eLpNorm u ⊤ (volume.restrict (N ∩ originCube 1)) = ⊤ := by
  apply eLpNorm_top_eq_top_of_large_sets
  intro M
  obtain ⟨E, hE, hEpos, hEv⟩ := scalarSubsolutionSum_large_near_line hd hζ0 hζ2 hx₀ hline
    isOpen_interior (mem_interior_iff_mem_nhds.mpr hN) M
  refine ⟨E, fun x hx => ⟨interior_subset (hE hx).1, (hE hx).2⟩, hEpos, ?_⟩
  have hdomE := ae_restrict_of_ae_restrict_of_subset (fun x hx => (hE hx).2) hdom
  filter_upwards [hEv, hdomE] with x hx1 hx2
  have h0 : 0 ≤ scalarSubsolutionSum ζ x := le_trans (Nat.cast_nonneg M) hx1
  linarith

end

end CoarseDeGiorgi.SharpnessExamples
