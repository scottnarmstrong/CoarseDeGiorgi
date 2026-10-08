module

public import CoarseDeGiorgi.Statements.PositiveCap
public import CoarseDeGiorgi.Statements.PositiveCapGradient
public import CoarseDeGiorgi.Statements.H1aWeightedNorm
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import CoarseDeGiorgi.Weighted.TestingNonnegative
public import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
public import CoarseDeGiorgi.Assembly.LocalBoundedness

/-! Elementary facts on the zero-level truncation of a nonnegative weighted subsolution, used to
apply the energy bound at a good radius with `k = 0`. -/

@[expose] public section

namespace CoarseDeGiorgi.CgCaccioppoli

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

section
variable {d : ℕ}

theorem positiveCap_zero_top (v : Vec d → ℝ) :
    positiveCap v 0 ⊤ = fun x => max (v x) 0 := by
  funext x
  simp [positiveCap, positivePart]

theorem positiveCapGradient_zero_top (v : Vec d → ℝ) (G : Vec d → Vec d) :
    positiveCapGradient v G 0 ⊤ = {x | 0 < v x}.indicator G := by
  funext x
  by_cases hx : 0 < v x <;>
    simp [positiveCapGradient, positiveTruncationGradient, hx]

theorem eLpNorm_positiveCap_le (v : Vec d → ℝ) (μ : Measure (Vec d)) :
    eLpNorm (positiveCap v 0 ⊤) 2 μ ≤ eLpNorm v 2 μ := by
  by_cases hv : AEStronglyMeasurable v μ
  · rw [positiveCap_zero_top]
    refine eLpNorm_mono ((continuous_id.max continuous_const).comp_aestronglyMeasurable hv) ?_
    intro x
    simp only [Real.norm_eq_abs]
    rcases le_total (v x) 0 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h]
  · rw [eLpNorm_of_not_aestronglyMeasurable hv]
    exact le_top

theorem surfaceFracSeminorm_positiveCap_le (τ α r : ℝ) (hr : 0 < r) (v : Vec d → ℝ) :
    surfaceFracSeminorm τ α r (positiveCap v 0 ⊤) ≤ surfaceFracSeminorm τ α r v := by
  unfold surfaceFracSeminorm
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply lintegral_mono
  intro p
  unfold fracKernelWithDimension
  apply ENNReal.ofReal_le_ofReal
  rw [positiveCap_zero_top]
  apply div_le_div_of_nonneg_right _ (by
    apply Real.rpow_nonneg
    exact Real.sqrt_nonneg _)
  apply Real.rpow_le_rpow (abs_nonneg _) _ hr.le
  exact abs_max_sub_max_le_abs _ _ _

end

section
variable {d : ℕ} {a : CoeffField d}

/-- The zero-level truncation of a nonnegative weighted subsolution (with its truncated
gradient) is again a weighted subsolution. -/
theorem isWeightedSubsolution_positiveCap_zero [NeZero d]
    (hV : IsOpenBoundedConvexDomain (originCube (d := d) 1))
    (hne : (originCube (d := d) 1).Nonempty)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : IsWeightedSubsolution a (originCube 1) v G)
    (hvpos : ∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ v x) :
    IsWeightedSubsolution a (originCube 1) (positiveCap v 0 ⊤)
      (positiveCapGradient v G 0 ⊤) := by
  obtain ⟨hval, hgrad⟩ := Weighted.nonnegative_pair_posPart_ae hV hne ha hv.1 hvpos
  rw [positiveCap_zero_top, positiveCapGradient_zero_top]
  refine ⟨Weighted.MemH1a.congr_ae hv.1 hval.symm hgrad.symm, ?_⟩
  intro φ hφ hc hs hnn
  obtain ⟨hI, hle⟩ := hv.2 φ hφ hc hs hnn
  have hae : (fun x => vecDot (smoothGrad φ x) (matVecMul (a x) ({x | 0 < v x}.indicator G x)))
      =ᵐ[volume.restrict (originCube 1)]
      (fun x => vecDot (smoothGrad φ x) (matVecMul (a x) (G x))) := by
    filter_upwards [hgrad] with x hx
    rw [hx]
  exact ⟨hI.congr_fun_ae hae.symm, by rw [integral_congr_ae hae]; exact hle⟩

end

section
variable {d : ℕ}

theorem volume_originCube_one : volume (originCube (d := d) 1) = 1 := by
  have he : CoarseDeGiorgi.originCube (d := d) 1 =
      Set.pi Set.univ (fun _ => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext x
    simp only [CoarseDeGiorgi.originCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      Set.mem_Ioo, forall_const]
  rw [he, volume_pi]
  norm_num

/-- L¹ convergence of the values and convergence of the energies give convergence in the
weighted norm `h1aWeightedNorm` on the unit cube. -/
theorem h1aWeightedNorm_tendsto_of_l1_energy {a : CoeffField d}
    {w : ℕ → Vec d → ℝ} {G : ℕ → Vec d → Vec d}
    (hL1 : Tendsto (fun i => eLpNorm (w i) 1 (volume.restrict (originCube 1)))
      atTop (𝓝 0))
    (hE : Tendsto (fun i => weightedEnergy a (originCube 1) (G i)) atTop (𝓝 0)) :
    Tendsto (fun i => h1aWeightedNorm a (originCube 1) (w i) (G i)) atTop (𝓝 0) := by
  have hmean : ∀ i, ENNReal.ofReal ((volumeAverage (originCube (d := d) 1) (w i)) ^ 2) ≤
      (eLpNorm (w i) 1 (volume.restrict (originCube 1))) ^ 2 := by
    intro i
    have h1 : ENNReal.ofReal ((volumeAverage (originCube (d := d) 1) (w i)) ^ 2) =
        (‖volumeAverage (originCube (d := d) 1) (w i)‖ₑ) ^ 2 := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h1]
    by_cases hm : AEStronglyMeasurable (w i) (volume.restrict (originCube 1))
    · refine pow_le_pow_left' ?_ 2
      unfold volumeAverage
      rw [volume_originCube_one, ENNReal.toReal_one, inv_one, one_mul,
        eLpNorm_one_eq_lintegral_enorm]
      · exact enorm_integral_le_lintegral_enorm _
      · exact hm
    · rw [eLpNorm_of_not_aestronglyMeasurable hm]
      simp
  have hsum : Tendsto (fun i => (eLpNorm (w i) 1 (volume.restrict (originCube 1))) ^ 2 +
      weightedEnergy a (originCube 1) (G i)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_pow 2).tendsto 0 |>.comp hL1
    simpa using this.add hE
  have hroot := (ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0 |>.comp hsum
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hroot
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hroot (fun _ => bot_le) ?_
  intro i
  unfold h1aWeightedNorm
  exact ENNReal.rpow_le_rpow (add_le_add (hmean i) le_rfl) (by norm_num)

end

end CoarseDeGiorgi.CgCaccioppoli
