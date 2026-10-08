import CoarseDeGiorgi.ExteriorIntegral.Core
import CoarseDeGiorgi.ExteriorIntegral.LayerEnergyWide

/-! # Exterior pairing with the wider width bound -/

namespace CoarseDeGiorgi.ExteriorIntegral.WideWidth

open Homogenization MeasureTheory Set Whitney ExteriorIntegral
open scoped ENNReal

noncomputable section

/-- The bound of the exterior integral by the sum over layers. -/
theorem exterior_bound_core {n : ℕ} [NeZero (n + 1)] {a : CoeffField (n + 1)}
    (ha : IsWeightedCoeffOn (originCube 1) a)
    {ρ₁ ρ₂ τ h : ℝ} (hd : 3 ≤ n + 1) (hρ₁ : 1 / 2 ≤ ρ₁) (hρ₂ : ρ₂ ≤ 1)
    (hτ : τ ∈ selectionInterval ρ₁ ρ₂) (hτ0 : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (hwidth : h ≤ (ρ₂ - ρ₁) / (200 * ((n + 1 : ℕ) : ℝ)))
    {v : Vec (n + 1) → ℝ} {G : Vec (n + 1) → Vec (n + 1)}
    (hv : MemH1a a (originCube 1) v G) {GH : Vec (n + 1) → Vec (n + 1)}
    (hGHm : AEStronglyMeasurable GH
      (volume.restrict (originCube 1 \ closedReferenceCube (d := n + 1) τ)))
    (hvan : ∀ cell : ExteriorCell (n + 1) τ, cell ∉ whitneySimplicesNear τ h →
      ∀ᵐ x ∂(volume.restrict (exteriorCellSet cell)), GH x = 0)
    {σ θ γ β : ℝ} (hθ : 0 < θ) (hγ : γ = σ + θ) (he : 0 ≤ 1 - σ - β)
    (C F L : ℝ≥0∞)
    (hE : ∀ j : ℕ, ∑' cell : whitneySimplicesNearSize (d := n + 1) τ h j,
        weightedEnergy a (exteriorCellSet cell.1) GH ≤
      sampledUpperResponse a ha j τ *
        (C * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
            (ENNReal.ofReal ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-((j : ℝ) * γ))) * F) ^ 2 +
          C * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
            (ENNReal.ofReal (h⁻¹ * (3 : ℝ) ^ ((j : ℝ) * β)) * L) ^ 2)) :
    ENNReal.ofReal |∫ x in originCube 1 \ closedReferenceCube (d := n + 1) τ,
        vecDot (GH x) (matVecMul (a x) (G x))| ≤
      (54 * C) ^ (1 / 2 : ℝ) *
        (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * σ))) *
          (sampledUpperResponse a ha k τ) ^ (1 / 2 : ℝ)) *
        (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ) ^ (1 / 2 : ℝ) *
        ((ENNReal.ofReal h) ^ θ * F + (ENNReal.ofReal h) ^ (-(σ + β)) * L) := by
  classical
  set Ω : Set (Vec (n + 1)) := originCube 1 \ closedReferenceCube τ with hΩdef
  have hΩm : MeasurableSet Ω :=
    (Whitney.source_cube_domain (d := n + 1) (by norm_num : (0 : ℝ) < 1)).isOpen.measurableSet.diff
      (isClosed_closedReferenceCube τ).measurableSet
  have hΩsub : Ω ⊆ originCube 1 := fun _ hx => hx.1
  let W : ℕ → Set (ExteriorCell (n + 1) τ) := fun j => whitneySimplicesNearSize τ h j
  let U : ℕ → Set (Vec (n + 1)) := fun j => ⋃ cell : W j, exteriorCellSet cell.1
  have hUm : ∀ j, MeasurableSet (U j) := fun j =>
    MeasurableSet.iUnion fun cell => cell_measurable cell.1
  have hcell_disj : ∀ j, Pairwise (Function.onFun Disjoint
      (fun cell : W j => exteriorCellSet cell.1)) := by
    intro j c b hcb
    exact cell_disjoint hτ0 hτ1 (fun he => hcb (Subtype.ext he))
  have hUdisj : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    simp only [Function.onFun, U]
    rw [Set.disjoint_iUnion_left]
    intro c
    rw [Set.disjoint_iUnion_right]
    intro b
    apply cell_disjoint hτ0 hτ1
    intro he
    apply hij
    have h1 := c.2.2
    have h2 := b.2.2
    rw [he] at h1
    omega
  have hUsub : ∀ j, U j ⊆ Ω := by
    intro j x hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
    refine ⟨layer_cell_subset hd hρ₂ hτ hh hwidth hτ0 hτ1 c.2 hc, ?_⟩
    have hcol := layer_collar hτ0 hτ1 c.2 hc
    intro hxr
    have hn : ‖x‖ ≤ τ / 2 := (pi_norm_le_iff_of_nonneg (by linarith only [hτ0])).mpr hxr
    have := hcol.1
    change τ / 2 < ‖x‖ at this
    linarith only [hn, this]
  -- the integrand vanishes off the layers
  have hcover : ∀ᵐ x ∂volume, x ∈ Ω → x ∉ ⋃ j, U j →
      vecDot (GH x) (matVecMul (a x) (G x)) = 0 := by
    have h1 := ae_exterior_mem_cell (d := n + 1) (τ := τ) hτ0 hτ1
    have h2 : ∀ᵐ x ∂(volume : Measure (Vec (n + 1))), ∀ cell : ExteriorCell (n + 1) τ,
        cell ∉ whitneySimplicesNear τ h → x ∈ exteriorCellSet cell → GH x = 0 := by
      apply ae_all_iff.mpr
      intro cell
      by_cases hn : cell ∈ whitneySimplicesNear τ h
      · exact Filter.Eventually.of_forall (fun x hx' => absurd hn hx')
      · exact ((ae_restrict_iff' (cell_measurable cell)).mp (hvan cell hn)).mono
          (fun x hx _ hmem => hx hmem)
    filter_upwards [h1, h2] with x hx1 hx2 hxΩ hxU
    obtain ⟨cell, hxc⟩ := hx1 hxΩ.2
    by_cases hn : cell ∈ whitneySimplicesNear τ h
    · obtain ⟨j, hj⟩ := near_exists_layer hτ0 hτ1 hh1 hn
      exact absurd (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨⟨cell, hj⟩, hxc⟩⟩) hxU
    · rw [hx2 cell hn hxc, vecDot_zero_left]
  -- the pairing is bounded by the sum of layer integrals
  have hlayerSum : ENNReal.ofReal |∫ x in Ω, vecDot (GH x) (matVecMul (a x) (G x))| ≤
      ∑' j, ∫⁻ x in U j, ENNReal.ofReal |vecDot (GH x) (matVecMul (a x) (G x))| := by
    set F : Vec (n + 1) → ℝ := fun x => vecDot (GH x) (matVecMul (a x) (G x)) with hF
    have h1 : ENNReal.ofReal |∫ x in Ω, F x| ≤ ∫⁻ x in Ω, ENNReal.ofReal |F x| := by
      have := enorm_integral_le_lintegral_enorm (μ := volume.restrict Ω) F
      simpa only [Real.enorm_eq_ofReal_abs] using this
    have hUU : MeasurableSet (⋃ j, U j) := MeasurableSet.iUnion hUm
    have hsplit := lintegral_inter_add_sdiff (μ := volume)
      (fun x => ENNReal.ofReal |F x|) Ω hUU
    have hinter : Ω ∩ ⋃ j, U j = ⋃ j, U j :=
      Set.inter_eq_right.mpr (Set.iUnion_subset hUsub)
    have hzero : ∫⁻ x in Ω \ ⋃ j, U j, ENNReal.ofReal |F x| = 0 := by
      have hae : ∀ᵐ x ∂(volume.restrict (Ω \ ⋃ j, U j)), ENNReal.ofReal |F x| = 0 := by
        rw [ae_restrict_iff' (hΩm.diff hUU)]
        filter_upwards [hcover] with x hx hxm
        simp only [hF]
        rw [hx hxm.1 hxm.2, abs_zero, ENNReal.ofReal_zero]
      rw [lintegral_congr_ae hae, lintegral_zero]
    rw [hinter, hzero, add_zero] at hsplit
    rw [lintegral_iUnion hUm hUdisj] at hsplit
    exact h1.trans (hsplit.symm.le)
  -- the layer bound
  have hlayer : ∀ j : ℕ, ∫⁻ x in U j, ENNReal.ofReal |vecDot (GH x) (matVecMul (a x) (G x))| ≤
      (54 * C) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (Real.rpow 3 (-((j : ℝ) * σ))) *
          (sampledUpperResponse a ha j τ) ^ (1 / 2 : ℝ)) *
        (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ) ^ (1 / 2 : ℝ) *
        ((ENNReal.ofReal h) ^ θ * F + (ENNReal.ofReal h) ^ (-(σ + β)) * L) := by
    intro j
    by_cases hemp : IsEmpty (W j)
    · have : U j = ∅ := by
        simp only [U]
        exact Set.iUnion_eq_empty.mpr (fun c => (hemp.false c).elim)
      rw [this]
      simp
    rw [not_isEmpty_iff] at hemp
    obtain ⟨c₀⟩ := hemp
    have hl : (3 : ℝ) ^ (-(j : ℤ)) ≤ h := by
      have := layer_small hτ0 hτ1 c₀.2
      have hr : (3 : ℝ) ^ (-(j : ℤ)) = (3 : ℝ) ^ (-(j : ℝ)) := by
        rw [← Real.rpow_intCast]; simp
      rw [hr]
      have : 0 < (3 : ℝ) ^ (-(j : ℝ)) := by positivity
      linarith only [this, ‹6 * (3 : ℝ) ^ (-(j : ℝ)) < h›]
    have hUsubO : U j ⊆ originCube 1 := (hUsub j).trans hΩsub
    have haU : IsWeightedCoeffOn (U j) a := lift_coeff_mono ha hUsubO
    have hGm : AEStronglyMeasurable G (volume.restrict (U j)) :=
      hv.2.1.mono_measure (Measure.restrict_mono hUsubO le_rfl)
    have hGHm' : AEStronglyMeasurable GH (volume.restrict (U j)) :=
      hGHm.mono_measure (Measure.restrict_mono (hUsub j) le_rfl)
    have hHold := lintegral_pairing_le haU hGHm' hGm
    have hunion (X : Vec (n + 1) → Vec (n + 1)) :
        weightedEnergy a (U j) X = ∑' cell : W j, weightedEnergy a (exteriorCellSet cell.1) X := by
      have hU : U j = ⋃ cell : W j, exteriorCellSet cell.1 := rfl
      unfold weightedEnergy
      rw [hU]
      exact lintegral_iUnion (s := fun cell : W j => exteriorCellSet cell.1)
        (fun cell => cell_measurable cell.1) (hcell_disj j)
        (fun x => ENNReal.ofReal (vecDot (X x) (matVecMul (a x) (X x))))
    have hEG := layer_energy_le ha hd hρ₁ hρ₂ hτ hτ0 hτ1 hh hwidth hv j
    have h54 : ENNReal.ofReal (54 * (3 : ℝ) ^ (-(j : ℝ))) =
        54 * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) := by
      have hr : (3 : ℝ) ^ (-(j : ℤ)) = (3 : ℝ) ^ (-(j : ℝ)) := by
        rw [← Real.rpow_intCast]; simp
      rw [ENNReal.ofReal_mul (by norm_num), hr]
      simp
    rw [h54] at hEG
    rw [hunion GH, hunion G] at hHold
    have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have hw0 := exponent_one j hθ hγ hh hl
    have hw1 := exponent_two j he hh hl
    calc _ ≤ _ := hHold
      _ ≤ (sampledUpperResponse a ha j τ *
            (C * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
              (ENNReal.ofReal ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-((j : ℝ) * γ))) * F) ^ 2 +
            C * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
              (ENNReal.ofReal (h⁻¹ * (3 : ℝ) ^ ((j : ℝ) * β)) * L) ^ 2)) ^ (1 / 2 : ℝ) *
          (54 * ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
            surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ) ^ (1 / 2 : ℝ) := by
        gcongr
        exact hE j
      _ ≤ _ := layer_product_bound _ _ _ _ _ _ _ _
      _ ≤ (54 * C) ^ (1 / 2 : ℝ) * (sampledUpperResponse a ha j τ) ^ (1 / 2 : ℝ) *
          (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal ((3 : ℝ) ^ (-((j : ℝ) * σ))) * (ENNReal.ofReal h) ^ θ * F +
            ENNReal.ofReal ((3 : ℝ) ^ (-((j : ℝ) * σ))) *
              (ENNReal.ofReal h) ^ (-(σ + β)) * L) := by
        gcongr
      _ = _ := by
        simp only [Real.rpow_eq_pow]
        ring
  calc _ ≤ _ := hlayerSum
    _ ≤ ∑' j : ℕ, ((54 * C) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (Real.rpow 3 (-((j : ℝ) * σ))) *
          (sampledUpperResponse a ha j τ) ^ (1 / 2 : ℝ)) *
        (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ) ^ (1 / 2 : ℝ) *
        ((ENNReal.ofReal h) ^ θ * F + (ENNReal.ofReal h) ^ (-(σ + β)) * L)) :=
      ENNReal.tsum_le_tsum hlayer
    _ = _ := by
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

end

end CoarseDeGiorgi.ExteriorIntegral.WideWidth
