import CoarseDeGiorgi.ExteriorIntegral.Geometry
import CoarseDeGiorgi.Harnack.Pairing.ArbitraryLayer
import CoarseDeGiorgi.Harnack.WeakHarnack.SelectionAdapters
import CoarseDeGiorgi.Selection.SourceRepresentatives
import CoarseDeGiorgi.Weighted.GradientHilbert
import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
import CoarseDeGiorgi.Statements.SelectionInterval
import CoarseDeGiorgi.Statements.MemH1a

/-! # Step 1 of the exterior integral: the energy of `v` on one layer -/

namespace CoarseDeGiorgi.ExteriorIntegral.WideWidth

open Homogenization MeasureTheory Set Whitney ExteriorIntegral
open scoped ENNReal

noncomputable section

/-- The layer cells lie in `ρ₂ □₀` and the collar interval lies in the selection interval. -/
theorem layer_radius_facts {d : ℕ} {ρ₁ ρ₂ τ h : ℝ} (hd : 3 ≤ d)
    (hτ : τ ∈ selectionInterval ρ₁ ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - ρ₁) / (200 * (d : ℝ))) :
    9 * h < ρ₂ - τ := by
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 0 < 200 * (d : ℝ) := by positivity
  have hw := (le_div_iff₀ hden).mp hwidth
  have hτ' : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hτ.2
  nlinarith only [hw, hdr, hh, hτ']

theorem layer_cell_subset {n : ℕ} {ρ₁ ρ₂ τ h : ℝ} (hd : 3 ≤ n + 1)
    (hρ₂ : ρ₂ ≤ 1)
    (hτ : τ ∈ selectionInterval ρ₁ ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - ρ₁) / (200 * ((n + 1 : ℕ) : ℝ)))
    {j : ℕ} {cell : ExteriorCell (n + 1) τ}
    (hτ0 : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    (hc : cell ∈ whitneySimplicesNearSize τ h j) :
    exteriorCellSet cell ⊆ originCube 1 := by
  have : NeZero (n + 1) := ⟨by omega⟩
  have hcol := layer_collar hτ0 hτ1 hc
  have hsm := layer_small hτ0 hτ1 hc
  have hr := layer_radius_facts hd hτ hh hwidth
  intro x hx
  have hxa := (hcol hx).2
  have hn : ‖x‖ < 1 / 2 := by
    change ‖x‖ < (τ + 54 * (3 : ℝ) ^ (-(j : ℝ))) / 2 at hxa
    linarith only [hxa, hsm, hr, hρ₂]
  intro i
  have hi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  exact abs_lt.mp (by linarith only [hi, hn])

theorem layer_interval_subset {n : ℕ} {ρ₁ ρ₂ τ h : ℝ} (hd : 3 ≤ n + 1)
    (hτ : τ ∈ selectionInterval ρ₁ ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - ρ₁) / (200 * ((n + 1 : ℕ) : ℝ)))
    {j : ℕ} (hl : 6 * (3 : ℝ) ^ (-(j : ℝ)) < h) :
    Ioo τ (τ + 54 * (3 : ℝ) ^ (-(j : ℝ))) ⊆ Ioo ρ₁ ρ₂ := by
  have hr := layer_radius_facts hd hτ hh hwidth
  intro x hx
  constructor
  · linarith only [hτ.1, hτ.2, hx.1]
  · linarith only [hx.2, hl, hr]

/-- Step 1: the energy of `v` on the layer `W_h^j` is at most `54 · 3^{-j} D_v(τ)`. -/
theorem layer_energy_le {n : ℕ} [NeZero (n + 1)] {a : CoeffField (n + 1)}
    (ha : IsWeightedCoeffOn (originCube 1) a)
    {ρ₁ ρ₂ τ h : ℝ} (hd : 3 ≤ n + 1) (hρ₁ : 1 / 2 ≤ ρ₁) (hρ₂ : ρ₂ ≤ 1)
    (hτ : τ ∈ selectionInterval ρ₁ ρ₂) (hτ0 : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    (hh : 0 < h) (hwidth : h ≤ (ρ₂ - ρ₁) / (200 * ((n + 1 : ℕ) : ℝ)))
    {v : Vec (n + 1) → ℝ} {G : Vec (n + 1) → Vec (n + 1)}
    (hv : MemH1a a (originCube 1) v G) (j : ℕ) :
    ∑' cell : whitneySimplicesNearSize (d := n + 1) τ h j,
        weightedEnergy a (exteriorCellSet cell.1) G ≤
      ENNReal.ofReal (54 * (3 : ℝ) ^ (-(j : ℝ))) *
        surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ := by
  classical
  by_cases hD : surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ = ⊤
  · rw [hD, ENNReal.mul_top (by simp)]
    exact le_top
  by_cases hemp : IsEmpty (whitneySimplicesNearSize (d := n + 1) τ h j)
  · simp
  rw [not_isEmpty_iff] at hemp
  obtain ⟨c₀⟩ := hemp
  have hl := layer_small hτ0 hτ1 c₀.2
  have hinterval := layer_interval_subset hd hτ hh hwidth hl
  have hUV : ∀ k : whitneySimplicesNearSize (d := n + 1) τ h j,
      exteriorCellSet k.1 ⊆ originCube 1 := fun k =>
    layer_cell_subset hd hρ₂ hτ hh hwidth hτ0 hτ1 k.2
  have hEwhole : weightedEnergy a (originCube 1) G < ⊤ :=
    Weighted.MemH1a.energy_lt_top
      (Whitney.source_cube_domain (d := n + 1) (by norm_num : (0 : ℝ) < 1)).isOpen ha hv
  have hEm := (Weighted.quadratic_aestronglyMeasurable ha hv.2.1).aemeasurable.ennreal_ofReal
  let density := hEm.mk (fun x =>
    ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x))))
  have hDensity : Measurable density := hEm.measurable_mk
  have hdensity : density =ᵐ[volume.restrict (originCube 1)]
      (fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))) :=
    hEm.ae_eq_mk.symm
  set Dr : ℝ := (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).toReal with hDr
  have hDrE : ENNReal.ofReal Dr = surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ :=
    ENNReal.ofReal_toReal hD
  have hmax' : Selection.surfaceEnergyMaximal ρ₁ ρ₂ density τ ≤ ENNReal.ofReal Dr := by
    have hρ0 : 0 ≤ ρ₁ := by linarith only [hρ₁]
    have hAnn : Selection.cubicalAnnulus (n + 1) ρ₁ ρ₂ ⊆ originCube 1 := by
      intro x hx i
      have hi : |x i| ≤ ‖x‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
      exact abs_lt.mp (by linarith only [hi, hx.2, hρ₂])
    have hge := ae_restrict_of_ae_restrict_of_subset hAnn hdensity
    rw [Selection.source_surfaceEnergyMaximal_congr_ae hρ0 hge,
      Harnack.WeakHarnack.sourceSurfaceEnergyMaximal_eq_statement ρ₁ ρ₂ a ha G τ, hDrE]
  have hτnn : 0 ≤ τ := by linarith only [hτ0]
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  have hfin : ∀ k : whitneySimplicesNearSize (d := n + 1) τ h j,
      weightedEnergy a (exteriorCellSet k.1) G ≠ ⊤ := by
    intro k
    exact ((lintegral_mono_set (hUV k)).trans_lt hEwhole).ne
  have hreal := Harnack.Pairing.exterior_subsolution_layer_of_collar
    (V := originCube 1) (a := a) (fun k : whitneySimplicesNearSize (d := n + 1) τ h j =>
      exteriorCellSet k.1) S (fun k _ => cell_measurable k.1)
    (by
      intro k hk b hb hkb
      exact cell_disjoint hτ0 hτ1 (fun he => hkb (Subtype.ext he)))
    hUV hτnn ENNReal.toReal_nonneg j hinterval
    (fun k _ => layer_collar hτ0 hτ1 k.2) density hDensity hmax' hEwhole hdensity
  calc ∑ k ∈ S, weightedEnergy a (exteriorCellSet k.1) G
      = ENNReal.ofReal (∑ k ∈ S, (weightedEnergy a (exteriorCellSet k.1) G).toReal) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => ENNReal.toReal_nonneg)]
        exact Finset.sum_congr rfl (fun k _ => (ENNReal.ofReal_toReal (hfin k)).symm)
    _ ≤ ENNReal.ofReal (54 * (3 : ℝ) ^ (-(j : ℝ)) * Dr) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), hDrE]

end

end CoarseDeGiorgi.ExteriorIntegral.WideWidth
