module

public import CoarseDeGiorgi.Whitney.Extension.EnergyOverlap
public import CoarseDeGiorgi.Statements.WhitneySimplicesNearSize
public import CoarseDeGiorgi.Statements.SmoothGrad

/-!
# Summing the energy over the simplices of size `3^{-j}`
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

/-- The cubes of scale `1 - j` that are near the reference cube. -/
def nearLevel (τ h : ℝ) (j : ℕ) (d : ℕ) : Set {D : TriadicCube d // D ∈ whitneyCubes (d := d) τ} :=
  {D | D.1.scale = 1 - (j : ℤ) ∧
    infSupDist (closedTriadicCube D.1) (closedReferenceCube (d := d) τ) < h}

theorem sum_energy_le (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (hh : 0 < h)
    (hh1 : h ≤ 1) {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) {α ξ b : ℝ}
    (hα : 0 < α) (hξ : 1 ≤ ξ) (hξ2 : ξ ≤ 2) (hb : 1 ≤ b) (hb2 : b ≤ 2) (j : ℕ) :
    ∑' cell : whitneySimplicesNearSize (d := d) τ h j,
        ∫⁻ x in exteriorCellSet cell.1,
          ENNReal.ofReal (vecNormSq (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)) ≤
      (Fintype.card ((Fin d → Fin 3) × Equiv.Perm (Fin d)) : ℝ≥0∞) *
        (ENNReal.ofReal (Ra d b ((3 : ℝ) ^ ((1 : ℤ) - (j : ℤ))) h) *
            ((overlapN d : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (|f x| ^ b) ∂surfaceMeasure τ) ^ (2 / b) +
          ENNReal.ofReal (Rb d α ξ ((3 : ℝ) ^ ((1 : ℤ) - (j : ℤ)))) *
            ((overlapN d : ℝ≥0∞) *
              ∫⁻ p, fracKernelWithDimension ((d : ℝ) - 1) α ξ f p
                ∂((surfaceMeasure τ).prod (surfaceMeasure τ))) ^ (2 / ξ)) := by
  classical
  set P : Set {D : TriadicCube d // D ∈ whitneyCubes (d := d) τ} := nearLevel τ h j d with hPdef
  set ℓ : ℝ := (3 : ℝ) ^ ((1 : ℤ) - (j : ℤ)) with hℓ
  have hb0 : 0 < b := by linarith only [hb]
  have hξ0 : 0 < ξ := by linarith only [hξ]
  -- the per-cube bound
  let Φ : {D : TriadicCube d // D ∈ whitneyCubes (d := d) τ} → ℝ≥0∞ := fun D =>
    ENNReal.ofReal (Ra d b ℓ h) * locMass τ f b D.1 ^ (2 / b) +
      ENNReal.ofReal (Rb d α ξ ℓ) * locFrac τ α ξ f D.1 ^ (2 / ξ)
  have hcube : ∀ D : {D : TriadicCube d // D ∈ whitneyCubes (d := d) τ}, D ∈ P →
      cubeScaleFactor D.1 = ℓ := by
    intro D hDP
    have := hDP.1
    unfold cubeScaleFactor
    rw [this, hℓ]
  have hcell : ∀ cell : whitneySimplicesNearSize (d := d) τ h j,
      ∫⁻ x in exteriorCellSet cell.1,
        ENNReal.ofReal (vecNormSq (smoothGrad (whitneyAffineExtension τ h f hτ0 hτ1) x)) ≤
        Φ cell.1.1 := by
    intro cell
    have hmem : cell.1.1 ∈ P := ⟨cell.2.2, cell.2.1⟩
    have := cell_energy_le hd hτ0 hτ1 hh hh1 cell.1.1.2 cell.2.1 hf hα hξ hb
      (cell := cell.1) rfl
    rw [hcube _ hmem] at this
    exact this
  have h1 := ENNReal.tsum_le_tsum hcell
  refine h1.trans ?_
  have h2 : ∑' cell : whitneySimplicesNearSize (d := d) τ h j, Φ cell.1.1 =
      ∑' cell : ExteriorCell d τ,
        (whitneySimplicesNearSize (d := d) τ h j).indicator (fun cell => Φ cell.1) cell :=
    tsum_subtype (whitneySimplicesNearSize (d := d) τ h j) (fun cell => Φ cell.1)
  have h3 : ∀ cell : ExteriorCell d τ,
      (whitneySimplicesNearSize (d := d) τ h j).indicator (fun cell => Φ cell.1) cell =
        P.indicator Φ cell.1 := by
    intro cell
    by_cases hc : cell ∈ whitneySimplicesNearSize (d := d) τ h j
    · have hc' : cell.1 ∈ P := ⟨hc.2, hc.1⟩
      rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc']
    · have hc' : cell.1 ∉ P := fun h' => hc ⟨h'.2, h'.1⟩
      rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc']
  have h4 : ∑' cell : ExteriorCell d τ, P.indicator Φ cell.1 =
      (Fintype.card ((Fin d → Fin 3) × Equiv.Perm (Fin d)) : ℝ≥0∞) *
        ∑' x : {D : TriadicCube d // D ∈ whitneyCubes (d := d) τ}, P.indicator Φ x := by
    change ∑' p : {D : TriadicCube d // D ∈ whitneyCubes (d := d) τ} ×
        ((Fin d → Fin 3) × Equiv.Perm (Fin d)), P.indicator Φ p.1 = _
    rw [ENNReal.tsum_prod (f := fun a _ => P.indicator Φ a)]
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [ENNReal.tsum_mul_left]
  rw [h2]
  simp only [h3]
  rw [h4, ← tsum_subtype P Φ]
  refine mul_le_mul_right ?_ _
  have hsc : ∀ i : P, (i.1.1).scale = 1 - (j : ℤ) := fun i => i.2.1
  have hinj : Function.Injective (fun i : P => (i.1.1 : TriadicCube d)) := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  have hovl : ∀ x : Vec d, ∀ T : Finset P, (∀ i ∈ T, x ∈ sigmaD τ i.1.1) → T.card ≤ overlapN d :=
    fun x T hT => sigmaD_overlap hd hτ0 hτ1 (fun i : P => i.1.1) (fun i => i.1.2) _ hsc hinj x T hT
  have hmass : ∑' i : P, locMass τ f b i.1.1 ≤
      (overlapN d : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (|f x| ^ b) ∂surfaceMeasure τ :=
    tsum_setLIntegral_le (surfaceMeasure τ) (fun i : P => sigmaD τ i.1.1)
      (fun i => measurableSet_sigmaD τ _) (overlapN d) hovl _
  have hfrac : ∑' i : P, locFrac τ α ξ f i.1.1 ≤
      (overlapN d : ℝ≥0∞) * ∫⁻ p, fracKernelWithDimension ((d : ℝ) - 1) α ξ f p
        ∂((surfaceMeasure τ).prod (surfaceMeasure τ)) :=
    tsum_setLIntegral_le ((surfaceMeasure τ).prod (surfaceMeasure τ))
      (fun i : P => sigmaD τ i.1.1 ×ˢ sigmaD τ i.1.1)
      (fun i => (measurableSet_sigmaD τ _).prod (measurableSet_sigmaD τ _)) (overlapN d)
      (fun p T hT => hovl p.1 T (fun i hi => (hT i hi).1)) _
  have hA : ∑' i : P, locMass τ f b i.1.1 ^ (2 / b) ≤
      ((overlapN d : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (|f x| ^ b) ∂surfaceMeasure τ) ^ (2 / b) :=
    (tsum_rpow_le_rpow_tsum _ (by rw [le_div_iff₀ hb0]; linarith only [hb2])).trans
      (ENNReal.rpow_le_rpow hmass (by positivity))
  have hB : ∑' i : P, locFrac τ α ξ f i.1.1 ^ (2 / ξ) ≤
      ((overlapN d : ℝ≥0∞) * ∫⁻ p, fracKernelWithDimension ((d : ℝ) - 1) α ξ f p
        ∂((surfaceMeasure τ).prod (surfaceMeasure τ))) ^ (2 / ξ) :=
    (tsum_rpow_le_rpow_tsum _ (by rw [le_div_iff₀ hξ0]; linarith only [hξ2])).trans
      (ENNReal.rpow_le_rpow hfrac (by positivity))
  calc ∑' i : P, Φ i.1 = ENNReal.ofReal (Ra d b ℓ h) * ∑' i : P, locMass τ f b i.1.1 ^ (2 / b) +
        ENNReal.ofReal (Rb d α ξ ℓ) * ∑' i : P, locFrac τ α ξ f i.1.1 ^ (2 / ξ) := by
        simp only [Φ]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    _ ≤ _ := by gcongr

end

end CoarseDeGiorgi.WhitneyExt
