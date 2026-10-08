module

public import CoarseDeGiorgi.Localization.SummedTendsto

/-! # Convergence of localized functions in the fractional norm -/

@[expose] public section

namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Foundations
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem summed_localization_converge (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t) (hθ : 0 < paramTheta d p q s t)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hrange : spatialMomentRange a ha p q s t)
    {δ R : ℝ} {m : ℤ} {K : Set (Vec d)}
    (hδ : 0 < δ) (hs1 : gridSpacing m ≤ 1) (hgap : δ / 192 < gridSpacing m)
    (hcover : LocalizationCover m K R δ) (hR : R ≤ 1)
    (u : ℕ → Vec d → ℝ) (H : ℕ → Vec d → Vec d)
    (hu : ∀ j, MemH1a a (originCube 1) (u j) (H j)) (hum : ∀ j, Measurable (u j))
    (hto : Tendsto (fun j => h1aWeightedNorm a (originCube 1) (u j) (H j)) atTop (𝓝 0)) :
    Tendsto (fun j => fracNorm Set.univ (alphaParam t) (paramR q)
      (localizedFunction m (coverIndices m K) (u j))) atTop (𝓝 0) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hα, hα1, hr, hr2, -⟩ := Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  obtain ⟨C₁, hC₁fin, -, hsum⟩ := exists_localization_sum_gap_constant (d := d) hα hα1 hr
  set r := paramR q with hrdef
  set α := alphaParam t with hαdef
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hunit := unitCube_domain (d := d)
  have hsubR : radiusCube (d := d) R ⊆ originCube 1 := by
    rw [radiusCube_eq_originCube]; exact originCube_mono hR
  set Z := coverIndices m K with hZ
  have hQ (z : Fin d → ℤ) (hz : z ∈ Z) : closure (auxCube m z) ⊆ originCube 1 :=
    ((hcover.1 z hz).2).trans hsubR
  have hmem (j : ℕ) (z : Fin d → ℤ) (hz : z ∈ Z) : MemH1a a (auxCube m z) (u j) (H j) :=
    LowerFractional.memH1a_restrict hunit.1 hunit.2 ha
      (LowerFractional.auxCube_isOpenBoundedConvexDomain _ z)
      (subset_closure.trans (hQ z hz)) (hu j)
  -- per cube: the local fractional norm is controlled by the local weighted norm
  have hcube (z : Fin d → ℤ) (hz : z ∈ Z) : ∃ Cz : ℝ≥0∞, Cz < ⊤ ∧ ∀ j,
      fracNorm (auxCube m z) α r (u j) ≤ Cz * h1aWeightedNorm a (auxCube m z) (u j) (H j) := by
    obtain ⟨Cz, hCz, hbd⟩ := lower_fractional_embedding hd p q s t a ha hrange m z (subset_closure.trans (hQ z hz))
    exact ⟨Cz, hCz, fun j => hbd _ _ (hmem j z hz)⟩
  have hloc0 (z : Fin d → ℤ) (hz : z ∈ Z) :
      Tendsto (fun j => fracNorm (auxCube m z) α r (u j)) atTop (𝓝 0) := by
    obtain ⟨Cz, hCz, hbd⟩ := hcube z hz
    have h0 := h1aWeightedNorm_cube_tendsto a ha (Q := auxCube m z)
      (subset_closure.trans (hQ z hz)) u H hu hto
    have h1 : Tendsto (fun j => Cz * h1aWeightedNorm a (auxCube m z) (u j) (H j)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hCz.ne)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le) hbd
  have hfin (j : ℕ) (z : Fin d → ℤ) (hz : z ∈ Z) : fracNorm (auxCube m z) α r (u j) < ⊤ := by
    obtain ⟨Cz, hCz, hbd⟩ := hcube z hz
    refine (hbd j).trans_lt (ENNReal.mul_lt_top hCz ?_)
    have henergy := Weighted.MemH1a.energy_lt_top hunit.1.isOpen ha (hu j)
    unfold h1aWeightedNorm
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.add_lt_top.mpr
      ⟨ENNReal.ofReal_lt_top, (lintegral_mono_set (subset_closure.trans (hQ z hz))).trans_lt henergy⟩).ne
  -- the sum of the r-th powers tends to zero
  have hpow : Tendsto (fun j => ∑ z ∈ Z, fracNorm (auxCube m z) α r (u j) ^ r) atTop (𝓝 0) := by
    have : (0 : ℝ≥0∞) = ∑ z ∈ Z, (0 : ℝ≥0∞) ^ r := by simp [ENNReal.zero_rpow_of_pos hr0]
    rw [this]
    refine tendsto_finsetSum _ fun z hz => ?_
    exact ((ENNReal.continuous_rpow_const (y := r)).tendsto 0).comp (hloc0 z hz)
  -- the bound
  set D : ℝ≥0∞ := C₁ + C₁ * ENNReal.ofReal (δ ^ (-α * r)) with hD
  have hb : ∀ j, fracNorm univ α r (localizedFunction m Z (u j)) ^ r ≤
      D * ∑ z ∈ Z, fracNorm (auxCube m z) α r (u j) ^ r := by
    intro j
    refine (hsum δ hδ m hs1 hgap Z (u j) (hum j) (hfin j)).trans ?_
    calc _ ≤ C₁ * ∑ z ∈ Z, fracNorm (auxCube m z) α r (u j) ^ r +
          C₁ * ENNReal.ofReal (δ ^ (-α * r)) * ∑ z ∈ Z, fracNorm (auxCube m z) α r (u j) ^ r :=
          add_le_add (by gcongr with z hz; exact FracGeometry.fracSeminorm_le_fracNorm _ α hr0 _)
            (by gcongr with z hz; exact FracGeometry.eLpNorm_le_fracNorm _ α hr0 _)
      _ = _ := by rw [hD, add_mul]
  have hDfin : D ≠ ⊤ := by
    rw [hD]; exact ENNReal.add_ne_top.mpr ⟨hC₁fin, ENNReal.mul_ne_top hC₁fin ENNReal.ofReal_ne_top⟩
  have hlim : Tendsto (fun j => D * ∑ z ∈ Z, fracNorm (auxCube m z) α r (u j) ^ r) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hpow (Or.inr hDfin)
  have hlim2 : Tendsto (fun j => fracNorm univ α r (localizedFunction m Z (u j)) ^ r) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hb
  have h3 := (ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0 |>.comp hlim2
  simp only [Function.comp_def, ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one,
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr hr0)] at h3
  exact h3

end
end CoarseDeGiorgi.Localization
