import CoarseDeGiorgi.Localization.SummedFamily

/-! # Bound and convergence for the chosen covers -/
namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem h1aWeightedNorm_congr_ae {a : CoeffField d} {Q : Set (Vec d)} {w w' : Vec d → ℝ}
    (G : Vec d → Vec d) (h : w =ᵐ[volume.restrict Q] w') :
    h1aWeightedNorm a Q w G = h1aWeightedNorm a Q w' G := by
  unfold h1aWeightedNorm volumeAverage
  rw [integral_congr_ae h]

theorem one_le_level {m : ℤ} {δ : ℝ} (hδ : δ ≤ 1) (h : gridSpacing m ≤ δ / 64) : 1 ≤ m := by
  by_contra hm
  have h1 : (1 : ℝ) ≤ gridSpacing m := by
    unfold gridSpacing
    exact one_le_zpow₀ (by norm_num) (by omega)
  linarith

theorem chosen_family (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t) (hθ : 0 < paramTheta d p q s t)
    (Kf : ℝ → ℝ → Set (Vec d))
    (hKf : ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 → ∃ m, GoodLevel (Kf ρ₁ ρ₂) ρ₁ ρ₂ m) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
          ∀ (v : Vec d → ℝ) (G : Vec d → Vec d), MemH1a a (originCube 1) v G →
            fracNorm Set.univ (alphaParam t) (paramR q)
                (fun x => ∑ i ∈ chosenS Kf ρ₁ ρ₂, chosenPhi Kf ρ₁ ρ₂ i x * v x) ≤
              C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-alphaParam t) *
                ((lowerMoment a ha t q ht (le_of_lt hq)).rpow (-(1 / 2)) *
                    (weightedEnergy a (originCube ρ₂) G).rpow (1 / 2) +
                  eLpNorm v (ENNReal.ofReal (paramR q)) (volume.restrict (originCube ρ₂))) ∧
            ∀ (vⱼ : ℕ → Vec d → ℝ) (Gⱼ : ℕ → Vec d → Vec d),
              (∀ j, MemH1a a (originCube 1) (vⱼ j) (Gⱼ j)) →
              Tendsto (fun j => h1aWeightedNorm a (originCube 1)
                (fun x => vⱼ j x - v x) (fun x => Gⱼ j x - G x)) atTop (𝓝 0) →
              Tendsto (fun j => fracNorm Set.univ (alphaParam t) (paramR q)
                (fun x => (∑ i ∈ chosenS Kf ρ₁ ρ₂, chosenPhi Kf ρ₁ ρ₂ i x * vⱼ j x) -
                  ∑ i ∈ chosenS Kf ρ₁ ρ₂, chosenPhi Kf ρ₁ ρ₂ i x * v x)) atTop (𝓝 0) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCfin, hCprop⟩ := summed_localization_bound hd hp hq hs ht hθ
  refine ⟨C, hCfin, ?_⟩
  intro a ha hrange ρ₁ ρ₂ h1 h12 h2
  obtain ⟨⟨hlo, hhi, hcover, b, hb, hbm⟩, hZ⟩ := chosen_spec (hKf ρ₁ ρ₂ h1 h12 h2)
  set m := chosenLevel Kf ρ₁ ρ₂ with hmdef
  set K := Kf ρ₁ ρ₂ with hKdef
  have hδ : 0 < ρ₂ - ρ₁ := sub_pos.mpr h12
  have hδ1 : ρ₂ - ρ₁ ≤ 1 := by linarith
  have hm1 : 1 ≤ m := one_le_level hδ1 hhi
  have hs1 : gridSpacing m ≤ 1 := by linarith
  have hunit := unitCube_domain (d := d)
  have hsubR : originCube (d := d) ρ₂ ⊆ originCube 1 := originCube_mono h2
  have hZsub : ∀ z ∈ coverIndices m K, auxCube m z ⊆ originCube 1 := fun z hz =>
    subset_closure.trans (((hcover.1 z hz).2).trans (by
      rw [radiusCube_eq_originCube]; exact hsubR))
  have hFeq (w : Vec d → ℝ) :
      (fun x => ∑ i ∈ chosenS Kf ρ₁ ρ₂, chosenPhi Kf ρ₁ ρ₂ i x * w x) =
        localizedFunction m (coverIndices m K) w := by
    funext x
    rw [sum_chosenS, hZ]
  intro v G hv
  refine ⟨?_, ?_⟩
  · have hae := hv.1.ae_eq_mk
    have hvm : MemH1a a (originCube 1) (hv.1.mk v) G :=
      Weighted.MemH1a.congr_ae hv hae EventuallyEq.rfl
    have hbd := hCprop a ha hrange (ρ₂ - ρ₁) ρ₂ b m K hδ hδ1 h2 hm1 hs1 hlo hcover hb hbm
      (hv.1.mk v) G hvm hv.1.stronglyMeasurable_mk.measurable
    rw [hFeq]
    have hcongr : fracNorm Set.univ (alphaParam t) (paramR q)
        (localizedFunction m (coverIndices m K) v) =
        fracNorm Set.univ (alphaParam t) (paramR q)
          (localizedFunction m (coverIndices m K) (hv.1.mk v)) := by
      refine fracNorm_congr_ae ?_
      rw [Measure.restrict_univ]
      exact localizedFunction_ae_eq hZsub hae
    rw [hcongr]
    refine hbd.trans (le_of_eq ?_)
    have hL : eLpNorm (hv.1.mk v) (ENNReal.ofReal (paramR q)) (volume.restrict (originCube ρ₂)) =
        eLpNorm v (ENNReal.ofReal (paramR q)) (volume.restrict (originCube ρ₂)) :=
      eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset hsubR hae.symm)
    rw [hL, ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos hδ]
    simp only [ENNReal.rpow_eq_pow]
  · intro vⱼ Gⱼ hvj hto
    have hdiff (j : ℕ) : MemH1a a (originCube 1) (vⱼ j - v) (Gⱼ j - G) :=
      Weighted.MemH1a.sub hunit.1 hunit.2 ha (hvj j) hv
    set u : ℕ → Vec d → ℝ := fun j => (hdiff j).1.mk (vⱼ j - v) with hu
    have hae (j : ℕ) : (vⱼ j - v) =ᵐ[volume.restrict (originCube 1)] u j := (hdiff j).1.ae_eq_mk
    have hum (j : ℕ) : Measurable (u j) := (hdiff j).1.stronglyMeasurable_mk.measurable
    have hmem (j : ℕ) : MemH1a a (originCube 1) (u j) (Gⱼ j - G) :=
      Weighted.MemH1a.congr_ae (hdiff j) (hae j) EventuallyEq.rfl
    have hto' : Tendsto (fun j => h1aWeightedNorm a (originCube 1) (u j) (Gⱼ j - G)) atTop (𝓝 0) := by
      refine hto.congr fun j => ?_
      exact (h1aWeightedNorm_congr_ae _ (hae j).symm).symm
    have hconv := summed_localization_converge hd hp hq hs ht hθ a ha hrange hδ hs1 hlo hcover h2
      u (fun j => Gⱼ j - G) hmem hum hto'
    refine hconv.congr fun j => ?_
    have hpt : (fun x => (∑ i ∈ chosenS Kf ρ₁ ρ₂, chosenPhi Kf ρ₁ ρ₂ i x * vⱼ j x) -
        ∑ i ∈ chosenS Kf ρ₁ ρ₂, chosenPhi Kf ρ₁ ρ₂ i x * v x) =
        localizedFunction m (coverIndices m K) (vⱼ j - v) := by
      funext x
      rw [sum_chosenS, sum_chosenS, hZ]
      unfold localizedFunction
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [Pi.sub_apply, mul_sub]
      rfl
    rw [hpt]
    refine (fracNorm_congr_ae ?_).symm
    rw [Measure.restrict_univ]
    exact localizedFunction_ae_eq hZsub (hae j)

end
end CoarseDeGiorgi.Localization
