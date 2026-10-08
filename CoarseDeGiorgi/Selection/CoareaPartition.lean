import CoarseDeGiorgi.Selection.Coarea

namespace CoarseDeGiorgi.Selection

open Homogenization MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

variable {n : ℕ}

/-- Two different coordinates have different absolute values off a volume-null set. -/
theorem ae_abs_coordinate_ne (i j : Fin (n + 1)) (hji : j ≠ i) :
    ∀ᵐ x : Vec (n + 1), |x i| ≠ |x j| := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
  have hscalar (l : ℝ) : ∀ᵐ t : ℝ, |l| ≠ |t| := by
    have h₁ : ∀ᵐ t : ℝ, t ≠ l := by simp [ae_iff]
    have h₂ : ∀ᵐ t : ℝ, t ≠ -l := by simp [ae_iff]
    filter_upwards [h₁, h₂] with t ht₁ ht₂
    intro he
    rcases abs_eq_abs.mp he with h | h
    · exact ht₁ h.symm
    · exact ht₂ (by linarith)
  have hu (l : ℝ) : ∀ᵐ u : Vec n, |l| ≠ |u k| :=
    Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => (volume : Measure ℝ)) (hscalar l)
  have hp : ∀ᵐ p : ℝ × Vec n ∂volume.prod volume, |p.1| ≠ |p.2 k| :=
    (Measure.ae_prod_iff_ae_ae (by exact (measurableSet_eq_fun
      (by fun_prop) (by fun_prop)).compl)).2
      (ae_of_all _ hu)
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).quasiMeasurePreserving.ae hp

/-- All coordinate ties may be discarded simultaneously. -/
theorem ae_distinct_abs_coordinates :
    ∀ᵐ x : Vec (n + 1), ∀ i j, j ≠ i → |x i| ≠ |x j| := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hji : j = i
  · exact ae_of_all _ (by simp [hji])
  · exact (ae_abs_coordinate_ne i j hji).mono (fun _ hx _ => hx)

/-- The annulus is the strict sup-norm shell. -/
def cubicalAnnulus (d : ℕ) (ρ R : ℝ) : Set (Vec d) :=
  {x | ρ / 2 < ‖x‖ ∧ ‖x‖ < R / 2}

theorem measurableSet_cubicalAnnulus (d : ℕ) (ρ R : ℝ) :
    MeasurableSet (cubicalAnnulus d ρ R) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

/-- A point in an oriented sector has that coordinate as its sup norm. -/
theorem faceSector_norm {ρ R : ℝ} (hρ : 0 ≤ ρ) {i : Fin (n + 1)} {pos : Bool}
    {x : Vec (n + 1)} (hx : x ∈ faceSector ρ R i pos) :
    ‖x‖ = faceRadius i pos x / 2 := by
  have hrad : 0 < faceRadius i pos x := hρ.trans_lt hx.1.1
  have hi : |x i| = faceRadius i pos x / 2 := by
    cases pos <;> simp only [faceRadius, Bool.false_eq_true, ite_false, ite_true] at *
    · rw [abs_of_neg (by linarith)]; ring
    · rw [abs_of_pos (by linarith)]; ring
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    by_cases hji : j = i
    · simpa [hji, Real.norm_eq_abs] using hi.le
    · have hj := hx.2 j hji
      have hj' : - (faceRadius i pos x / 2) < x j ∧ x j < faceRadius i pos x / 2 := by
        constructor <;> linarith [hj.1, hj.2]
      simpa only [Real.norm_eq_abs] using (abs_lt.mpr hj').le
  · rw [← hi]
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i

theorem faceSector_subset_annulus {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (i : Fin (n + 1)) (pos : Bool) :
    faceSector ρ R i pos ⊆ cubicalAnnulus (n + 1) ρ R := by
  intro x hx
  change ρ / 2 < ‖x‖ ∧ ‖x‖ < R / 2
  rw [faceSector_norm hρ hx]
  constructor <;> linarith [hx.1.1, hx.1.2]

/-- Every shell point without a coordinate tie belongs to one oriented sector. -/
theorem exists_faceSector_of_distinct {ρ R : ℝ} (hρ : 0 ≤ ρ)
    {x : Vec (n + 1)} (hx : x ∈ cubicalAnnulus (n + 1) ρ R)
    (hdistinct : ∀ i j, j ≠ i → |x i| ≠ |x j|) :
    ∃ i pos, x ∈ faceSector ρ R i pos := by
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm x).1
  have hi' : |x i| = ‖x‖ := by simpa only [Real.norm_eq_abs] using hi
  have hpos : 0 < |x i| := by rw [hi']; linarith [hx.1]
  have hother (j : Fin (n + 1)) (hji : j ≠ i) : |x j| < |x i| := by
    have hle : |x j| ≤ |x i| := by rw [hi']; exact norm_le_pi_norm x j
    exact lt_of_le_of_ne hle (hdistinct i j hji).symm
  by_cases hxi : 0 < x i
  · refine ⟨i, true, ?_⟩
    have hr : faceRadius i true x = 2 * ‖x‖ := by simp [faceRadius, ← hi', abs_of_pos hxi]
    refine ⟨?_, ?_⟩
    · rw [hr]; constructor <;> linarith [hx.1, hx.2]
    · intro j hji
      have hj := abs_lt.mp (hother j hji)
      simp only [faceRadius, ite_true]
      rw [abs_of_pos hxi] at hj
      constructor <;> linarith [hj.1, hj.2]

  · have hxi' : x i < 0 := by
      have := abs_pos.mp hpos
      exact lt_of_le_of_ne (le_of_not_gt hxi) this
    refine ⟨i, false, ?_⟩
    have hr : faceRadius i false x = 2 * ‖x‖ := by simp [faceRadius, ← hi', abs_of_neg hxi']
    refine ⟨?_, ?_⟩
    · rw [hr]; constructor <;> linarith [hx.1, hx.2]
    · intro j hji
      have hj := abs_lt.mp (hother j hji)
      simp only [faceRadius, Bool.false_eq_true, ite_false]
      rw [abs_of_neg hxi'] at hj
      constructor <;> linarith [hj.1, hj.2]


/-- Strict dominance makes the oriented sector unique. -/
theorem faceSector_unique {ρ R : ℝ} (hρ : 0 ≤ ρ)
    {x : Vec (n + 1)} {i j : Fin (n + 1)} {pos pos' : Bool}
    (hi : x ∈ faceSector ρ R i pos) (hj : x ∈ faceSector ρ R j pos') :
    i = j ∧ pos = pos' := by
  have hni := faceSector_norm hρ hi
  have hnj := faceSector_norm hρ hj
  have hcoord (k : Fin (n + 1)) (b : Bool) (h : x ∈ faceSector ρ R k b) :
      |x k| = ‖x‖ := by
    rw [faceSector_norm hρ h]
    have hr : 0 < faceRadius k b x := hρ.trans_lt h.1.1
    cases b <;> simp only [faceRadius, Bool.false_eq_true, ite_false, ite_true] at *
    · rw [abs_of_neg (by linarith)]; ring
    · rw [abs_of_pos (by linarith)]; ring
  have hij : i = j := by
    by_contra hne
    have h := hi.2 j (Ne.symm hne)
    have hlt : |x j| < faceRadius i pos x / 2 := abs_lt.mpr ⟨by linarith [h.1], h.2⟩
    rw [hcoord j pos' hj, ← hni] at hlt
    exact lt_irrefl _ hlt
  subst j
  refine ⟨rfl, ?_⟩
  by_contra hne
  have hri : 0 < faceRadius i pos x := hρ.trans_lt hi.1.1
  have hrj : 0 < faceRadius i pos' x := hρ.trans_lt hj.1.1
  cases pos <;> cases pos'
  all_goals simp only [faceRadius, Bool.false_eq_true, ite_false, ite_true] at hri hrj
  all_goals first | exact (hne rfl).elim | linarith

/-- The sector indicators partition the shell almost everywhere. -/
theorem annulus_indicator_eq_sum {ρ R : ℝ} (hρ : 0 ≤ ρ)
    (g : Vec (n + 1) → ℝ≥0∞) :
    (cubicalAnnulus (n + 1) ρ R).indicator g =ᵐ[volume]
      fun x => ∑ i : Fin (n + 1), ∑ pos : Bool, (faceSector ρ R i pos).indicator g x := by
  classical
  filter_upwards [ae_distinct_abs_coordinates (n := n)] with x hx
  by_cases ha : x ∈ cubicalAnnulus (n + 1) ρ R
  · obtain ⟨i, pos, hmem⟩ := exists_faceSector_of_distinct hρ ha hx
    rw [indicator_of_mem ha, Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single pos, indicator_of_mem hmem]
      · intro b _ hb
        exact indicator_of_notMem (fun h => hb ((faceSector_unique hρ h hmem).2)) g
      · simp
    · intro j _ hj
      apply Finset.sum_eq_zero
      intro b _
      exact indicator_of_notMem (fun h => hj ((faceSector_unique hρ h hmem).1)) g
    · simp
  · rw [indicator_of_notMem ha]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro pos _
    exact indicator_of_notMem (fun h => ha (faceSector_subset_annulus hρ i pos h)) g

/-- Cubical coarea for the summed-face surface measure (`e.cubical.coarea`).
The source annulus is `ball 0 (R/2) \ closedBall 0 (ρ/2)` in the sup norm. -/
theorem cubical_coarea {ρ R : ℝ} (hρ : 0 ≤ ρ)
    {g : Vec (n + 1) → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ τ in Ioo ρ R, ∫⁻ x, g x ∂CoarseDeGiorgi.surfaceMeasure τ) =
      2 * ∫⁻ x in cubicalAnnulus (n + 1) ρ R, g x := by
  classical
  rw [← lintegral_indicator (measurableSet_cubicalAnnulus (n + 1) ρ R) g,
    lintegral_congr_ae (annulus_indicator_eq_sum hρ g)]
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _
    (fun pos _ => hg.indicator (measurableSet_faceSector ρ R i pos)))]
  simp_rw [lintegral_finsetSum _ (fun pos _ => hg.indicator (measurableSet_faceSector ρ R _ pos)),
    lintegral_indicator (measurableSet_faceSector ρ R _ _)]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum, ← cubical_coarea_face ρ R _ _ hg]
  -- The variable-face measurability needed to exchange the finite sum is proved below.
  unfold CoarseDeGiorgi.surfaceMeasure
  simp_rw [lintegral_finsetSum_measure]
  symm
  rw [lintegral_finsetSum]
  · congr 1
    funext i
    rw [lintegral_finsetSum]
    intro pos _
    exact measurable_cubeFaceIntegral i pos hg
  · intro i _
    exact Finset.measurable_sum _ (fun pos _ => measurable_cubeFaceIntegral i pos hg)


end

end CoarseDeGiorgi.Selection
