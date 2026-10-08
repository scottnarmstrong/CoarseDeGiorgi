module

public import CoarseDeGiorgi.Assembly.EnergyToSupQuantity

@[expose] public section

namespace CoarseDeGiorgi.Assembly
open Homogenization MeasureTheory Aliases
open scoped ENNReal

/-- Every compact subset of the unit cube lies in a strictly smaller cube. -/
theorem energy_to_sup_compact_cube {d : ℕ} {K : Set (Vec d)}
    (hK : IsCompact K) (hKV : K ⊆ originCube 1) :
    ∃ ρ : ℝ, (1 / 2 : ℝ) ≤ ρ ∧ ρ < 1 ∧ K ⊆ originCube ρ := by
  by_cases hKe : K.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKe continuous_norm.continuousOn
    have hxnorm : ‖x‖ < (1 / 2 : ℝ) := (pi_norm_lt_iff (by norm_num)).mpr (fun i => by
      rw [Real.norm_eq_abs, abs_lt]
      exact hKV hx i)
    let ρ := max (1 / 2 : ℝ) (‖x‖ + 1 / 2)
    refine ⟨ρ, le_max_left _ _, max_lt (by norm_num) (by linarith), ?_⟩
    intro y hy i
    have hiy : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i
    have hi : |y i| ≤ ‖x‖ := hiy.trans (hmax hy)
    have hx0 := norm_nonneg x
    have hρ : ‖x‖ + 1 / 2 ≤ ρ := le_max_right _ _
    obtain ⟨hlo, hhi⟩ := abs_le.mp hi
    constructor <;> linarith only [hlo, hhi, hx0, hxnorm, hρ]
  · refine ⟨1 / 2, le_rfl, by norm_num, ?_⟩
    intro x hx
    exact False.elim (hKe ⟨x, hx⟩)

/-- Zero quantity at a nonnegative level gives the essential bound. -/
theorem energy_to_sup_zero_bound {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (q t : ℝ) (ht : 0 < t) (hq : 1 ≤ q)
    (hr : 0 < paramR q) (u : Vec d → ℝ) (G : Vec d → Vec d) {L R : ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (originCube 1))) (hR : R ≤ 1)
    (hL : 0 ≤ L) (hzero : twoLevelQuantity a ha q t ht hq u G L R = 0) :
    eLpNorm (positivePart u) ⊤ (volume.restrict (originCube R)) ≤ ENNReal.ofReal L ∧
      ∀ᵐ x ∂(volume.restrict (originCube R)), u x ≤ L := by
  have hn : eLpNorm (fun x => max (u x - L) 0) (ENNReal.ofReal (paramR q))
      (volume.restrict (originCube R)) = 0 := by
    apply le_antisymm _ bot_le
    exact (energy_to_sup_norm_le_quantity a ha q t ht hq u G L R).trans_eq hzero
  have hz := (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hr).ne').mp hn
  have hbound : ∀ᵐ x ∂(volume.restrict (originCube R)), u x ≤ L := by
    filter_upwards [hz] with x hx
    have : u x - L ≤ 0 := (le_max_left _ _).trans_eq hx
    linarith only [this]
  refine ⟨?_, hbound⟩
  have hmeas := (continuous_id.max (continuous_const (y := (0 : ℝ)))).comp_aestronglyMeasurable
    (hu.mono_set (caccioppoli_cube_mono hR))
  rw [eLpNorm_exponent_top (show AEStronglyMeasurable (positivePart u) _ from hmeas)]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [hbound] with x hx
  change ‖max (u x) 0‖ ≤ L
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le hx hL

/-- Local Lʳ and weighted H¹ give finite zero-level data on an inner cube. -/
theorem energy_to_sup_initial_finite {d : ℕ} {a : CoeffField d}
    {ha : IsWeightedCoeffOn (originCube 1) a} {q t : ℝ} (ht : 0 < t) (hq : 1 ≤ q)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : IsWeightedSubsolution a (originCube 1) u G)
    (hlower : 0 < lowerMoment a ha t q ht hq) {R : ℝ} (hR : R ≤ 1)
    (hLr : MemLp u (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R))) :
    twoLevelQuantity a ha q t ht hq u G 0 R < ⊤ := by
  have hnorm : eLpNorm (fun x => max (u x - 0) 0) (ENNReal.ofReal (paramR q))
      (volume.restrict (originCube R)) < ⊤ := by
    apply lt_of_le_of_lt _ hLr.eLpNorm_lt_top
    simp only [sub_zero]
    apply eLpNorm_mono_ae ((continuous_id.max (continuous_const (y := (0 : ℝ)))).comp_aestronglyMeasurable (hu.1.1.mono_set (caccioppoli_cube_mono hR)))
    filter_upwards [] with x
    change ‖max (u x) 0‖ ≤ ‖u x‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right (u x) 0)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hE : weightedEnergy a (originCube R) (positiveTruncationGradient u G 0) < ⊤ := by
    apply lt_of_le_of_lt _ (caccioppoli_energy_finite ha hu hR)
    apply lintegral_mono
    intro x
    dsimp only [positiveTruncationGradient]
    by_cases hx : 0 < u x
    · simp only [hx, ite_true]
      exact le_rfl
    · simp [hx, vecDot, matVecMul]
  dsimp only [twoLevelQuantity]
  simp only [ENNReal.rpow_eq_pow, ENNReal.rpow_neg_one]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.add_ne_top.mpr ⟨(ENNReal.rpow_lt_top_of_nonneg (by norm_num) hnorm.ne).ne,
      ENNReal.mul_ne_top (ENNReal.inv_lt_top.mpr hlower).ne hE.ne⟩)

end CoarseDeGiorgi.Assembly
