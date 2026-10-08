import CoarseDeGiorgi.Weighted.PairOperations

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The literal energy of the zero field is zero. -/
theorem weightedEnergy_zero : weightedEnergy a V (0 : Vec d → Vec d) = 0 := by
  simp [weightedEnergy, CoarseDeGiorgi.weightedEnergy, vecDot, matVecMul]

/-- A full weighted pair with zero mean and zero energy is zero almost everywhere. -/
theorem MemH1a.eq_zero_of_mean_energy_zero [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a a V u G)
    (hm : volumeAverage V u = 0) (hE : weightedEnergy a V G = 0) :
    u =ᵐ[volume.restrict V] 0 ∧ G =ᵐ[volume.restrict V] 0 := by
  have hw := memH1a_memW11 hV hne ha hu
  obtain ⟨C, hC, hp⟩ := Foundations.exists_mean_zero_poincare_w11 hV hne
  have hl := gradient_length_integrable_and_bound ha hu.2.1 hw.2.2.2.2
  have hlen : (∫ x in V, Real.sqrt (vecDot (G x) (G x))) ≤ 0 := by
    simpa only [hE, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero] using hl.2
  have habs : (∫ x in V, |u x|) ≤ 0 := by
    have hh := hp u G hw.1 hw.2.1 hw.2.2.1
    rw [hm] at hh
    simp only [sub_zero] at hh
    exact hh.trans (by simpa only [mul_zero] using mul_le_mul_of_nonneg_left hlen hC)
  have haeu : u =ᵐ[volume.restrict V] 0 := by
    have hi : IntegrableOn (fun x => |u x|) V := hw.1.abs
    have hz : (∫ x in V, |u x|) = 0 :=
      le_antisymm habs (integral_nonneg fun x => abs_nonneg (u x))
    have hh := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg (u x)) hi).mp hz
    filter_upwards [hh] with x hx
    exact abs_eq_zero.mp hx
  let F := memH1aEnergyField hV.isOpen ha hu
  have hn : ‖F‖ = 0 := by
    apply eq_zero_of_pow_eq_zero (n := 2)
    rw [GradientCore.norm_sq ha, memH1aEnergyField_field, hE, ENNReal.toReal_zero]
  have hz : (F : GradientHilbert ha) = ((0 : GradientCore ha) : GradientHilbert ha) := by
    rw [UniformSpace.Completion.coe_zero]
    exact norm_eq_zero.mp (by rw [UniformSpace.Completion.norm_coe, hn])
  have hG := (GradientCore.coe_eq_iff ha F 0).mp hz
  exact ⟨haeu, hG⟩

/-- Zero-boundary energy is definite on measurable pairs modulo a.e. equality. -/
theorem MemH1a0.eq_zero_of_energy_zero [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a0 a V u G)
    (hE : weightedEnergy a V G = 0) :
    u =ᵐ[volume.restrict V] 0 ∧ G =ᵐ[volume.restrict V] 0 := by
  obtain ⟨C, _, hb⟩ := exists_memH1a0_coercivity hV hne
  have hh := (hb a ha u G hu).2.2.1
  rw [hE, ENNReal.toReal_zero, Real.sqrt_zero, mul_zero] at hh
  have hm : volumeAverage V u = 0 := abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  exact (hu.memH1a ha).eq_zero_of_mean_energy_zero hV hne ha hm hE





end CoarseDeGiorgi.Weighted
