module

public import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
public import CoarseDeGiorgi.Assembly.CaccioppoliParameters
public import CoarseDeGiorgi.Weighted.TestingTruncation
public import CoarseDeGiorgi.Weighted.TestingNorms
public import CoarseDeGiorgi.Foundations.Iteration.HoleFilling
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

namespace CoarseDeGiorgi.Assembly

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal
open Aliases

/-- The cancellation of contrast exponents in the proof of Theorem A. -/
theorem theoremA_exponent_identity (D A θ : ℝ) :
    (D - 1 - 2 * A) / (4 * θ) + A / (2 * θ) = (D - 1) / (4 * θ) := by
  by_cases hθ : θ = 0
  · simp only [hθ, mul_zero, div_zero, add_zero]
  · field_simp
    ring

/-- The zero-level value in the two-level quantity is exactly the positive part. -/
theorem theoremA_twoLevel_zero {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (q t : ℝ) (ht : 0 < t) (hq : 1 ≤ q)
    (u : Vec d → ℝ) (G : Vec d → Vec d) (R : ℝ) :
    twoLevelQuantity a ha q t ht hq u G 0 R =
      ((eLpNorm (positivePart u) (ENNReal.ofReal (paramR q))
        (volume.restrict (originCube R))).rpow 2 +
        (lowerMoment a ha t q ht hq)⁻¹ * weightedEnergy a (originCube R)
          ({x | 0 < u x}.indicator G)).rpow (1 / 2) := by
  have hg : positiveTruncationGradient u G 0 = {x | 0 < u x}.indicator G := by
    funext x
    by_cases hx : 0 < u x <;> simp only [positiveTruncationGradient,
      Set.indicator_apply, Set.mem_ofPred_eq, hx, ite_true, ite_false]
  have hr := ENNReal.rpow_neg_one (lowerMoment a ha t q ht hq)
  change ENNReal.rpow (lowerMoment a ha t q ht hq) (-1) = _ at hr
  dsimp only [twoLevelQuantity, positivePart]
  simp only [sub_zero, hg, hr]
  rfl

/-- The unit cube is a nonempty open bounded convex domain. -/
theorem theoremA_unitCube_domain (d : ℕ) :
    IsOpenBoundedConvexDomain (originCube (d := d) 1) ∧
      (Aliases.originCube (d := d) 1).Nonempty := by
  have he : CoarseDeGiorgi.originCube (d := d) 1 =
      openCubeSet (Homogenization.originCube d 0) := by
    ext x
    simp [CoarseDeGiorgi.originCube, openCubeSet, Homogenization.originCube, cubeScaleFactor]
  rw [he]
  refine ⟨isOpenBoundedConvexDomain_openCubeSet _, ?_⟩
  refine ⟨fun _ => 0, ?_⟩
  intro i
  norm_num

/-- The centered cubes have at most unit volume for radii at most one. -/
theorem theoremA_cube_volume_le_one {d : ℕ} {R : ℝ} (hR : R ≤ 1) :
    volume (originCube (d := d) R) ≤ 1 := by
  have he : CoarseDeGiorgi.originCube (d := d) 1 =
      Set.pi Set.univ (fun _ => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    ext x
    simp only [CoarseDeGiorgi.originCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ,
      Set.mem_Ioo, forall_const]
  have hvol : volume (originCube (d := d) 1) = 1 := by
    rw [he, volume_pi]
    norm_num
  exact (measure_mono (caccioppoli_cube_mono hR)).trans_eq hvol

/-- The source exponent r lies strictly between one and two. -/
theorem theoremA_paramR_range {q : ℝ} (hq : 1 < q) : 1 < paramR q ∧ paramR q < 2 := by
  have hden : 0 < q + 1 := by linarith only [hq]
  constructor
  · exact (lt_div_iff₀ hden).mpr (by linarith only [hq])
  · exact (div_lt_iff₀ hden).mpr (by linarith only [hq])

/-- The finite initial two-level quantity used between the two gates. -/
theorem theoremA_twoLevel_finite {d : ℕ} {a : CoeffField d}
    {ha : IsWeightedCoeffOn (originCube 1) a} {q t : ℝ} (ht : 0 < t) (hq : 1 ≤ q)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSubsolution a (originCube 1) u G)
    (hlower : 0 < lowerMoment a ha t q ht hq) {R : ℝ} (hR : R ≤ 1)
    (hLr : eLpNorm (positivePart u) (ENNReal.ofReal (paramR q))
      (volume.restrict (originCube R)) < ⊤) :
    twoLevelQuantity a ha q t ht hq u G 0 R < ⊤ := by
  have hsub := caccioppoli_cube_mono (d := d) hR
  have haR : IsWeightedCoeffOn (originCube R) a :=
    ⟨ha.1.mono_set hsub, ae_restrict_of_ae_restrict_of_subset hsub ha.2.1,
      ha.2.2.1.mono_set hsub, ha.2.2.2.mono_set hsub⟩
  have hE := (Weighted.energy_positivePart_le haR u G 0).trans_lt
    (caccioppoli_energy_finite ha hu hR)
  rw [theoremA_twoLevel_zero]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (ENNReal.add_ne_top.mpr ⟨(ENNReal.rpow_lt_top_of_nonneg (by norm_num) hLr.ne).ne,
      ENNReal.mul_ne_top (ENNReal.inv_lt_top.mpr hlower).ne hE.ne⟩)

/-- Essential local boundedness gives every finite inner-cube Lᵖ norm. -/
theorem theoremA_inner_norm_finite {d : ℕ} {u : Vec d → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (originCube 1)))
    (hlocal : LocallyBoundedAbove (originCube 1) u) {R : ℝ} (hR : R < 1)
    (p : ENNReal) : eLpNorm (positivePart u) p (volume.restrict (originCube R)) < ⊤ := by
  let K : Set (Vec d) := Set.pi Set.univ (fun _ => Set.Icc (-(R / 2)) (R / 2))
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hKV : K ⊆ originCube 1 := by
    intro x hx i
    have hxi : -(R / 2) ≤ x i ∧ x i ≤ R / 2 := hx i (Set.mem_univ _)
    constructor <;> linarith only [hxi.1, hxi.2, hR]
  have hinner : originCube R ⊆ K := by
    intro x hx i _
    exact ⟨(hx i).1.le, (hx i).2.le⟩
  obtain ⟨M, hM⟩ := hlocal K hK hKV
  have hpM : AEStronglyMeasurable (positivePart u) (volume.restrict (originCube R)) :=
    (continuous_id.max (continuous_const (y := (0 : ℝ)))).comp_aestronglyMeasurable
      (hu.mono_set (hinner.trans hKV))
  have htop : MemLp (positivePart u) ⊤ (volume.restrict (originCube R)) := by
    change eLpNorm (positivePart u) ⊤ (volume.restrict (originCube R)) < ⊤
    rw [eLpNorm_exponent_top hpM]
    apply eLpNormEssSup_lt_top_of_ae_bound (C := max M 0)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hinner hM] with x hx
    change ‖max (u x) 0‖ ≤ max M 0
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le_max hx le_rfl
  let : IsFiniteMeasure (volume.restrict (originCube R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (theoremA_cube_volume_le_one (d := d) hR.le).trans_lt (by simp : (1 : ENNReal) < ⊤)⟩
  exact (htop.mono_exponent le_top).eLpNorm_lt_top

/-- The subunit-volume comparison used to initialize the iteration. -/
theorem theoremA_lr_le_l2 {d : ℕ} {u : Vec d → ℝ} {q ρ R : ℝ}
    (hq : 1 < q) (hρR : ρ ≤ R) (hR : R ≤ 1)
    (hu : AEStronglyMeasurable (positivePart u) (volume.restrict (originCube ρ))) :
    eLpNorm (positivePart u) (ENNReal.ofReal (paramR q))
      (volume.restrict (originCube ρ)) ≤
      eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) := by
  have hr := theoremA_paramR_range hq
  have hpq : ENNReal.ofReal (paramR q) ≤ 2 := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hr.2.le
  have hexp : 0 ≤ 1 / (ENNReal.ofReal (paramR q)).toReal - 1 / (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofReal (by linarith only [hr.1])]
    norm_num only [ENNReal.toReal_ofNat]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith only [hr.1]) hr.2.le)
  have hvol : (volume.restrict (originCube (d := d) ρ)) Set.univ ≤ 1 := by
    rw [Measure.restrict_apply_univ]
    exact theoremA_cube_volume_le_one (hρR.trans hR)
  calc
    _ ≤ eLpNorm (positivePart u) 2 (volume.restrict (originCube ρ)) *
        ((volume.restrict (originCube ρ)) Set.univ) ^
          (1 / (ENNReal.ofReal (paramR q)).toReal - 1 / (2 : ENNReal).toReal) :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hu
    _ ≤ eLpNorm (positivePart u) 2 (volume.restrict (originCube ρ)) := by
      simpa only [mul_one] using
        mul_le_mul' (le_refl (eLpNorm (positivePart u) 2 (volume.restrict (originCube ρ))))
          (ENNReal.rpow_le_one hvol hexp)
    _ ≤ _ := eLpNorm_mono_measure _ (Measure.restrict_mono (caccioppoli_cube_mono hρR) le_rfl)

/-- Square-root bookkeeping for the finite initial quantity. -/
theorem theoremA_initial_bound {C D B N L E : ENNReal} {κ e : ℝ}
    (hD : D ≤ 1) (hB : 1 ≤ B) (hκ : 0 ≤ κ) (he : 0 ≤ e)
    (hL : L ≤ N) (hE : E ≤ C * D ^ (-κ) * B ^ e * N ^ (2 : ℝ)) :
    (L ^ (2 : ℝ) + E) ^ (1 / 2 : ℝ) ≤
      (1 + C) ^ (1 / 2 : ℝ) * D ^ (-κ / 2) * B ^ (e / 2) * N := by
  have hDpow : 1 ≤ D ^ (-κ) := by
    simpa only [ENNReal.rpow_zero] using
      (ENNReal.rpow_le_rpow_of_exponent_ge hD (neg_nonpos.mpr hκ))
  have hBpow : 1 ≤ B ^ e := by
    simpa only [ENNReal.rpow_zero] using
      (ENNReal.rpow_le_rpow_of_exponent_le hB he)
  have hL' : L ^ (2 : ℝ) ≤ D ^ (-κ) * B ^ e * N ^ (2 : ℝ) := by
    calc
      _ ≤ N ^ (2 : ℝ) := ENNReal.rpow_le_rpow hL (by norm_num)
      _ = 1 * 1 * N ^ (2 : ℝ) := by simp only [one_mul]
      _ ≤ _ := mul_le_mul' (mul_le_mul' hDpow hBpow) le_rfl
  have hsum : L ^ (2 : ℝ) + E ≤ (1 + C) * D ^ (-κ) * B ^ e * N ^ (2 : ℝ) := by
    calc
      _ ≤ D ^ (-κ) * B ^ e * N ^ (2 : ℝ) +
          C * D ^ (-κ) * B ^ e * N ^ (2 : ℝ) := add_le_add hL' hE
      _ = _ := by ring
  calc
    _ ≤ ((1 + C) * D ^ (-κ) * B ^ e * N ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hsum (by norm_num)
    _ = _ := by
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num),
        ← ENNReal.rpow_mul]
      norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
      rw [show -κ * (1 / 2) = -κ / 2 by ring,
        show e * (1 / 2) = e / 2 by ring]

/-- Composition of the two gates, retaining both parameter exponents exactly. -/
theorem theoremA_combine {M Y N C₁ C₂ B : ENNReal} {δ γ₄ κ D A θ : ℝ}
    (hδ : 0 < δ) (hB : 0 < B) (hBt : B ≠ ⊤)
    (hY : Y ≤ (1 + C₁) ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal (δ / 2)) ^ (-κ / 2) * B ^ (A / (2 * θ)) * N)
    (hM : M ≤ C₂ * (ENNReal.ofReal (δ / 2)) ^ (-γ₄) *
      B ^ ((D - 1 - 2 * A) / (4 * θ)) * Y) :
    M ≤ (C₂ * (1 + C₁) ^ (1 / 2 : ℝ) * (2 : ENNReal) ^ (γ₄ + κ / 2)) *
      (ENNReal.ofReal δ) ^ (-(γ₄ + κ / 2)) * B ^ ((D - 1) / (4 * θ)) * N := by
  let H := ENNReal.ofReal (δ / 2)
  have hH0 : H ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos hδ)).ne'
  have hHt : H ≠ ⊤ := ENNReal.ofReal_ne_top
  have hscale : H ^ (-γ₄) * H ^ (-κ / 2) =
      (2 : ENNReal) ^ (γ₄ + κ / 2) * (ENNReal.ofReal δ) ^ (-(γ₄ + κ / 2)) := by
    rw [← ENNReal.rpow_add _ _ hH0 hHt]
    have hg : -γ₄ + -κ / 2 = -(γ₄ + κ / 2) := by ring
    rw [hg]
    dsimp only [H]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [div_eq_mul_inv, ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top
      (by simp) _, ENNReal.inv_rpow, ← ENNReal.rpow_neg, neg_neg, mul_comm]
  have hcontrast : B ^ ((D - 1 - 2 * A) / (4 * θ)) * B ^ (A / (2 * θ)) =
      B ^ ((D - 1) / (4 * θ)) := by
    rw [← ENNReal.rpow_add _ _ hB.ne' hBt, theoremA_exponent_identity]
  calc
    M ≤ C₂ * H ^ (-γ₄) * B ^ ((D - 1 - 2 * A) / (4 * θ)) *
        ((1 + C₁) ^ (1 / 2 : ℝ) * H ^ (-κ / 2) * B ^ (A / (2 * θ)) * N) :=
      hM.trans (mul_le_mul' le_rfl hY)
    _ = (C₂ * (1 + C₁) ^ (1 / 2 : ℝ)) * (H ^ (-γ₄) * H ^ (-κ / 2)) *
        (B ^ ((D - 1 - 2 * A) / (4 * θ)) * B ^ (A / (2 * θ))) * N := by ring
    _ = _ := by rw [hscale, hcontrast]; ring

end CoarseDeGiorgi.Assembly
