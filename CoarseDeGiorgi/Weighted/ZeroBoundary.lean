module

public import CoarseDeGiorgi.Weighted.ZeroCore
public import CoarseDeGiorgi.Foundations.PoincareW11Zero

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

/-- Source coercivity on the zero-boundary completion. The constant is chosen
before the coefficient field and the pair, hence depends only on the domain.
The last inequality uses the extended squared mean plus energy, literally. -/
theorem exists_memH1a0_coercivity {d : ℕ} [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : CoeffField d), IsWeightedCoeffOn V a →
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d), MemH1a0 a V u G →
        IntegrableOn u V ∧
        (∫ x in V, G x) = 0 ∧
        |volumeAverage V u| ≤ C * Real.sqrt (∫ x in V, ((a x)⁻¹).trace) *
          Real.sqrt (weightedEnergy a V G).toReal ∧
        ENNReal.ofReal ((volumeAverage V u) ^ 2) + weightedEnergy a V G ≤
          ENNReal.ofReal (1 + C ^ 2 * (∫ x in V, ((a x)⁻¹).trace)) * weightedEnergy a V G := by
  obtain ⟨C0, hC0, hpoincare⟩ := Foundations.exists_zero_boundary_poincare_w11
    hV.isOpen hV.isBoundedDomain.isBounded
  let C := (volume V).toReal⁻¹ * C0
  have hC : 0 ≤ C := mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) hC0
  refine ⟨C, hC, ?_⟩
  intro a ha u G hu
  have hw11 := memH1a_memW11 hV hne ha (hu.memH1a ha)
  have hE := hw11.2.2.2.2
  have huI := hw11.1
  have hGI := hw11.2.1
  obtain ⟨huM, hGM, f, hf, hc, hl, ht⟩ := hu
  have hcore := fun n => isSmoothCore_of_supported ha (hf n).1 (hf n).2.1
  have hFM := fun n => smoothGrad_aestronglyMeasurable hV.isOpen (hcore n).1
  have hFE := fun n => (hcore n).2.2
  have htv := (core_tendsto_l1 hV hne ha hcore hc huM hl).2
  have htG := fun i => tendsto_coord_l1_of_energy ha hFM hGM hFE ht i
  have hzeroi (i : Fin d) : (∫ x in V, G x i) = 0 := by
    have hit : Tendsto (fun n => ∫ x in V, smoothGrad (f n) x i) atTop (nhds (∫ x in V, G x i)) :=
      tendsto_integral_of_L1' (fun x => G x i)
        (Eventually.of_forall fun n => coord_integrable_of_length (hFM n)
          (gradient_length_integrable_and_bound ha (hFM n) (hFE n)).1 i) (htG i)
    have heq : (fun n => ∫ x in V, smoothGrad (f n) x i) = (fun _ : ℕ => (0 : ℝ)) :=
      funext fun n => integral_smoothGrad_eq_zero (hf n).1 (hf n).2.1 (hf n).2.2 i
    rw [heq] at hit
    exact tendsto_nhds_unique hit tendsto_const_nhds
  have hzero : (∫ x in V, G x) = 0 := by
    have hIG : IntegrableOn G V := Integrable.of_eval hGI
    funext i
    have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).integral_comp_comm hIG
    exact hproj.symm.trans (hzeroi i)
  have hp := hpoincare u G f huI hGI (fun n => (hf n).1) (fun n => (hf n).2.1)
    (fun n => (hf n).2.2) htv htG
  have hlen := gradient_length_integrable_and_bound ha hGM hE
  have hmean : |volumeAverage V u| ≤ C * Real.sqrt (∫ x in V, ((a x)⁻¹).trace) *
      Real.sqrt (weightedEnergy a V G).toReal := by
    calc
      |volumeAverage V u| = (volume V).toReal⁻¹ * |∫ x in V, u x| := by
        simp only [volumeAverage, abs_mul, abs_inv, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ (volume V).toReal⁻¹ * ∫ x in V, |u x| :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ ≤ (volume V).toReal⁻¹ * (C0 * ∫ x in V, Real.sqrt (vecDot (G x) (G x))) :=
        mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ ≤ (volume V).toReal⁻¹ * (C0 * (Real.sqrt (∫ x in V, ((a x)⁻¹).trace) *
          Real.sqrt (weightedEnergy a V G).toReal)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlen.2 hC0)
          (inv_nonneg.mpr ENNReal.toReal_nonneg)
      _ = C * Real.sqrt (∫ x in V, ((a x)⁻¹).trace) * Real.sqrt (weightedEnergy a V G).toReal := by
        dsimp [C]
        ring
  have htrace : 0 ≤ ∫ x in V, ((a x)⁻¹).trace := by
    apply integral_nonneg_of_ae
    filter_upwards [ha.2.1] with x hx
    exact hx.inv.posSemidef.trace_nonneg
  have hsq : (volumeAverage V u) ^ 2 ≤ C ^ 2 * (∫ x in V, ((a x)⁻¹).trace) *
      (weightedEnergy a V G).toReal := by
    have h := mul_self_le_mul_self (abs_nonneg _) hmean
    simpa only [← pow_two, sq_abs, mul_pow, Real.sq_sqrt htrace, Real.sq_sqrt ENNReal.toReal_nonneg,
      mul_assoc] using h
  have hreal : (volumeAverage V u) ^ 2 + (weightedEnergy a V G).toReal ≤
      (1 + C ^ 2 * (∫ x in V, ((a x)⁻¹).trace)) * (weightedEnergy a V G).toReal := by
    nlinarith only [hsq]
  have hnorm : ENNReal.ofReal ((volumeAverage V u) ^ 2) + weightedEnergy a V G ≤
      ENNReal.ofReal (1 + C ^ 2 * (∫ x in V, ((a x)⁻¹).trace)) * weightedEnergy a V G := by
    have hcoef : 0 ≤ 1 + C ^ 2 * (∫ x in V, ((a x)⁻¹).trace) := by positivity
    have hof : ENNReal.ofReal (weightedEnergy a V G).toReal = weightedEnergy a V G :=
      ENNReal.ofReal_toReal hE.ne
    rw [← hof, ← ENNReal.ofReal_add (sq_nonneg _) ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul hcoef]
    exact ENNReal.ofReal_le_ofReal hreal
  exact ⟨huI, hzero, hmean, hnorm⟩

end CoarseDeGiorgi.Weighted
