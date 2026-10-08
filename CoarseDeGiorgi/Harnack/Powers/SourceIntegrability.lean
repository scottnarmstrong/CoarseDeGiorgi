module

public import CoarseDeGiorgi.Harnack.Powers.Chain
public import CoarseDeGiorgi.Weighted.Identification
public import CoarseDeGiorgi.Weighted.Energy

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Powers

open Homogenization MeasureTheory
open scoped ENNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The shifted power is in the source `L^r` class, and its source energy density is
integrable. The positive-power branch uses `mr < 1`; the negative-power branch
uses the uniform bound coming from the shift.
-/
theorem signedPower_source_integrability (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a a V u G)
    (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x)
    (ε m r : ℝ) (hε : 0 < ε) (hm : m < 1 / 2) (hm0 : m ≠ 0)
    (hr1 : 1 < r) (hr2 : r < 2) :
    MemLp (fun x => (u x + ε) ^ m) (ENNReal.ofReal r) (volume.restrict V) ∧
      IntegrableOn
        (fun x => m ^ 2 * (u x + ε) ^ (m - 2) *
          vecDot (G x) (matVecMul (a x) (G x))) V := by
  let μ := volume.restrict V
  let : IsFiniteMeasure μ := hV.isFiniteMeasure_restrict_volume
  have hUintegrable : Integrable (fun x => u x + ε) μ := by
    change IntegrableOn (fun x => u x + ε) V
    exact (Weighted.memH1a_memW11 hV hne ha hu).1.add
      (integrableOn_const hV.isBoundedDomain.isBounded.measure_lt_top.ne)
  have hchain := signedPower_chain hV hne ha hu hnonneg ε m hε hm
  have hvmeas : AEStronglyMeasurable (fun x => (u x + ε) ^ m) μ := hchain.1.1
  have hLr : MemLp (fun x => (u x + ε) ^ m) (ENNReal.ofReal r) μ := by
    by_cases hmneg : m < 0
    · apply MemLp.of_bound hvmeas (ε ^ m)
      filter_upwards [hnonneg] with x hx
      have hU : ε ≤ u x + ε := by linarith
      have hUpos : 0 < u x + ε := lt_of_lt_of_le hε hU
      have hvnonneg : 0 ≤ (u x + ε) ^ m := Real.rpow_nonneg (le_of_lt hUpos) _
      rw [Real.norm_eq_abs, abs_of_nonneg hvnonneg]
      exact Real.rpow_le_rpow_of_nonpos hε hU (le_of_lt hmneg)
    · have hmpos : 0 < m := lt_of_le_of_ne (le_of_not_gt hmneg) (Ne.symm hm0)
      have hrpos : 0 < r := lt_trans zero_lt_one hr1
      have hpr : 0 ≤ m * r := mul_nonneg (le_of_lt hmpos) (le_of_lt hrpos)
      have hpr1 : m * r ≤ 1 := by nlinarith
      have hnormU1 : Integrable (fun x => ‖u x + ε‖ ^ (1 : ℝ)) μ := by
        have h := (memLp_one_iff_integrable.mpr hUintegrable).integrable_norm_rpow
          (by norm_num) (by norm_num)
        simpa using h
      have hnormUp : Integrable (fun x => ‖u x + ε‖ ^ (m * r)) μ :=
        integrable_norm_rpow_of_le hUintegrable.aestronglyMeasurable hpr
          (by norm_num) hpr1 hnormU1
      have hpowerEq :
          (fun x => ‖(u x + ε) ^ m‖ ^ r) =ᵐ[μ]
            (fun x => ‖u x + ε‖ ^ (m * r)) := by
        filter_upwards [hnonneg] with x hx
        have hUpos : 0 < u x + ε := by linarith
        rw [show ‖(u x + ε) ^ m‖ = (u x + ε) ^ m by
              rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hUpos) _)],
          show ‖u x + ε‖ = u x + ε by rw [Real.norm_eq_abs, abs_of_pos hUpos],
          ← Real.rpow_mul (le_of_lt hUpos)]
      have hnormV : Integrable (fun x => ‖(u x + ε) ^ m‖ ^ r) μ :=
        hnormUp.congr hpowerEq.symm
      have hmemlp : MemLp (fun x => (u x + ε) ^ m) (ENNReal.ofReal r) μ := by
        rw [← integrable_norm_rpow_iff hvmeas
          (ENNReal.ofReal_pos.mpr (by linarith)).ne' ENNReal.ofReal_ne_top]
        simpa [ENNReal.toReal_ofReal (le_trans (by norm_num) hr1.le)] using hnormV
      exact hmemlp
  have henergy := Weighted.MemH1a.energy_lt_top hV.isOpen ha hu
  have hquad : IntegrableOn
      (fun x => vecDot (G x) (matVecMul (a x) (G x))) V :=
    Weighted.quadratic_integrable ha hu.2.1 henergy
  have hfactorBound : ∀ᵐ x ∂μ,
      |m ^ 2 * (u x + ε) ^ (m - 2)| ≤ m ^ 2 * ε ^ (m - 2) := by
    filter_upwards [hnonneg] with x hx
    have hU : ε ≤ u x + ε := by linarith
    have hUpos : 0 < u x + ε := lt_of_lt_of_le hε hU
    have hexp : m - 2 ≤ 0 := by linarith
    have hpow : (u x + ε) ^ (m - 2) ≤ ε ^ (m - 2) :=
      Real.rpow_le_rpow_of_nonpos hε hU hexp
    have hpow0 : 0 ≤ (u x + ε) ^ (m - 2) := Real.rpow_nonneg (le_of_lt hUpos) _
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg m) hpow0)]
    exact mul_le_mul_of_nonneg_left hpow (sq_nonneg m)
  have hfactorMeas : AEStronglyMeasurable
      (fun x => m ^ 2 * (u x + ε) ^ (m - 2)) μ := by
    have hUmeas : AEStronglyMeasurable (fun x => u x + ε) μ :=
      (continuous_id.add continuous_const).comp_aestronglyMeasurable hu.1
    exact aestronglyMeasurable_const.mul
      (hUmeas.aemeasurable.pow_const (m - 2) |>.aestronglyMeasurable)
  have hsource : IntegrableOn
      (fun x => m ^ 2 * (u x + ε) ^ (m - 2) *
        vecDot (G x) (matVecMul (a x) (G x))) V := by
    exact hquad.bdd_mul hfactorMeas hfactorBound
  simpa [μ] using And.intro hLr hsource

omit [NeZero d] in
/-- The source density `v⁻¹ Gv · aGv` is pointwise the bounded negative shifted
power times the energy density of the original gradient.
-/
theorem signedPower_source_density_identity {V : Set (Vec d)} {a : CoeffField d}
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x)
    (ε m : ℝ) (hε : 0 < ε) :
    (fun x => ((u x + ε) ^ m)⁻¹ *
      vecDot ((m * (u x + ε) ^ (m - 1)) • G x)
        (matVecMul (a x) ((m * (u x + ε) ^ (m - 1)) • G x))) =ᵐ[
      volume.restrict V] (fun x => m ^ 2 * (u x + ε) ^ (m - 2) *
        vecDot (G x) (matVecMul (a x) (G x))) := by
  have hUpositive : ∀ᵐ x ∂volume.restrict V, 0 < u x + ε := by
    filter_upwards [hnonneg] with x hx
    linarith
  have hratio : (fun x => ((u x + ε) ^ (m - 1)) ^ 2 /
      (u x + ε) ^ m) =ᵐ[volume.restrict V] (fun x => (u x + ε) ^ (m - 2)) := by
    filter_upwards [hUpositive] with x hx
    have hpow : ((u x + ε) ^ (m - 1)) ^ 2 = (u x + ε) ^ (m - 2 + m) := by
      rw [← Real.rpow_natCast ((u x + ε) ^ (m - 1)) 2,
        ← Real.rpow_mul (le_of_lt hx)]
      congr 1
      ring
    rw [hpow, Real.rpow_add hx]
    have hden : (u x + ε) ^ m ≠ 0 := (Real.rpow_pos_of_pos hx m).ne'
    field_simp [hden]
  filter_upwards [hratio] with x hx
  simp only [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  calc
    ((u x + ε) ^ m)⁻¹ * ((m * (u x + ε) ^ (m - 1)) *
        ((m * (u x + ε) ^ (m - 1)) * vecDot (G x) (matVecMul (a x) (G x)))) =
        m ^ 2 * ((((u x + ε) ^ (m - 1)) ^ 2 /
          (u x + ε) ^ m)) * vecDot (G x) (matVecMul (a x) (G x)) := by ring
    _ = m ^ 2 * (u x + ε) ^ (m - 2) *
          vecDot (G x) (matVecMul (a x) (G x)) := by rw [hx]

end CoarseDeGiorgi.Harnack.Powers
