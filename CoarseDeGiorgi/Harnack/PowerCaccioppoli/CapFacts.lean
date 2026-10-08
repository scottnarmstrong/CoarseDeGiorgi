module

public import CoarseDeGiorgi.Harnack.Selection.Cap
public import CoarseDeGiorgi.Weighted.Energy
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import CoarseDeGiorgi.Foundations.FractionalSobolev.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Positive-cap identities used in the signed test limit -/

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open Homogenization MeasureTheory Set
open scoped ENNReal

/-- Pairing the capped gradient with `a H` over `V` gives the weighted energy of the capped
gradient. -/
theorem positive_cap_pairing_eq_energy
    {d : ℕ} {V : Set (Vec d)} (a : CoeffField d)
    (ha : IsWeightedCoeffOn V a) (v : Vec d → ℝ) (H : Vec d → Vec d)
    (N : ℝ≥0∞)
    (hcapMeas : AEStronglyMeasurable
      (Selection.selectionCapGradient 0 N v H) (volume.restrict V)) :
    (∫ x in V, vecDot (Selection.selectionCapGradient 0 N v H x)
      (matVecMul (a x) (H x))) =
      (weightedEnergy a V (Selection.selectionCapGradient 0 N v H)).toReal := by
  rw [Weighted.energy_toReal ha hcapMeas]
  apply integral_congr_ae
  filter_upwards with x
  by_cases htop : N = ⊤
  · by_cases hband : 0 < v x
    · simp only [Selection.selectionCapGradient, ite_eq_left htop,
        indicator_of_mem (show x ∈ {x | 0 < v x} from hband)]
    · simp only [Selection.selectionCapGradient, ite_eq_left htop,
        indicator_of_notMem (show x ∉ {x | 0 < v x} from hband), vecDot_zero_left]
  · by_cases hband : 0 < v x ∧ v x < 0 + N.toReal
    · simp only [Selection.selectionCapGradient, ite_eq_right htop,
        indicator_of_mem (show x ∈ {x | 0 < v x ∧ v x < 0 + N.toReal} from hband)]
    · simp only [Selection.selectionCapGradient, ite_eq_right htop,
        indicator_of_notMem (show x ∉ {x | 0 < v x ∧ v x < 0 + N.toReal} from hband), vecDot_zero_left]

/-- The cap-to-value ratio lies between zero and one on a positive value. -/
theorem positive_cap_ratio_bounds {d : ℕ} (v : Vec d → ℝ) (N : ℝ≥0∞)
    (x : Vec d) (hx : 0 < v x) :
    0 ≤ Selection.selectionCap 0 N v x / v x ∧
      Selection.selectionCap 0 N v x / v x ≤ 1 := by
  have hcap : 0 ≤ Selection.selectionCap 0 N v x ∧
      Selection.selectionCap 0 N v x ≤ v x := by
    by_cases htop : N = ⊤
    · simp only [Selection.selectionCap, ite_eq_left htop, sub_zero,
        max_eq_left hx.le]
      exact ⟨hx.le, le_rfl⟩
    · simp only [Selection.selectionCap, ite_eq_right htop, sub_zero,
        max_eq_left hx.le]
      exact ⟨le_min hx.le ENNReal.toReal_nonneg, min_le_left _ _⟩
  exact ⟨div_nonneg hcap.1 hx.le, (div_le_one hx).mpr hcap.2⟩

/-- The positive cap of an a.e. strongly measurable function is a.e. strongly measurable. -/
theorem positive_cap_aestronglyMeasurable
    {d : ℕ} {v : Vec d → ℝ} {μ : Measure (Vec d)}
    (hv : AEStronglyMeasurable v μ) (N : ℝ≥0∞) :
    AEStronglyMeasurable (Selection.selectionCap 0 N v) μ := by
  change AEStronglyMeasurable
    (fun x => if N = ⊤ then max (v x - 0) 0
      else min (max (v x - 0) 0) N.toReal) μ
  by_cases htop : N = ⊤
  · have hc : Continuous (fun z : ℝ => max z 0) := by fun_prop
    simpa only [ite_eq_left htop, sub_zero] using
      hc.comp_aestronglyMeasurable hv
  · have hc : Continuous (fun z : ℝ => min (max z 0) N.toReal) := by fun_prop
    simpa only [ite_eq_right htop, sub_zero] using
      hc.comp_aestronglyMeasurable hv

/-- Finite power energy controls the cap quotient without a majorant for the
smooth test sequence. -/
theorem positive_cap_ratio_integrable_nonneg
    {d : ℕ} {V : Set (Vec d)} (a : CoeffField d)
    (ha : IsWeightedCoeffOn V a) {v : Vec d → ℝ} {H : Vec d → Vec d}
    (hv : AEStronglyMeasurable v (volume.restrict V))
    (hH : AEStronglyMeasurable H (volume.restrict V))
    (hE : weightedEnergy a V H < ⊤)
    (hpositive : ∀ᵐ x ∂volume.restrict V, 0 < v x) (N : ℝ≥0∞) :
    IntegrableOn (fun x => (Selection.selectionCap 0 N v x / v x) *
      vecDot (H x) (matVecMul (a x) (H x))) V ∧
    (0 ≤ᵐ[volume.restrict V] fun x =>
      (Selection.selectionCap 0 N v x / v x) *
        vecDot (H x) (matVecMul (a x) (H x))) := by
  have hcap := positive_cap_aestronglyMeasurable hv N
  have hratioBound : ∀ᵐ x ∂volume.restrict V,
      ‖Selection.selectionCap 0 N v x / v x‖ ≤ (1 : ℝ) := by
    filter_upwards [hpositive] with x hx
    obtain ⟨hlo, hhi⟩ := positive_cap_ratio_bounds v N x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlo] using hhi
  refine ⟨(Weighted.quadratic_integrable ha hH hE).bdd_mul (hcap.div₀ hv) hratioBound,
    ?_⟩
  filter_upwards [hpositive, Weighted.quadratic_nonneg ha H] with x hx hq
  exact mul_nonneg (positive_cap_ratio_bounds v N x hx).1 hq

/-- The positive cap is `1`-Lipschitz in the function value. -/
theorem positive_cap_abs_sub_le {d : ℕ} (v : Vec d → ℝ) (N : ℝ≥0∞)
    (x y : Vec d) :
    |Selection.selectionCap 0 N v x - Selection.selectionCap 0 N v y| ≤
      |v x - v y| := by
  have hLip : LipschitzWith 1 (fun z : ℝ =>
      if N = ⊤ then max z 0 else min (max z 0) N.toReal) := by
    by_cases htop : N = ⊤
    · simpa only [ite_eq_left htop, id_eq] using LipschitzWith.id.max_const (0 : ℝ)
    · simpa only [ite_eq_right htop, id_eq] using
        (LipschitzWith.id.max_const (0 : ℝ)).min_const N.toReal
  simpa only [Selection.selectionCap, sub_zero, Real.dist_eq,
    NNReal.coe_one, one_mul] using hLip.dist_le_mul (v x) (v y)

/-- Capping does not increase the selected fractional seminorm. -/
theorem positive_cap_surface_seminorm_le
    {d : ℕ} (τ α r : ℝ) (hr : 0 < r) (v : Vec d → ℝ) (N : ℝ≥0∞) :
    surfaceFracSeminorm τ α r (Selection.selectionCap 0 N v) ≤
      surfaceFracSeminorm τ α r v := by
  apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ 1 / r)
  apply lintegral_mono
  intro p
  unfold fracKernelWithDimension
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Foundations.FractionalSobolev.euclidDist_nonneg _ _) _)
  exact Real.rpow_le_rpow (abs_nonneg _) (positive_cap_abs_sub_le v N p.1 p.2) hr.le

/-- Capping does not increase any Lebesgue quasi-norm, even without a positive
representative on the selected surface. -/
theorem positive_cap_eLpNorm_le
    {d : ℕ} (v : Vec d → ℝ) (N r : ℝ≥0∞) (μ : Measure (Vec d))
    (hcap : AEStronglyMeasurable (Selection.selectionCap 0 N v) μ) :
    eLpNorm (Selection.selectionCap 0 N v) r μ ≤ eLpNorm v r μ := by
  apply eLpNorm_mono hcap
  intro x
  have hcap0 : 0 ≤ Selection.selectionCap 0 N v x := by
    by_cases htop : N = ⊤
    · simp only [Selection.selectionCap, ite_eq_left htop, sub_zero]
      exact le_max_right _ _
    · simp only [Selection.selectionCap, ite_eq_right htop, sub_zero]
      exact le_min (le_max_right _ _) ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg hcap0, Real.norm_eq_abs]
  have hcapLe : Selection.selectionCap 0 N v x ≤ max (v x) 0 := by
    by_cases htop : N = ⊤
    · simp only [Selection.selectionCap, ite_eq_left htop, sub_zero]
      exact le_rfl
    · simp only [Selection.selectionCap, ite_eq_right htop, sub_zero]
      exact min_le_left _ _
  exact hcapLe.trans (max_le (le_abs_self _) (abs_nonneg _))

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
