import CoarseDeGiorgi.Foundations.FractionalSobolev.UnitCubeExtension
import CoarseDeGiorgi.Statements.DnpvTheorem6_5

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

/-- A finite powered-energy coefficient depending only on dimension and exponents. -/
def unitCubeEnergyFactor (n : ℕ) (s p : ℝ) : ℝ≥0∞ :=
  1 + (2 : ℝ≥0∞) ^ p * ((3 ^ n : ℝ≥0∞) * (3 ^ n : ℝ≥0∞) +
    2 * (ENNReal.ofReal ((1 / 2 : ℝ) ^ (-s * p)) *
      ENNReal.ofReal (∫ z : Vec n, CoarseDeGiorgi.Foundations.FracGeometry.cutoffRadial s p 1 z) *
      (3 ^ n : ℝ≥0∞)))

lemma unitCubeEnergyFactor_ne_top (n : ℕ) (s p : ℝ) :
    unitCubeEnergyFactor n s p ≠ ⊤ := by
  unfold unitCubeEnergyFactor
  finiteness

lemma unitCubeEnergyFactor_pos (n : ℕ) (s p : ℝ) : 0 < unitCubeEnergyFactor n s p :=
  zero_lt_one.trans_le (le_add_right le_rfl)

/-- A compact reflected extension with full mixed-pair control, including p=1. -/
lemma unitCubeExtension_energy {n : ℕ} [NeZero n] {s p : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hp : 1 ≤ p) {f : Vec n → ℝ} (hf : Measurable f) :
    (∫⁻ xy : Vec n × Vec n, fracKernel s p (unitCubeExtension f) xy ∂(volume.prod volume)) ≤
      unitCubeEnergyFactor n s p * fracNorm (dnpvUnitCube n) s p f ^ p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let a : ℝ≥0∞ := 3 ^ n
  let A : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ (-s * p)) *
    ENNReal.ofReal (∫ z : Vec n, CoarseDeGiorgi.Foundations.FracGeometry.cutoffRadial s p 1 z)
  let L := eLpNorm f (ENNReal.ofReal p) (volume.restrict (dnpvUnitCube n)) ^ p
  let S := fracSeminorm (dnpvUnitCube n) s p f ^ p
  let F := fracNorm (dnpvUnitCube n) s p f ^ p
  have hL : L ≤ F := by
    dsimp [L, F]
    rw [fracNorm_power _ _ hp0]
    exact le_add_right le_rfl
  have hS : S ≤ F := by
    dsimp [S, F]
    rw [fracNorm_power _ _ hp0]
    exact le_add_left le_rfl
  have hm := cubeFold_lp_power_le hf hp0
  have he := cubeFold_seminorm_power_le hf hp0 (by positivity : 0 ≤ (n : ℝ) + s * p)
  have hc := CoarseDeGiorgi.Foundations.FracGeometry.fracSeminorm_cutoff_rpow_le
    (reflectedCube_open n) hs hs1 hp0 (by norm_num : (0 : ℝ) < 1 / 2)
    (hf.comp cubeFold_continuous.measurable)
    unitCubeCutoff_bound unitCubeCutoff_lipschitz
    (fun x hx y hy => unitCubeCutoff_separation hx hy)
  change fracSeminorm Set.univ s p (unitCubeExtension f) ^ p ≤
    (2 : ℝ≥0∞) ^ p * (fracSeminorm (reflectedCube n) s p (f ∘ cubeFold) ^ p +
      2 * (A * eLpNorm (f ∘ cubeFold) (ENNReal.ofReal p) (volume.restrict (reflectedCube n)) ^ p)) at hc
  rw [fracSeminorm_power _ _ hp0, Measure.restrict_univ] at hc
  calc
    _ ≤ (2 : ℝ≥0∞) ^ p * (fracSeminorm (reflectedCube n) s p (f ∘ cubeFold) ^ p +
        2 * (A * eLpNorm (f ∘ cubeFold) (ENNReal.ofReal p) (volume.restrict (reflectedCube n)) ^ p)) := hc
    _ ≤ (2 : ℝ≥0∞) ^ p * (a * a * S + 2 * (A * (a * L))) :=
      mul_le_mul' le_rfl (add_le_add he (mul_le_mul' le_rfl (mul_le_mul' le_rfl hm)))
    _ ≤ (2 : ℝ≥0∞) ^ p * (a * a * F + 2 * (A * (a * F))) :=
      mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hS)
        (mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hL))))
    _ = ((2 : ℝ≥0∞) ^ p * (a * a + 2 * (A * a))) * F := by
      simp only [mul_add, add_mul, mul_assoc]
    _ ≤ unitCubeEnergyFactor n s p * F := mul_le_mul' (le_add_left le_rfl) le_rfl

/-- The cube inequality first for genuine measurable functions, allowing infinite norms. -/
theorem unitCubeSobolev_measurable {n : ℕ} {s p : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp : 1 ≤ p) (hsp : s * p < (n : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Vec n → ℝ, Measurable f →
      eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent n s p)) (volume.restrict (dnpvUnitCube n)) ≤
        ENNReal.ofReal C * fracNorm (dnpvUnitCube n) s p f := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hn : 0 < n := (critical_parameters hs hp hsp).1
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨C₀, hC₀, h65⟩ := CoarseDeGiorgi.dnpv_theorem_6_5 n s p hs hs1 hp hsp
  let C := (C₀ * (unitCubeEnergyFactor n s p).toReal) ^ (1 / p)
  have hprod : 0 < C₀ * (unitCubeEnergyFactor n s p).toReal :=
    mul_pos hC₀ (ENNReal.toReal_pos (unitCubeEnergyFactor_pos n s p).ne'
      (unitCubeEnergyFactor_ne_top n s p))
  have hC : 0 < C := Real.rpow_pos_of_pos hprod _
  have hCpower : ENNReal.ofReal C ^ p = ENNReal.ofReal C₀ * unitCubeEnergyFactor n s p := by
    dsimp [C]
    rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hprod _),
      ← Real.rpow_mul hprod.le, one_div_mul_cancel hp0.ne', Real.rpow_one,
      ENNReal.ofReal_mul hC₀.le, ENNReal.ofReal_toReal (unitCubeEnergyFactor_ne_top n s p)]
  refine ⟨C, hC, ?_⟩
  intro f hf
  let G := unitCubeExtension f
  have hGeq : f =ᵐ[volume.restrict (dnpvUnitCube n)] G := by
    filter_upwards [ae_restrict_mem (unitCube_open n).measurableSet] with x hx
    exact (unitCubeExtension_eq hx).symm
  have hnorm : eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent n s p)) (volume.restrict (dnpvUnitCube n)) ≤
      eLpNorm G (ENNReal.ofReal (dnpvCriticalExponent n s p)) volume := by
    rw [eLpNorm_congr_ae hGeq]
    exact eLpNorm_mono_measure G Measure.restrict_le_self
  have hGsob := h65 G (unitCubeExtension_measurable hf) (unitCubeExtension_compact f)
  apply (ENNReal.rpow_le_rpow_iff hp0).mp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hCpower]
  exact (ENNReal.rpow_le_rpow hnorm hp0.le).trans (hGsob.trans
    (by simpa only [mul_assoc] using mul_le_mul' le_rfl (unitCubeExtension_energy hs hs1 hp hf)))

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
