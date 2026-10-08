import CoarseDeGiorgi.Weighted.EnergyLimits
import CoarseDeGiorgi.Foundations.PoincareW11Mean

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The squared-mean-plus-energy Cauchy condition on the smooth core implies L¹ Cauchy. -/
theorem core_l1_cauchy (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {f : ℕ → Vec d → ℝ}
    (hf : ∀ n, IsSmoothCore a V (f n))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      ENNReal.ofReal ((volumeAverage V (fun x => f n x - f m x)) ^ 2) +
        weightedEnergy a V (fun x => smoothGrad (f n) x - smoothGrad (f m) x) <
        ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      ∫ x in V, |f n x - f m x| < ε := by
  let : IsFiniteMeasure (volume.restrict V) := hV.isBoundedDomain.isFiniteMeasure_restrict_volume
  obtain ⟨C, hC, hmean⟩ := Foundations.exists_mean_zero_poincare_w11 hV hne
  let T := Real.sqrt (∫ x in V, ((a x)⁻¹).trace)
  let B := C * T + (volume V).toReal
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) ENNReal.toReal_nonneg
  intro ε hε
  let t := ε / (B + 1)
  have ht : 0 < t := div_pos hε (by linarith only [hB])
  obtain ⟨N, hN⟩ := hc (t ^ 2) (sq_pos_of_pos ht)
  refine ⟨N, ?_⟩
  intro m n hm hn
  let z : Vec d → ℝ := fun x => f n x - f m x
  let D : Vec d → Vec d := fun x => smoothGrad (f n) x - smoothGrad (f m) x
  have hz : IntegrableOn z V := (hf n).2.1.sub (hf m).2.1
  have hD : AEStronglyMeasurable D (volume.restrict V) :=
    (smoothGrad_aestronglyMeasurable hV.isOpen (hf n).1).sub
      (smoothGrad_aestronglyMeasurable hV.isOpen (hf m).1)
  have hsmall := hN m n hm hn
  have hEsmall : weightedEnergy a V D < ENNReal.ofReal (t ^ 2) :=
    lt_of_le_of_lt le_add_self hsmall
  have hE : weightedEnergy a V D < ⊤ := hEsmall.trans ENNReal.ofReal_lt_top
  have hmsmall : (volumeAverage V z) ^ 2 ≤ t ^ 2 :=
    ((ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos ht)).mp
      (lt_of_le_of_lt le_self_add hsmall)).le
  have hEsqrt : Real.sqrt (weightedEnergy a V D).toReal ≤ t := by
    have hle := Real.sqrt_le_sqrt (ENNReal.toReal_lt_of_lt_ofReal hEsmall).le
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg ht.le] using hle
  have hmsqrt : |volumeAverage V z| ≤ t := by
    have hle := Real.sqrt_le_sqrt hmsmall
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg ht.le] using hle
  have hlen := gradient_length_integrable_and_bound ha hD hE
  have hweak : HasWeakGradientOn V z D :=
    hasWeakGradientOn_congr_grad
      (hasWeakGradientOn_of_contDiffOn hV.isOpen ((hf n).1.sub (hf m).1))
      (smoothGrad_sub_ae hV.isOpen (hf n).1 (hf m).1)
  have hp := hmean z D hz (coord_integrable_of_length hD hlen.1) hweak
  have hcenter : IntegrableOn (fun x => |z x - volumeAverage V z|) V :=
    (hz.sub (integrable_const _)).abs
  have htriangle : (∫ x in V, |z x|) ≤
      (∫ x in V, |z x - volumeAverage V z|) + (volume V).toReal * |volumeAverage V z| := by
    rw [← show (∫ x in V, |volumeAverage V z|) = (volume V).toReal * |volumeAverage V z| by
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]]
    rw [← integral_add hcenter (integrable_const _)]
    apply integral_mono_ae hz.abs (hcenter.add (integrable_const _))
    filter_upwards with x
    simpa only [sub_add_cancel, Pi.add_apply] using abs_add_le (z x - volumeAverage V z) (volumeAverage V z)
  have hfinal : (∫ x in V, |z x|) ≤ B * t := by
    calc
      (∫ x in V, |z x|) ≤ C * (∫ x in V, Real.sqrt (vecDot (D x) (D x))) +
          (volume V).toReal * |volumeAverage V z| :=
        htriangle.trans (add_le_add hp le_rfl)
      _ ≤ C * (T * Real.sqrt (weightedEnergy a V D).toReal) +
          (volume V).toReal * |volumeAverage V z| :=
        add_le_add (mul_le_mul_of_nonneg_left hlen.2 hC) le_rfl
      _ ≤ C * (T * t) + (volume V).toReal * t := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hEsqrt (Real.sqrt_nonneg _)) hC)
          (mul_le_mul_of_nonneg_left hmsqrt ENNReal.toReal_nonneg)
      _ = B * t := by dsimp [B]; ring
  have hBt : B * t < ε := by
    have heq : t * (B + 1) = ε := div_mul_cancel₀ ε (by linarith only [hB])
    nlinarith only [ht, heq]
  exact hfinal.trans_lt hBt

/-- The approved completion data gives global L¹ convergence of its defining values. -/
theorem core_tendsto_l1 (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {f : ℕ → Vec d → ℝ} {u : Vec d → ℝ}
    (hf : ∀ n, IsSmoothCore a V (f n))
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      ENNReal.ofReal ((volumeAverage V (fun x => f n x - f m x)) ^ 2) +
        weightedEnergy a V (fun x => smoothGrad (f n) x - smoothGrad (f m) x) <
        ENNReal.ofReal ε)
    (hu : AEStronglyMeasurable u (volume.restrict V))
    (hloc : ∀ K : Set (Vec d), IsCompact K → K ⊆ V →
      Tendsto (fun n => ∫⁻ x in K, ‖f n x - u x‖ₑ) atTop (nhds 0)) :
    IntegrableOn u V ∧ Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (nhds 0) := by
  obtain ⟨w, hw, htw⟩ := exists_l1_limit_of_cauchy (fun n => (hf n).2.1)
    (core_l1_cauchy hV hne ha hf hc)
  have heq := ae_eq_of_global_local_l1_limits hV.isOpen (fun n => (hf n).2.1.1) hu htw hloc
  refine ⟨hw.congr heq, htw.congr ?_⟩
  intro n
  exact eLpNorm_congr_ae (EventuallyEq.rfl.sub heq)

end CoarseDeGiorgi.Weighted
