import CoarseDeGiorgi.Foundations.Reconstruction.Defs
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Minkowski and Fatou for the exact Euclidean reconstruction seminorm -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section
variable {d : ℕ}

/-- Linear Euclidean difference quotient; its `L^r` norm is the fractional seminorm. -/
def assemblyQuotient (α r : ℝ) (f : Vec d → ℝ) (p : Vec d × Vec d) : ℝ :=
  Euclid.eDist2 p.1 p.2 ^ (-(α + (d : ℝ) / r)) * (f p.1 - f p.2)

theorem assemblyQuotient_measurable (α r : ℝ) {f : Vec d → ℝ}
    (hf : Measurable f) : Measurable (assemblyQuotient α r f) :=
  ((Euclid.continuous_eNorm2.measurable.comp (measurable_fst.sub measurable_snd)).pow
    measurable_const).mul ((hf.comp measurable_fst).sub (hf.comp measurable_snd))

theorem assemblyQuotient_rpow (α : ℝ) {r : ℝ} (hr : 0 < r) (f : Vec d → ℝ)
    (p : Vec d × Vec d) :
    ‖assemblyQuotient α r f p‖ₑ ^ r =
      Euclid.euclidKernel ((d : ℝ) + α * r) r f p := by
  rw [assemblyQuotient, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hr.le,
    Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg (Euclid.eDist2_nonneg _ _) _),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (Euclid.eDist2_nonneg _ _) _) hr.le,
    ← Real.rpow_mul (Euclid.eDist2_nonneg _ _), Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hr.le]
  have he : -(α + (d : ℝ) / r) * r = -((d : ℝ) + α * r) := by
    field_simp
    ring
  rw [he]
  unfold Euclid.euclidKernel
  rw [Real.rpow_neg (Euclid.eDist2_nonneg _ _), div_eq_mul_inv,
    ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
  exact mul_comm _ _

theorem assembly_seminorm_eq_eLpNorm (V : Set (Vec d)) (α : ℝ) {r : ℝ}
    (hr : 0 < r) {f : Vec d → ℝ} (hf : Measurable f) :
    CoarseDeGiorgi.fracSeminorm V α r f =
      eLpNorm (assemblyQuotient α r f) (ENNReal.ofReal r)
        ((volume.restrict V).prod (volume.restrict V)) := by
  rw [← fracSeminorm_eq_statement, FracGeometry.fracSeminorm_eq_eFracSeminorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hr))
      ENNReal.ofReal_ne_top (assemblyQuotient_measurable α r hf).aestronglyMeasurable,
    ENNReal.toReal_ofReal hr.le]
  simp only [Euclid.eFracSeminorm, assemblyQuotient_rpow α hr]

theorem assembly_seminorm_sum_le {ι : Type*} (s : Finset ι) {r : ℝ}
    (hr : 1 < r) (V : Set (Vec d)) (α : ℝ) (f : ι → Vec d → ℝ)
    (hf : ∀ i, Measurable (f i)) :
    CoarseDeGiorgi.fracSeminorm V α r (fun x => ∑ i ∈ s, f i x) ≤
      ∑ i ∈ s, CoarseDeGiorgi.fracSeminorm V α r (f i) := by
  have hsum : Measurable (fun x => ∑ i ∈ s, f i x) := by fun_prop
  rw [assembly_seminorm_eq_eLpNorm V α (zero_lt_one.trans hr) hsum]
  simp_rw [assembly_seminorm_eq_eLpNorm V α (zero_lt_one.trans hr) (hf _)]
  have heq : assemblyQuotient α r (fun x => ∑ i ∈ s, f i x) =
      ∑ i ∈ s, assemblyQuotient α r (f i) := by
    ext p
    simp only [assemblyQuotient, Finset.sum_apply, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
  rw [heq]
  exact eLpNorm_sum_le (by simpa using ENNReal.ofReal_le_ofReal hr.le)

/-- Fatou needs only a.e. scalar convergence; the exceptional pair set is null. -/
theorem assembly_seminorm_le_of_ae_tendsto {V : Set (Vec d)} {α r : ℝ}
    (hr : 0 < r) {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ} {C : ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ x ∂volume.restrict V, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hbound : ∀ n, CoarseDeGiorgi.fracSeminorm V α r (f n) ≤ C) :
    CoarseDeGiorgi.fracSeminorm V α r g ≤ C := by
  rw [assembly_seminorm_eq_eLpNorm V α hr hg]
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (Eventually.of_forall fun n => by
      simpa only [assembly_seminorm_eq_eLpNorm V α hr (hf n)] using hbound n)
    (fun n => (assemblyQuotient_measurable α r (hf n)).aestronglyMeasurable)
    (assemblyQuotient_measurable α r hg).aestronglyMeasurable
  have hfst := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict V) (ν := volume.restrict V)).ae hlim
  have hsnd := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict V) (ν := volume.restrict V)).ae hlim
  filter_upwards [hfst, hsnd] with p hp hq
  exact tendsto_const_nhds.mul (hp.sub hq)

/-- The subsequence in Step 10 follows directly from the Step 8 `L^r` limit. -/
theorem assembly_exists_subsequence_ae {V : Set (Vec d)} {r : ℝ} (hr : 0 < r)
    {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hlim : Tendsto (fun n => eLpNorm (f n - g) (ENNReal.ofReal r)
      (volume.restrict V)) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂volume.restrict V, Tendsto (fun n => f (ns n) x) atTop (𝓝 (g x)) :=
  (tendstoInMeasure_of_tendsto_eLpNorm
    (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) hlim).exists_seq_tendsto_ae

end
end CoarseDeGiorgi.Foundations.Reconstruction
