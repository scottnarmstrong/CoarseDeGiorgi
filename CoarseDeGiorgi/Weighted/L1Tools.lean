import CoarseDeGiorgi.Weighted.SmoothCore
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

/-- The real integral of the absolute value represents the scalar L¹ seminorm. -/
theorem l1_eq_ofReal_integral_abs {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) :
    eLpNorm f 1 μ = ENNReal.ofReal (∫ x, |f x| ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.1]
  simpa only [← ofReal_norm, Real.norm_eq_abs] using
    (ofReal_integral_eq_lintegral_ofReal hf.norm (Eventually.of_forall fun x => norm_nonneg (f x))).symm

/-- L¹ convergence is preserved by multiplication by a bounded measurable factor. -/
theorem tendsto_integral_mul_of_l1 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g ψ : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hψ : MemLp ψ ⊤ μ)
    (ht : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f n x * ψ x ∂μ) atTop (nhds (∫ x, g x * ψ x ∂μ)) := by
  have hp : Tendsto (fun n => eLpNorm (f n - g) 1 μ * eLpNorm ψ ⊤ μ) atTop (nhds 0) := by
    simpa only [zero_mul] using
      ENNReal.Tendsto.mul ht (Or.inr hψ.eLpNorm_lt_top.ne) tendsto_const_nhds (Or.inr (by simp))
  apply tendsto_integral_of_L1' (fun x => g x * ψ x)
    (Eventually.of_forall fun n => memLp_one_iff_integrable.mp
      ((memLp_one_iff_integrable.mpr (hf n)).fun_mul hψ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hp (fun _ => bot_le)
  intro n
  change eLpNorm ((fun x => f n x * ψ x) - (fun x => g x * ψ x)) 1 μ ≤ _
  have heq : ((fun x => f n x * ψ x) - (fun x => g x * ψ x)) = (f n - g) • ψ := by
    funext x
    change f n x * ψ x - g x * ψ x = (f n x - g x) * ψ x
    ring
  rw [heq]
  exact eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top (φ := f n - g) (f := ψ) 1 hψ.aestronglyMeasurable

/-- Weak gradients are closed under scalar and coordinate L¹ convergence. -/
theorem hasWeakGradientOn_of_l1_limit {d : ℕ} {V : Set (Vec d)}
    {f : ℕ → Vec d → ℝ} {G : ℕ → Vec d → Vec d} {u : Vec d → ℝ} {H : Vec d → Vec d}
    (hf : ∀ n, IntegrableOn (f n) V)
    (hG : ∀ n i, IntegrableOn (fun x => G n x i) V)
    (hw : ∀ n, HasWeakGradientOn V (f n) (G n))
    (htf : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (nhds 0))
    (htG : ∀ i, Tendsto (fun n => eLpNorm (fun x => G n x i - H x i) 1
      (volume.restrict V)) atTop (nhds 0)) :
    HasWeakGradientOn V u H := by
  intro i ψ hψ hc hs
  have htψ : MemLp ψ ⊤ (volume.restrict V) :=
    (hψ.continuous.memLp_of_hasCompactSupport hc).restrict V
  have htdψ : MemLp (fun x => fderiv ℝ ψ x (basisVec i)) ⊤ (volume.restrict V) :=
    (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict V
  have hl := tendsto_integral_mul_of_l1 hf htdψ htf
  have hr := tendsto_integral_mul_of_l1 (fun n => hG n i) htψ (htG i)
  have heq : (fun n => ∫ x in V, f n x * fderiv ℝ ψ x (basisVec i)) =
      (fun n => -(∫ x in V, G n x i * ψ x)) :=
    funext fun n => hw n i ψ hψ hc hs
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr.neg

/-- A global L¹ limit agrees with a prescribed local L¹ limit on an open set. -/
theorem ae_eq_of_global_local_l1_limits {d : ℕ} {V : Set (Vec d)} (hV : IsOpen V)
    {f : ℕ → Vec d → ℝ} {u w : Vec d → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict V))
    (hu : AEStronglyMeasurable u (volume.restrict V))
    (ht : Tendsto (fun n => eLpNorm (f n - w) 1 (volume.restrict V)) atTop (nhds 0))
    (hloc : ∀ K : Set (Vec d), IsCompact K → K ⊆ V →
      Tendsto (fun n => ∫⁻ x in K, ‖f n x - u x‖ₑ) atTop (nhds 0)) :
    w =ᵐ[volume.restrict V] u := by
  let : LocallyCompactSpace V := hV.locallyCompactSpace
  let K : ℕ → Set (Vec d) := fun n => Subtype.val '' compactCovering V n
  have hK (n : ℕ) : IsCompact (K n) := (isCompact_compactCovering V n).image continuous_subtype_val
  have hKV (n : ℕ) : K n ⊆ V := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hcover : ⋃ n, K n = V := by
    simp only [K, ← Set.image_iUnion, iUnion_compactCovering, Set.image_univ, Subtype.range_val]
  rw [← hcover, ae_eq_restrict_iUnion_iff]
  intro n
  have hle : volume.restrict (K n) ≤ volume.restrict V := Measure.restrict_mono (hKV n) le_rfl
  have htw : Tendsto (fun j => eLpNorm (f j - w) 1 (volume.restrict (K n))) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
      (fun j => eLpNorm_mono_measure _ hle)
  have htu : Tendsto (fun j => eLpNorm (f j - u) 1 (volume.restrict (K n))) atTop (nhds 0) := by
    convert hloc (K n) (hK n) (hKV n) using 1
    funext j
    exact eLpNorm_one_eq_lintegral_enorm ((hf j).mono_measure hle |>.sub (hu.mono_measure hle))
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_tendsto_eLpNorm (by simp) htw)
    (tendstoInMeasure_of_tendsto_eLpNorm (by simp) htu)

/-- Completeness of scalar L¹, in the raw-function form used by the completion. -/
theorem exists_l1_limit_of_cauchy {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} (hf : ∀ n, Integrable (f n) μ)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      ∫ x, |f n x - f m x| ∂μ < ε) :
    ∃ w : α → ℝ, Integrable w μ ∧
      Tendsto (fun n => eLpNorm (f n - w) 1 μ) atTop (nhds 0) := by
  let F : ℕ → Lp ℝ 1 μ := fun n => (hf n).toL1 (f n)
  have hC : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    change dist ((memLp_one_iff_integrable.mpr (hf m)).toLp (f m))
      ((memLp_one_iff_integrable.mpr (hf n)).toLp (f n)) < ε
    rw [dist_edist, Lp.edist_toLp_toLp, l1_eq_ofReal_integral_abs ((hf m).sub (hf n)),
      ENNReal.toReal_ofReal (integral_nonneg fun x => abs_nonneg _)]
    exact hN n m hn hm
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨w, memLp_one_iff_integrable.mp (Lp.memLp w), ?_⟩
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F w).mp hw
  apply ht.congr
  intro n
  apply eLpNorm_congr_ae
  exact (memLp_one_iff_integrable.mpr (hf n)).coeFn_toLp.sub EventuallyEq.rfl

end CoarseDeGiorgi.Weighted
