import CoarseDeGiorgi.Endpoint.Potential.Equation
import CoarseDeGiorgi.Endpoint.Potential.Distribution
import CoarseDeGiorgi.Endpoint.Potential.Blocks
import CoarseDeGiorgi.Endpoint.Potential.Assembly
import CoarseDeGiorgi.Endpoint.Potential.Params
import CoarseDeGiorgi.Statements.MemH1a0
import CoarseDeGiorgi.Statements.RStarParam
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.OriginCube

namespace CoarseDeGiorgi.Endpoint.Potential

open Homogenization MeasureTheory Filter Topology CoarseDeGiorgi
open scoped ENNReal

theorem abs_truncate_ge {K t : ℝ} (hK : 0 < K) (h : K < |t|) : K ≤ |Weighted.truncate K t| := by
  unfold Weighted.truncate
  rcases lt_abs.1 h with h | h
  · rw [min_eq_right h.le, max_eq_right (by linarith), abs_of_pos hK]
  · rw [min_eq_left (by linarith), max_eq_left (by linarith), abs_neg, abs_of_pos hK]

/-- The core of `p.endpoint.potential`: the level-set argument, abstracted over the block weights `b`. -/
theorem core_bound {d : ℕ} (hd : 3 ≤ d) {q t : ℝ} (hq : 1 < q) (ht : 0 < t) (ht1 : t < 1)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {a : CoeffField d} (ha : IsWeightedCoeffOn (originCube 1) a)
    (b : ℕ → ℝ≥0∞)
    (hrec : ∀ (f : Vec d → ℝ) (Gf : Vec d → Vec d), MemH1a0 a (originCube 1) f Gf →
      ∃ vk : ℕ → Vec d → ℝ,
        Tendsto (fun N : ℕ => eLpNorm (fun x => f x - ∑ k ∈ Finset.Icc 1 N, vk k x)
          (ENNReal.ofReal (paramR q)) (volume.restrict (originCube 1))) atTop (𝓝 0) ∧
        ∀ k : ℕ, 1 ≤ k →
          AEStronglyMeasurable (vk k) (volume.restrict (originCube 1)) ∧
          eLpNorm (vk k) (ENNReal.ofReal (paramR q)) (volume.restrict (originCube 1)) ≤
            ENNReal.ofReal C₀ * ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * (1 - t)))) * b k *
              (weightedEnergy a (originCube 1) Gf).rpow (1 / 2) ∧
          eLpNorm (vk k) ⊤ (volume.restrict (originCube 1)) ≤
            ENNReal.ofReal C₀ *
              ENNReal.ofReal (Real.rpow 3 ((d : ℝ) / rStarParam (d := d) q t * (k : ℝ))) * b k *
                (weightedEnergy a (originCube 1) Gf).rpow (1 / 2))
    (ν : Measure (Vec d)) [IsFiniteMeasure ν] (hν : ν (originCube 1)ᶜ = 0)
    {v : Vec d → ℝ} (hvm : Measurable v) {Gv : Vec d → Vec d}
    (hv : MemH1a0 a (originCube 1) v Gv)
    (heq : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ originCube 1 →
      ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume =
        ∫ x, φ x ∂ν) :
    eLpNorm v (ENNReal.ofReal (rStarParam (d := d) q t / 2)) (volume.restrict (originCube 1)) ≤
      ENNReal.ofReal 2 *
        ENNReal.ofReal (C₀ * (3 : ℝ) ^ ((d : ℝ) / rStarParam (d := d) q t + (1 - t))) ^ 2 *
        (((1 - ENNReal.ofReal ((3 : ℝ) ^ (-((d : ℝ) / rStarParam (d := d) q t))))⁻¹ +
          (1 - ENNReal.ofReal ((3 : ℝ) ^ (-(1 - t))))⁻¹) * ∑' k, b k) ^ 2 *
        ν (originCube 1) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hV, hne⟩ := originCube_one_domain (d := d)
  set V := originCube (d := d) 1 with hVdef
  set μ := volume.restrict V with hμ
  have : IsFiniteMeasure μ := hV.isFiniteMeasure_restrict_volume
  obtain ⟨hg1, hrs1, hsum, hg1rs, hrlt⟩ := rStar_facts hd hq ht ht1
  set r := paramR q with hr
  set rs := rStarParam (d := d) q t with hrs
  set g₁ : ℝ := (d : ℝ) / rs with hg₁
  have hr1 : 1 < r := one_lt_paramR hq
  have hμuniv : μ Set.univ = 1 := by
    rw [hμ, Measure.restrict_apply_univ]
    exact Harnack.Scalar.volume_originCube_one
  set A : ℝ≥0∞ := ENNReal.ofReal (C₀ * (3 : ℝ) ^ (g₁ + (1 - t))) with hA
  set ρ₁ : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ (-g₁)) with hρ₁
  set ρ₂ : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ (-(1 - t))) with hρ₂
  set c : ℕ → ℝ≥0∞ := scaleSum ρ₁ ρ₂ b with hc
  set m : ℝ≥0∞ := ν V with hm
  set T : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal 2 *
    (A * ENNReal.ofReal ((3 : ℝ) ^ (g₁ * N)) * c N) ^ 2 * m with hT
  set w : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal ((((3 : ℝ) ^ d) ^ N)⁻¹) with hw
  have hlevel : ∀ K : ℝ, 0 < K →
      μ {x | K < |v x|} ≤ ∑' N, w N * (if ENNReal.ofReal K ≤ T N then 1 else 0) := by
    intro K hK
    set S : Set (Vec d) := {x | K < |v x|} with hS
    have hSm : MeasurableSet S :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp hvm)
    by_cases h0 : μ S = 0
    · rw [h0]; exact zero_le
    have hle1 : μ S ≤ 1 := hμuniv ▸ measure_mono (Set.subset_univ _)
    have hSfin : μ S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hle1
    set m' : ℝ := (μ S).toReal with hm'
    have hm'pos : 0 < m' := ENNReal.toReal_pos h0 hSfin
    have hm'1 : m' ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top hle1
      simpa using this
    have hy : (1 : ℝ) < 3 ^ d := one_lt_pow₀ (by norm_num) (by omega)
    obtain ⟨N, hN1, hN2⟩ := exists_scale hm'pos hm'1 hy
    have hμS : μ S = ENNReal.ofReal m' := (ENNReal.ofReal_toReal hSfin).symm
    have hTN : ENNReal.ofReal K ≤ T N := by
      have hfm : AEStronglyMeasurable (fun x => Weighted.truncate K (v x)) μ :=
        (Weighted.truncate_lipschitz K).continuous.comp_aestronglyMeasurable hv.1
      obtain ⟨vk, hconv, hbd⟩ := hrec _ _ (Weighted.MemH1a0.truncation hV hne ha hv hK)
      set Eh : ℝ≥0∞ := (weightedEnergy a V ({x | |v x| < K}.indicator Gv)).rpow (1 / 2) with hEhdef
      have hEh : Eh ≤ (ENNReal.ofReal (2 * K) * m) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (truncation_energy_le hV hne ha ν hν hv heq hK) (by norm_num)
      have hXpos : 0 < ((3 : ℝ) ^ d) ^ (N + 1) := by positivity
      have hinv : (μ S)⁻¹ = ENNReal.ofReal m'⁻¹ := by
        rw [hμS, ENNReal.ofReal_inv_of_pos hm'pos]
      have hm'inv : m'⁻¹ < ((3 : ℝ) ^ d) ^ (N + 1) := (inv_lt_comm₀ hXpos hm'pos).1 hN2
      have hX : (((3 : ℝ) ^ d) ^ (N + 1)) ^ (1 / r) =
          (3 : ℝ) ^ ((g₁ + (1 - t)) * ((N : ℝ) + 1)) := by
        rw [← pow_mul, ← Real.rpow_natCast (3 : ℝ) (d * (N + 1)), ← Real.rpow_mul (by norm_num),
          hsum]
        congr 1
        push_cast
        ring
      have hΘ : (μ S)⁻¹ ^ (1 / r) ≤ ENNReal.ofReal ((3 : ℝ) ^ ((g₁ + (1 - t)) * ((N : ℝ) + 1))) := by
        rw [hinv, ← hX, ← ENNReal.ofReal_rpow_of_nonneg hXpos.le (by positivity)]
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hm'inv.le) (by positivity)
      have hdist := distribution_bound μ hr1 hconv (fun k hk => (hbd k hk).1) hfm hSm
        (A := S) (K := K) (fun x hx => abs_truncate_ge hK hx) h0 N
        (ENNReal.ofReal ((3 : ℝ) ^ ((g₁ + (1 - t)) * ((N : ℝ) + 1)))) hΘ
      have hblocks := blocks_bound b (fun k => eLpNorm (vk k) ⊤ μ)
        (fun k => eLpNorm (vk k) (ENNReal.ofReal r) μ) Eh hC₀ hg1.le (by linarith)
        (fun k hk => (hbd k hk).2.2) (fun k hk => (hbd k hk).2.1) N
        (ENNReal.ofReal ((3 : ℝ) ^ ((g₁ + (1 - t)) * ((N : ℝ) + 1)))) le_rfl
      have hfin := hdist.trans hblocks
      apply quad_ineq hK
      calc ENNReal.ofReal K ≤ A * ENNReal.ofReal ((3 : ℝ) ^ (g₁ * N)) * Eh * c N := hfin
        _ = (A * ENNReal.ofReal ((3 : ℝ) ^ (g₁ * N)) * c N) * Eh := by ring
        _ ≤ _ := by gcongr
    calc μ S = ENNReal.ofReal m' := hμS
      _ ≤ w N := ENNReal.ofReal_le_ofReal hN1
      _ = w N * (if ENNReal.ofReal K ≤ T N then 1 else 0) := by simp [hTN]
      _ ≤ _ := ENNReal.le_tsum (f := fun N => w N * (if ENNReal.ofReal K ≤ T N then 1 else 0)) N
  have hη : 0 < rs / 2 := by linarith
  have h1 := lintegral_rpow_le_tsum μ hvm.aemeasurable hη w T hlevel
  have h2 := assembly_bound (d := d) hrs1 hg1rs A m c
  have hE : eLpNorm v (ENNReal.ofReal (rs / 2)) μ =
      (∫⁻ x, ENNReal.ofReal (|v x| ^ (rs / 2)) ∂μ) ^ (1 / (rs / 2)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hη).ne'
      ENNReal.ofReal_ne_top hvm.aestronglyMeasurable,
      ENNReal.toReal_ofReal hη.le]
    congr 1
    apply lintegral_congr
    intro x
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hη.le]
  have hρ₂ : ρ₂ ≤ 1 := by
    rw [hρ₂, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by linarith))
  have hcs := tsum_scaleSum_le ρ₁ ρ₂ hρ₂ b
  rw [hE]
  calc _ ≤ (∑' N, w N * T N ^ (rs / 2)) ^ (1 / (rs / 2)) := by gcongr
    _ ≤ ENNReal.ofReal 2 * A ^ 2 * (∑' N, c N) ^ 2 * m := h2
    _ ≤ _ := by gcongr

end CoarseDeGiorgi.Endpoint.Potential
