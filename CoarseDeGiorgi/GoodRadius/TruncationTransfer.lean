import CoarseDeGiorgi.Selection.SurfaceMeasurability
import CoarseDeGiorgi.Statements.PositiveCap
import CoarseDeGiorgi.Statements.SurfaceFracNorm
import CoarseDeGiorgi.Statements.SurfaceMeasure

/-!
# Truncation transfer at a fixed radius (Proposition `p.good.radius`, Step 3)

At a fixed radius whose surface errors `u i - f` have a summable `r`-th power of the
surface fractional norm (and `f` has finite surface fractional norm), composing with a
one-Lipschitz map `T` keeps the surface fractional norm of the errors tending to zero,
by dominated convergence with the dominating function of the paper.
-/

namespace CoarseDeGiorgi.GoodRadius

open Homogenization MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

section Elementary

/-- The elementary three-term bound used for the dominating function. -/
theorem abs_rpow_three_le {r : ℝ} (hr : 1 ≤ r) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A + 2 * B) ^ r ≤ 3 ^ r * (A ^ r + B ^ r) := by
  have h0 : (0 : ℝ) ≤ 3 := by norm_num
  have hle : A + 2 * B ≤ 3 * max A B := by
    have := le_max_left A B; have := le_max_right A B; linarith
  calc (A + 2 * B) ^ r ≤ (3 * max A B) ^ r :=
        Real.rpow_le_rpow (by positivity) hle (by linarith)
    _ = 3 ^ r * (max A B) ^ r := Real.mul_rpow h0 (le_max_of_le_left hA)
    _ ≤ 3 ^ r * (A ^ r + B ^ r) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total A B with h | h
        · rw [max_eq_right h]
          have : 0 ≤ A ^ r := Real.rpow_nonneg hA _
          linarith
        · rw [max_eq_left h]
          have : 0 ≤ B ^ r := Real.rpow_nonneg hB _
          linarith

end Elementary

section Transfer

variable {d : ℕ}

/-- `r`-th power of the surface fractional norm as an explicit sum of two integrals. -/
theorem surfaceFracNorm_rpow_eq {τ α r : ℝ} (hr : 0 < r) {g : Vec d → ℝ} (hg : Measurable g) :
    surfaceFracNorm τ α r g ^ r =
      ∫⁻ x, ENNReal.ofReal (|g x| ^ r) ∂(surfaceMeasure (d := d) τ) +
        ∫⁻ xy, Foundations.Euclid.euclidKernel ((d : ℝ) - 1 + α * r) r g xy
          ∂((surfaceMeasure (d := d) τ).prod (surfaceMeasure (d := d) τ)) :=
  Foundations.FracGeometry.surfaceNorm_power_eq τ α hr g hg

theorem powerIntegral_le_rpow {τ α r : ℝ} (hr : 0 < r) {g : Vec d → ℝ} (hg : Measurable g) :
    ∫⁻ x, ENNReal.ofReal (|g x| ^ r) ∂(surfaceMeasure (d := d) τ) ≤
      surfaceFracNorm τ α r g ^ r := by
  rw [surfaceFracNorm_rpow_eq hr hg]; exact le_self_add

theorem kernel_le_rpow {τ α r : ℝ} (hr : 0 < r) {g : Vec d → ℝ} (hg : Measurable g) :
    ∫⁻ xy, Foundations.Euclid.euclidKernel ((d : ℝ) - 1 + α * r) r g xy
        ∂((surfaceMeasure (d := d) τ).prod (surfaceMeasure (d := d) τ)) ≤
      surfaceFracNorm τ α r g ^ r := by
  rw [surfaceFracNorm_rpow_eq hr hg]; exact le_add_self

/-- Truncation transfer: if the errors `u i - f` have summable `r`-th powers of surface
fractional norms and `f` has finite surface fractional norm, then for every one-Lipschitz `T`
the surface fractional norms of `T ∘ u i - T ∘ f` tend to zero. -/
theorem truncation_tendsto_surfaceFracNorm {τ α r : ℝ} (hr : 1 < r)
    {f : Vec d → ℝ} {u : ℕ → Vec d → ℝ} (hf : Measurable f) (hu : ∀ i, Measurable (u i))
    (T : ℝ → ℝ) (hT : ∀ x y, |T x - T y| ≤ |x - y|)
    (hfin : surfaceFracNorm τ α r f ≠ ⊤)
    (hsum : ∑' i, surfaceFracNorm τ α r (fun x => u i x - f x) ^ r ≠ ⊤) :
    Tendsto (fun i => surfaceFracNorm τ α r (fun x => T (u i x) - T (f x))) atTop (𝓝 0) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hTc : Continuous T := by
    have : LipschitzWith 1 T := LipschitzWith.of_dist_le_mul (fun x y => by
      simpa [Real.dist_eq] using hT x y)
    exact this.continuous
  set μ := surfaceMeasure (d := d) τ with hμ
  have : IsFiniteMeasure μ := by
    change IsFiniteMeasure (Foundations.FracGeometry.surfaceMeasure (d := d) τ)
    infer_instance
  let e : ℕ → Vec d → ℝ := fun i x => u i x - f x
  have he : ∀ i, Measurable (e i) := fun i => (hu i).sub hf
  let g : ℕ → Vec d → ℝ := fun i x => T (u i x) - T (f x)
  have hg : ∀ i, Measurable (g i) := fun i =>
    (hTc.measurable.comp (hu i)).sub (hTc.measurable.comp hf)
  let β : ℝ := (d : ℝ) - 1 + α * r
  let K : (Vec d → ℝ) → Vec d × Vec d → ℝ≥0∞ := Foundations.Euclid.euclidKernel β r
  have hK : ∀ w, Measurable w → Measurable (K w) := fun w hw =>
    Foundations.FracGeometry.measurable_euclidKernel β r hw
  let Pe : ℕ → ℝ≥0∞ := fun i => surfaceFracNorm τ α r (e i) ^ r
  have hPe0 : Tendsto Pe atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum
  have hge : ∀ i x, |g i x| ≤ |e i x| := fun i x => hT _ _
  -- a.e. convergence of `e i` on the surface
  have hae : ∀ᵐ x ∂μ, Tendsto (fun i => e i x) atTop (𝓝 0) := by
    have hP : ∑' i, ∫⁻ x, ENNReal.ofReal (|e i x| ^ r) ∂μ ≠ ⊤ := by
      refine ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun i => ?_)
      exact powerIntegral_le_rpow hr0 (he i)
    rw [← lintegral_tsum (fun i =>
      (Foundations.FracGeometry.measurable_power r (he i)).aemeasurable)] at hP
    have hlt := ae_lt_top (Measurable.tsum fun i =>
      Foundations.FracGeometry.measurable_power r (he i)) hP
    filter_upwards [hlt] with x hx
    have hs : Tendsto (fun i => ENNReal.ofReal (|e i x| ^ r)) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
    have h1 : Tendsto (fun i => |e i x| ^ r) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hs
      simpa only [Function.comp_def, ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) _),
        ENNReal.toReal_zero] using this
    have h2 : Tendsto (fun i => (|e i x| ^ r) ^ (1 / r)) atTop (𝓝 0) := by
      have := ((Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 1 / r)).tendsto 0).comp h1
      simpa only [Function.comp_def, Real.zero_rpow (by positivity : (1 / r : ℝ) ≠ 0)] using this
    have h3 : Tendsto (fun i => |e i x|) atTop (𝓝 0) := by
      refine h2.congr fun i => ?_
      rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hr0.ne', Real.rpow_one]
    exact tendsto_zero_iff_abs_tendsto_zero _ |>.mpr h3
  -- the power of the norm
  have hpow : Tendsto (fun i => surfaceFracNorm τ α r (g i) ^ r) atTop (𝓝 0) := by
    have hform : ∀ i, surfaceFracNorm τ α r (g i) ^ r =
        ∫⁻ x, ENNReal.ofReal (|g i x| ^ r) ∂μ +
          ∫⁻ xy, K (g i) xy ∂(μ.prod μ) := fun i => surfaceFracNorm_rpow_eq hr0 (hg i)
    simp_rw [hform]
    rw [show (0 : ℝ≥0∞) = 0 + 0 by simp]
    refine Tendsto.add ?_ ?_
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hPe0
        (fun _ => zero_le) (fun i => ?_)
      refine (lintegral_mono fun x => ?_).trans (powerIntegral_le_rpow hr0 (he i))
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) (hge i x) hr0.le)
    · have hbound_meas : Measurable (fun xy => ENNReal.ofReal (3 ^ r) *
          (K f xy + ∑' i, K (e i) xy)) :=
        (hK f hf |>.add (Measurable.tsum fun i => hK _ (he i))).const_mul _
      have hkey : ∀ i xy, K (g i) xy ≤ ENNReal.ofReal (3 ^ r) * (K f xy + K (e i) xy) := by
        intro i xy
        simp only [K, Foundations.Euclid.euclidKernel]
        set D := Foundations.Euclid.eDist2 xy.1 xy.2 ^ β with hD
        have hD0 : 0 ≤ D := Real.rpow_nonneg (Foundations.Euclid.eDist2_nonneg _ _) _
        have hpt : |g i xy.1 - g i xy.2| ≤ |e i xy.1 - e i xy.2| + 2 * |f xy.1 - f xy.2| := by
          have h1 := hT (u i xy.1) (u i xy.2)
          have h2 := hT (f xy.1) (f xy.2)
          have h3 : |u i xy.1 - u i xy.2| ≤ |e i xy.1 - e i xy.2| + |f xy.1 - f xy.2| := by
            have : u i xy.1 - u i xy.2 = (e i xy.1 - e i xy.2) + (f xy.1 - f xy.2) := by
              simp only [e]; ring
            rw [this]; exact abs_add_le _ _
          have : g i xy.1 - g i xy.2 =
              (T (u i xy.1) - T (u i xy.2)) - (T (f xy.1) - T (f xy.2)) := by
            simp only [g]; ring
          rw [this]
          calc _ ≤ |T (u i xy.1) - T (u i xy.2)| + |T (f xy.1) - T (f xy.2)| := abs_sub _ _
            _ ≤ _ := by linarith
        have hb := abs_rpow_three_le hr.le _ _ (abs_nonneg (e i xy.1 - e i xy.2))
          (abs_nonneg (f xy.1 - f xy.2))
        rw [← ENNReal.ofReal_add (div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) hD0)
          (div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) hD0),
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := Real.rpow_le_rpow (abs_nonneg _) hpt hr0.le
        calc _ ≤ (3 ^ r * (|e i xy.1 - e i xy.2| ^ r + |f xy.1 - f xy.2| ^ r)) / D :=
              div_le_div_of_nonneg_right (this.trans hb) hD0
          _ = _ := by ring
      have hdom : ∀ i, K (g i) ≤ fun xy => ENNReal.ofReal (3 ^ r) *
          (K f xy + ∑' j, K (e j) xy) := by
        intro i xy
        refine (hkey i xy).trans ?_
        show _ ≤ ENNReal.ofReal (3 ^ r) * (K f xy + ∑' j, K (e j) xy)
        gcongr
        exact ENNReal.le_tsum (f := fun j => K (e j) xy) i
      have hfinb : ∫⁻ xy, ENNReal.ofReal (3 ^ r) * (K f xy + ∑' j, K (e j) xy) ∂(μ.prod μ) ≠ ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (hK f hf),
          lintegral_tsum (fun j => (hK _ (he j)).aemeasurable)]
        refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)
        · exact ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hr0.le hfin)
            (kernel_le_rpow hr0 hf)
        · exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun j => kernel_le_rpow hr0 (he j))
      have hlim : ∀ᵐ xy ∂(μ.prod μ), Tendsto (fun i => K (g i) xy) atTop (𝓝 0) := by
        have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hae
        have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hae
        filter_upwards [h1, h2] with xy hx hy
        have hsq : Tendsto (fun i => |g i xy.1 - g i xy.2|) atTop (𝓝 0) := by
          have hs : Tendsto (fun i => |e i xy.1| + |e i xy.2|) atTop (𝓝 0) := by
            simpa using (tendsto_zero_iff_abs_tendsto_zero _ |>.mp hx).add
              (tendsto_zero_iff_abs_tendsto_zero _ |>.mp hy)
          refine squeeze_zero (fun _ => abs_nonneg _) (fun i => ?_) hs
          calc _ ≤ |g i xy.1| + |g i xy.2| := abs_sub _ _
            _ ≤ _ := add_le_add (hge _ _) (hge _ _)
        have hpw : Tendsto (fun i => |g i xy.1 - g i xy.2| ^ r) atTop (𝓝 0) := by
          have := ((Real.continuous_rpow_const hr0.le).tendsto 0).comp hsq
          simpa only [Function.comp_def, Real.zero_rpow hr0.ne'] using this
        have hdiv := hpw.div_const (Foundations.Euclid.eDist2 xy.1 xy.2 ^ β)
        have := ENNReal.tendsto_ofReal hdiv
        simp only [zero_div, ENNReal.ofReal_zero] at this
        exact this
      have := tendsto_lintegral_of_dominated_convergence _ (fun i => hK _ (hg i))
        (fun i => Eventually.of_forall (hdom i)) hfinb hlim
      simpa using this
  have hf2 := (ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0 |>.comp hpow
  simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by positivity : (0 : ℝ) < 1 / r),
    ← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one] using hf2

/-- The scalar map `y ↦ min {(y - k)₊, N}` with `min {y, ∞} = y`. -/
def capMap (k : ℝ) (N : ℝ≥0∞) (y : ℝ) : ℝ :=
  if N = ⊤ then max (y - k) 0 else min (max (y - k) 0) N.toReal

theorem positiveCap_eq_capMap {d : ℕ} (v : Vec d → ℝ) (k : ℝ) (N : ℝ≥0∞) :
    positiveCap v k N = fun x => capMap k N (v x) := by
  funext x
  simp only [positiveCap, capMap, positivePart]

theorem capMap_lipschitz (k : ℝ) (N : ℝ≥0∞) (x y : ℝ) :
    |capMap k N x - capMap k N y| ≤ |x - y| := by
  have h1 : ∀ x y : ℝ, |max (x - k) 0 - max (y - k) 0| ≤ |x - y| := by
    intro x y
    have := abs_max_sub_max_le_abs (x - k) (y - k) 0
    simpa using this
  unfold capMap
  split_ifs
  · exact h1 x y
  · have := abs_min_sub_min_le_max (max (x - k) 0) N.toReal (max (y - k) 0) N.toReal
    simp only [sub_self, abs_zero] at this
    exact (this.trans_eq (max_eq_left (abs_nonneg _))).trans (h1 x y)

/-- Step 3 at a fixed radius, for every `k` and `N`: both the fractional and the `L²` surface
convergence transfer from the approximants `u i` of `f` to all truncations. -/
theorem truncations_tendsto {τ α r : ℝ} (hr : 1 < r)
    {f : Vec d → ℝ} {u : ℕ → Vec d → ℝ} (hf : Measurable f) (hu : ∀ i, Measurable (u i))
    (hfin : surfaceFracNorm τ α r f ≠ ⊤)
    (hsum : ∑' i, surfaceFracNorm τ α r (fun x => u i x - f x) ^ r ≠ ⊤)
    (hL2 : Tendsto (fun i => eLpNorm (fun x => u i x - f x) 2 (surfaceMeasure (d := d) τ))
      atTop (𝓝 0)) (k : ℝ) (N : ℝ≥0∞) :
    Tendsto (fun i => surfaceFracNorm τ α r
      (fun x => positiveCap (u i) k N x - positiveCap f k N x)) atTop (𝓝 0) ∧
    Tendsto (fun i => eLpNorm (fun x => positiveCap (u i) k N x - positiveCap f k N x) 2
      (surfaceMeasure (d := d) τ)) atTop (𝓝 0) := by
  simp only [positiveCap_eq_capMap]
  refine ⟨truncation_tendsto_surfaceFracNorm hr hf hu (capMap k N) (capMap_lipschitz k N)
    hfin hsum, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL2
    (fun _ => zero_le) (fun i => ?_)
  have hcont : Continuous (capMap k N) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => by
      simpa [Real.dist_eq] using capMap_lipschitz k N x y)).continuous
  refine eLpNorm_mono ((hcont.measurable.comp (hu i)).sub
    (hcont.measurable.comp hf)).aestronglyMeasurable (fun x => ?_)
  simpa only [Real.norm_eq_abs] using capMap_lipschitz k N (u i x) (f x)

end Transfer

end

end CoarseDeGiorgi.GoodRadius
