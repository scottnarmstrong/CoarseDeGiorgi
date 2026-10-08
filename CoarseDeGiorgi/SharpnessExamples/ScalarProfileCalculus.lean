module

public import CoarseDeGiorgi.SharpnessExamples.ScalarProfile
public import Mathlib.Topology.Piecewise

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open scoped ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- Derivative of the annular radial harmonic branch. -/
theorem scalarAnnularProfile_hasDerivAt (d : ℕ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (scalarAnnularProfile d)
      (-cylinderRadialConstant d * Real.rpow r (2 - (d : ℝ))) r := by
  let f : ℝ → ℝ := fun z => Real.rpow z (2 - (d : ℝ))
  have hf : IntervalIntegrable f volume r 2 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    left
    have hpos : 0 < x := (lt_min hr (by norm_num : (0 : ℝ) < 2)).trans_le hx.1
    exact ne_of_gt hpos
  have hfc : ContinuousAt f r := by
    exact continuousAt_id.rpow_const (Or.inl hr.ne')
  have hfm : StronglyMeasurableAtFilter f (𝓝 r) volume := by
    have hm : Measurable f := by
      exact (measurable_id.pow measurable_const : Measurable (fun z : ℝ => z ^ (2 - (d : ℝ))))
    exact hm.stronglyMeasurable.stronglyMeasurableAtFilter
  have hderiv := (intervalIntegral.integral_hasDerivAt_left hf hfm hfc).const_mul
    (cylinderRadialConstant d)
  convert hderiv using 1
  · rfl
  · dsimp [f]
    ring

/-- Both interfaces use the continuous profile values. -/
theorem scalarRadialProfile_continuous {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) : Continuous (scalarRadialProfile d n ζ) := by
  classical
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  have hε : 0 < ε := (cylinderRadius_data hd hζ0 hζ2 (cylinderRadialConstant_pos hd)
    (d := d) (n := n)).1
  let A : ℝ → ℝ := fun r => scalarAnnularProfile d (max r ε / ε)
  have hA : Continuous A := by
    apply continuous_iff_continuousAt.mpr
    intro r
    have harg : 0 < max r ε / ε := div_pos (hε.trans_le (le_max_right _ _)) hε
    change ContinuousAt (fun t : ℝ => scalarAnnularProfile d (max t ε / ε)) r
    have hargcont : ContinuousAt (fun t : ℝ => max t ε / ε) r := by fun_prop
    exact (scalarAnnularProfile_hasDerivAt d harg).continuousAt.comp
      (f := fun t : ℝ => max t ε / ε) hargcont
  let B : ℝ → ℝ := fun r => if r < 2 * ε then A r else 0
  have hB : Continuous B := by
    apply hA.if ?_ continuous_const
    intro r hr
    have hr' : r = 2 * ε := by simpa only [show {r : ℝ | r < 2 * ε} = Iio (2 * ε) by rfl,
      frontier_Iio, mem_singleton_iff] using hr
    subst r
    dsimp [A]
    have hmax : max (2 * ε) ε = 2 * ε := max_eq_left (by linarith)
    rw [hmax, mul_div_cancel_right₀ _ hε.ne', scalarAnnularProfile_two]
  let C : ℝ → ℝ := fun r => 1 + scalarProfileXi d n ζ * (1 - (max r 0) ^ 2 / ε ^ 2)
  have hC : Continuous C := by dsimp [C]; fun_prop
  have hCB : Continuous (fun r => if r ≤ ε then C r else B r) := by
    apply hC.if ?_ hB
    intro r hr
    have hr' : r = ε := by simpa only [show {r : ℝ | r ≤ ε} = Iic ε by rfl,
      frontier_Iic, mem_singleton_iff] using hr
    subst r
    have hmax : max ε 0 = ε := max_eq_left hε.le
    have hmax' : max ε ε = ε := max_self _
    have hsmall : ε < 2 * ε := by linarith
    simp only [C, B, A, hsmall, ↓reduceIte, hmax, hmax', div_self (sq_pos_of_pos hε).ne',
      div_self hε.ne', sub_self, mul_zero, add_zero, scalarAnnularProfile_one hd]
  convert hCB using 1
  funext r
  by_cases hr : r ≤ ε
  · simp [scalarRadialProfile, C, hr, ε]
  · have hr' : ε ≤ r := le_of_not_ge hr
    simp [scalarRadialProfile, B, A, hr, max_eq_left hr', C, ε]

/-- First derivative of the axial cosh factor. -/
def scalarAxialDerivative (d n : ℕ) (ζ t : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) / (1 + scalarProfileXi d n ζ) *
    cylinderRate d n (cylinderRadialConstant d) *
      Real.sinh (cylinderRate d n (cylinderRadialConstant d) * t)

theorem scalarAxialProfile_hasDerivAt (d n : ℕ) (ζ t : ℝ) :
    HasDerivAt (scalarAxialProfile d n ζ) (scalarAxialDerivative d n ζ t) t := by
  have h := (Real.hasDerivAt_cosh (cylinderRate d n (cylinderRadialConstant d) * t)).comp t
    ((hasDerivAt_id t).const_mul (cylinderRate d n (cylinderRadialConstant d)))
  convert h.const_mul (((n + 1 : ℕ) : ℝ) / (1 + scalarProfileXi d n ζ)) using 1
  · rfl
  · dsimp [scalarAxialProfile, scalarAxialDerivative]
    ring

theorem scalarAxialDerivative_hasDerivAt (d n : ℕ) (ζ t : ℝ) :
    HasDerivAt (scalarAxialDerivative d n ζ)
      ((cylinderRate d n (cylinderRadialConstant d)) ^ 2 * scalarAxialProfile d n ζ t) t := by
  have h := (Real.hasDerivAt_sinh (cylinderRate d n (cylinderRadialConstant d) * t)).comp t
    ((hasDerivAt_id t).const_mul (cylinderRate d n (cylinderRadialConstant d)))
  convert h.const_mul ((((n + 1 : ℕ) : ℝ) / (1 + scalarProfileXi d n ζ)) *
    cylinderRate d n (cylinderRadialConstant d)) using 1
  · rfl
  · dsimp [scalarAxialProfile, scalarAxialDerivative]
    ring

/-- The core transverse Laplacian cancels the axial rate at profile value one. -/
theorem scalarCore_curvature_eq_rate {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    2 * ((d : ℝ) - 1) * scalarProfileXi d n ζ /
        (cylinderRadius d n ζ (cylinderRadialConstant d)) ^ 2 =
      (cylinderRate d n (cylinderRadialConstant d)) ^ 2 := by
  have hε := (cylinderRadius_data hd hζ0 hζ2 (cylinderRadialConstant_pos hd)
    (d := d) (n := n)).1
  have hκ := cylinderRadialConstant_pos hd
  have hdim : 0 ≤ ((d : ℝ) - 1) * cylinderRadialConstant d := by
    have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    exact mul_nonneg (by linarith) hκ.le
  unfold scalarProfileXi cylinderRate
  simp only [div_pow]
  rw [Real.sq_sqrt hdim]
  field_simp [hε.ne', (cylinderB_pos n).ne']

/-- Classical core derivative away from the inner interface and radial origin. -/
theorem scalarRadialProfile_core_hasDerivAt {d : ℕ} {n : ℕ} {ζ r : ℝ}
    (hr0 : 0 < r)
    (hr : r < cylinderRadius d n ζ (cylinderRadialConstant d)) :
    HasDerivAt (scalarRadialProfile d n ζ)
      (-2 * scalarProfileXi d n ζ * r /
        (cylinderRadius d n ζ (cylinderRadialConstant d)) ^ 2) r := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  have hq := ((hasDerivAt_const r (1 : ℝ)).sub
    ((hasDerivAt_pow 2 r).div_const (ε ^ 2))).const_mul (scalarProfileXi d n ζ)
  have hq' := (hasDerivAt_const r (1 : ℝ)).add hq
  have hlocal : scalarRadialProfile d n ζ =ᶠ[𝓝 r]
      (fun t => 1 + scalarProfileXi d n ζ * (1 - t ^ 2 / ε ^ 2)) := by
    filter_upwards [Ioo_mem_nhds hr0 hr] with t ht
    have htε : t ≤ cylinderRadius d n ζ (cylinderRadialConstant d) := ht.2.le
    simp [scalarRadialProfile, htε, max_eq_left ht.1.le, ε]
  apply HasDerivAt.congr_of_eventuallyEq _ hlocal
  convert hq' using 1
  ring

/-- Classical annular derivative in the open annulus. -/
theorem scalarRadialProfile_annulus_hasDerivAt {d : ℕ} (hd : 3 ≤ d)
    {n : ℕ} {ζ r : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hr1 : cylinderRadius d n ζ (cylinderRadialConstant d) < r)
    (hr2 : r < 2 * cylinderRadius d n ζ (cylinderRadialConstant d)) :
    HasDerivAt (scalarRadialProfile d n ζ)
      (-cylinderRadialConstant d / cylinderRadius d n ζ (cylinderRadialConstant d) *
        Real.rpow (r / cylinderRadius d n ζ (cylinderRadialConstant d)) (2 - (d : ℝ))) r := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  have hε : 0 < ε := (cylinderRadius_data hd hζ0 hζ2 (cylinderRadialConstant_pos hd)
    (d := d) (n := n)).1
  have hratio : 0 < r / ε := div_pos (hε.trans hr1) hε
  have hq := (scalarAnnularProfile_hasDerivAt d hratio).comp r
    ((hasDerivAt_id r).div_const ε)
  have hlocal : scalarRadialProfile d n ζ =ᶠ[𝓝 r]
      (fun t => scalarAnnularProfile d (t / ε)) := by
    filter_upwards [Ioo_mem_nhds hr1 hr2] with t ht
    simp [scalarRadialProfile, not_le.mpr ht.1, ht.2, ε]
  apply HasDerivAt.congr_of_eventuallyEq _ hlocal
  convert hq using 1
  · rfl
  · dsimp [ε]
    ring

/-- Equality of the inward and outward scalar fluxes at the inner interface. -/
theorem scalarProfile_inner_flux_match {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    scalarCoreValue d n ζ (cylinderRadialConstant d) *
        (-2 * scalarProfileXi d n ζ / cylinderRadius d n ζ (cylinderRadialConstant d)) =
      scalarAnnulusValue d n ζ (cylinderRadialConstant d) *
        (-cylinderRadialConstant d / cylinderRadius d n ζ (cylinderRadialConstant d)) := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  have hε : 0 < ε := (cylinderRadius_data hd hζ0 hζ2 (cylinderRadialConstant_pos hd)
    (d := d) (n := n)).1
  have hp : Real.rpow ε (-ζ) * ε ^ 2 = Real.rpow ε (2 - ζ) := by
    calc
      _ = Real.rpow ε (-ζ) * Real.rpow ε (2 : ℝ) := by
        exact congrArg (fun t => Real.rpow ε (-ζ) * t) (Real.rpow_natCast ε 2).symm
      _ = Real.rpow ε (-ζ + 2) := (Real.rpow_add hε _ _).symm
      _ = _ := by congr 1; ring
  unfold scalarCoreValue scalarAnnulusValue scalarProfileXi
  change (cylinderB n * Real.rpow ε (-ζ)) *
      (-2 * (cylinderRadialConstant d / 2 * (ε / cylinderB n) ^ 2) / ε) =
    (cylinderB n)⁻¹ * Real.rpow ε (2 - ζ) * (-cylinderRadialConstant d / ε)
  rw [← hp]
  field_simp [(cylinderB_pos n).ne', hε.ne']

end

end CoarseDeGiorgi.SharpnessExamples
