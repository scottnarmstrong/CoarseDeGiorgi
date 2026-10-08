module

public import CoarseDeGiorgi.Statements.SurfaceFracNorm
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import CoarseDeGiorgi.Statements.FracKernelWithDimension
public import CoarseDeGiorgi.Statements.EuclidDist
public import CoarseDeGiorgi.Statements.FaceCoordinateMeasures
public import CoarseDeGiorgi.Statements.CubeFaceMeasure
public import CoarseDeGiorgi.Statements.SurfaceMeasure
public import CoarseDeGiorgi.LowerFractional.FractionalDifference
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open Homogenization MeasureTheory Filter Topology CoarseDeGiorgi
open scoped ENNReal

private instance trace_faceCoordinateMeasures_finite {d : ℕ} (τ : ℝ)
    (i : Fin d) (positive : Bool) (j : Fin d) :
    IsFiniteMeasure (CoarseDeGiorgi.faceCoordinateMeasures τ i positive j) := by
  unfold CoarseDeGiorgi.faceCoordinateMeasures
  split_ifs <;> infer_instance

private instance trace_cubeFaceMeasure_finite {d : ℕ} (τ : ℝ)
    (i : Fin d) (positive : Bool) :
    IsFiniteMeasure (CoarseDeGiorgi.cubeFaceMeasure τ i positive) := by
  unfold CoarseDeGiorgi.cubeFaceMeasure
  infer_instance

private instance trace_surfaceMeasure_finite {d : ℕ} (τ : ℝ) :
    IsFiniteMeasure (CoarseDeGiorgi.surfaceMeasure (d := d) τ) := by
  unfold CoarseDeGiorgi.surfaceMeasure
  infer_instance

private noncomputable def surfaceDifference {d : ℕ} (α r : ℝ)
    (f : Vec d → ℝ) (p : Vec d × Vec d) : ℝ :=
  LowerFractional.fractionalDifference (α - 1 / r) r f p

private theorem surfaceKernel_eq_enorm_rpow {d : ℕ} {α r : ℝ}
    (hr : 0 < r) (f : Vec d → ℝ) (p : Vec d × Vec d) :
    fracKernelWithDimension ((d : ℝ) - 1) α r f p =
      ‖surfaceDifference α r f p‖ₑ ^ r := by
  have hexp : ((d : ℝ) - 1) + α * r = (d : ℝ) + (α - 1 / r) * r := by
    field_simp [hr.ne']
    ring
  unfold surfaceDifference
  rw [show fracKernelWithDimension ((d : ℝ) - 1) α r f p =
      fracKernelWithDimension (d : ℝ) (α - 1 / r) r f p by
        unfold fracKernelWithDimension
        rw [hexp]]
  exact LowerFractional.fracKernel_eq_fractionalDifference (α - 1 / r) hr f p

private theorem surfaceFracSeminorm_le_surfaceFracNorm_local {d : ℕ}
    {τ α r : ℝ} (hr : 1 < r) (f : Vec d → ℝ) :
    surfaceFracSeminorm τ α r f ≤ surfaceFracNorm τ α r f := by
  unfold CoarseDeGiorgi.surfaceFracNorm
  have hbase : surfaceFracSeminorm τ α r f ^ r ≤
      eLpNorm f (ENNReal.ofReal r) (surfaceMeasure τ) ^ r +
        surfaceFracSeminorm τ α r f ^ r := le_add_left le_rfl
  have h := ENNReal.rpow_le_rpow hbase (show 0 ≤ 1 / r by positivity)
  simpa only [ENNReal.rpow_eq_pow, ← ENNReal.rpow_mul,
    mul_one_div_cancel (zero_lt_one.trans hr).ne', ENNReal.rpow_one] using h

private theorem surfaceFracSeminorm_eq_eLpNorm_local {d : ℕ} {τ α r : ℝ}
    (hr : 0 < r) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (surfaceMeasure τ)) :
    surfaceFracSeminorm τ α r f =
      eLpNorm (surfaceDifference α r f) (ENNReal.ofReal r)
        ((surfaceMeasure τ).prod (surfaceMeasure τ)) := by
  unfold surfaceDifference
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top
    (LowerFractional.fractionalDifference_aestronglyMeasurable
      hf (α - 1 / r) r)]
  rw [ENNReal.toReal_ofReal hr.le]
  unfold CoarseDeGiorgi.surfaceFracSeminorm
  congr 1
  apply lintegral_congr
  intro p
  exact surfaceKernel_eq_enorm_rpow hr f p

private theorem surfaceFracSeminorm_add_le_local {d : ℕ} {τ α r : ℝ}
    (hr : 1 ≤ r) {f g : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (surfaceMeasure τ))
    (hg : AEStronglyMeasurable g (surfaceMeasure τ)) :
    surfaceFracSeminorm τ α r (f + g) ≤
      surfaceFracSeminorm τ α r f + surfaceFracSeminorm τ α r g := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [surfaceFracSeminorm_eq_eLpNorm_local hr0 (hf.add hg),
    surfaceFracSeminorm_eq_eLpNorm_local hr0 hf,
    surfaceFracSeminorm_eq_eLpNorm_local hr0 hg]
  have hlinear : surfaceDifference α r (f + g) =
      surfaceDifference α r f + surfaceDifference α r g := by
    funext p
    simp [surfaceDifference, LowerFractional.fractionalDifference, Pi.add_apply]
    ring
  rw [hlinear]
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr
  exact eLpNorm_add_le hp

/-- Convergence in the surface norm `surfaceFracNorm` gives an arbitrarily sharp eventual
upper bound for the fractional seminorm. -/
theorem surfaceFracSeminorm_eventually_close_of_tendsto
    {d : ℕ} {τ α r : ℝ} (hr : 1 < r)
    (w : Vec d → ℝ) (vi : ℕ → Vec d → ℝ)
    (hw : AEStronglyMeasurable w (surfaceMeasure τ))
    (hvi : ∀ i, AEStronglyMeasurable (vi i) (surfaceMeasure τ))
    (hfinite : surfaceFracSeminorm τ α r w < ⊤)
    (herror : Tendsto (fun i => surfaceFracNorm τ α r (vi i - w)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      surfaceFracSeminorm τ α r (vi i) ≤
        surfaceFracSeminorm τ α r w + ENNReal.ofReal ε := by
  have _hfinite := hfinite
  intro ε hε
  have hεnorm : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hsmall : ∀ᶠ i in atTop,
      surfaceFracNorm τ α r (vi i - w) < ENNReal.ofReal ε :=
    (tendsto_order.1 herror).2 (ENNReal.ofReal ε) hεnorm
  filter_upwards [hsmall] with i hi
  have htriangle : surfaceFracSeminorm τ α r (vi i) ≤
      surfaceFracSeminorm τ α r w + surfaceFracSeminorm τ α r (vi i - w) := by
    have hfun : vi i = w + (vi i - w) := by
      ext x
      simp
    calc
      surfaceFracSeminorm τ α r (vi i) =
          surfaceFracSeminorm τ α r (w + (vi i - w)) := congrArg _ hfun
      _ ≤ surfaceFracSeminorm τ α r w + surfaceFracSeminorm τ α r (vi i - w) :=
        surfaceFracSeminorm_add_le_local hr.le hw ((hvi i).sub hw)
  have herr : surfaceFracSeminorm τ α r (vi i - w) ≤
      surfaceFracNorm τ α r (vi i - w) :=
    surfaceFracSeminorm_le_surfaceFracNorm_local hr (vi i - w)
  calc
    surfaceFracSeminorm τ α r (vi i) ≤
        surfaceFracSeminorm τ α r w + surfaceFracNorm τ α r (vi i - w) := by
      exact htriangle.trans (by gcongr)
    _ ≤ surfaceFracSeminorm τ α r w + ENNReal.ofReal ε := by gcongr

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
