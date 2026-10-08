module

public import CoarseDeGiorgi.Whitney.Harmonic.CellId
public import CoarseDeGiorgi.Statements.WhitneyInterpolationSpec
public import CoarseDeGiorgi.Statements.WhitneyAffineExtensionDef
public import CoarseDeGiorgi.Weighted.TestingCompactSupport
public import CoarseDeGiorgi.Weighted.Lipschitz
public import CoarseDeGiorgi.Weighted.Truncation.Energy

/-! Admissibility of the piecewise harmonic extension: `H = Φ + ξ` with `ξ ∈ H¹_{a,0}`. -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

variable {d : ℕ}

instance countable_exteriorCell (τ : ℝ) : Countable (CoarseDeGiorgi.ExteriorCell d τ) := by
  have hinj : Function.Injective (fun D : TriadicCube d => (D.scale, D.index)) := by
    intro D E h
    cases D; cases E
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2; rfl
  have : Countable (TriadicCube d) := hinj.countable
  unfold CoarseDeGiorgi.ExteriorCell
  infer_instance

/-- On an open set where `Φ` is affine, its classical gradient is the constant direction. -/
theorem smoothGrad_eq_of_affine {U : Set (Vec d)} (hU : IsOpen U) {Φ : Vec d → ℝ}
    (e : Vec d) (c : ℝ) (hΦ : ∀ y ∈ U, Φ y = vecDot e y + c) :
    ∀ x ∈ U, CoarseDeGiorgi.smoothGrad Φ x = e := by
  intro x hx
  have hev : Φ =ᶠ[𝓝 x] fun y => Weighted.responseAffine e y + c := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hΦ y hy
  funext i
  change fderiv ℝ Φ x (basisVec i) = e i
  rw [hev.fderiv_eq, ((Weighted.responseAffine e).hasFDerivAt.add_const c).fderiv]
  change vecDot e (basisVec i) = e i
  simp [vecDot_basisVec_right]


open CoarseDeGiorgi.Harnack.Replacement

end CoarseDeGiorgi.Whitney.Harmonic
