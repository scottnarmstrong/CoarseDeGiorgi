module

public import CoarseDeGiorgi.PowerCacc.Glue
public import CoarseDeGiorgi.Weighted.Testing

/-! # Testing a subsolution with the glued extension of Proposition `p.whitney.extension`

For a weighted subsolution `(u, G)` on `□₀` and the function `ψ` equal to `f` on `τ□̄₀` and to the
exterior extension `Hx` outside, the testing inequality reads
`∫_{τ□₀} ∇f · a G ≤ |∫_{□₀ ∖ τ□̄₀} ∇Hx · a G|`.  The gradient of `ψ` is identified with `Fg` inside and
with `GHx` outside by uniqueness of weak gradients. -/

@[expose] public section

namespace CoarseDeGiorgi.GoodRadiusEnergy

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal Classical

variable {d : ℕ}

theorem glued_test_inner_le [NeZero d] {a : CoeffField d}
    (ha : IsWeightedCoeffOn (originCube 1) a)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSubsolution a (originCube 1) u G)
    {τ R : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {f : Vec d → ℝ} {Fg : Vec d → Vec d}
    (hf : MemH1a a (originCube 1) f Fg) (hf0 : ∀ x, 0 ≤ f x)
    (hfL : ∃ K : ℝ≥0, LipschitzOnWith K f (closedReferenceCube (d := d) τ))
    {Hx : Vec d → ℝ} {GHx : Vec d → Vec d}
    (hGHint : Integrable GHx
      (volume.restrict (originCube (d := d) 1 \ closedReferenceCube τ)))
    (hHw : HasWeakGradientOn (originCube (d := d) 1 \ closedReferenceCube τ) Hx GHx)
    (hglue : ∀ w : Vec d → ℝ,
      (∃ K : ℝ≥0, LipschitzOnWith K w (closedReferenceCube (d := d) τ)) →
      (∀ y ∈ cubeSurface (d := d) τ, w y = f y) →
      ∃ G' : Vec d → Vec d,
        MemH1a0 a (originCube (d := d) 1)
          (fun x => if x ∈ closedReferenceCube (d := d) τ then w x else Hx x) G' ∧
        (∃ K : Set (Vec d), IsCompact K ∧ K ⊆ originCube (d := d) R ∧
          ∀ᵐ x ∂volume, x ∉ K →
            (if x ∈ closedReferenceCube (d := d) τ then w x else Hx x) = 0) ∧
        ((∀ x ∈ closedReferenceCube (d := d) τ, 0 ≤ w x) →
          ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)),
            0 ≤ (if x ∈ closedReferenceCube (d := d) τ then w x else Hx x))) :
    (∫ x in originCube τ, vecDot (Fg x) (matVecMul (a x) (G x))) ≤
      |∫ x in originCube 1 \ closedReferenceCube τ,
        vecDot (GHx x) (matVecMul (a x) (G x))| := by
  obtain ⟨hV, hne⟩ := Assembly.theoremA_unitCube_domain d
  have hsub : originCube (d := d) τ ⊆ originCube 1 := by
    intro x hx i
    have := hx i
    constructor <;> linarith [this.1, this.2]
  have hU : IsOpenBoundedConvexDomain (originCube (d := d) τ) :=
    Whitney.source_cube_domain hτ0
  obtain ⟨G', hψ, -, hnn⟩ := hglue f hfL (fun _ _ => rfl)
  set ψ : Vec d → ℝ := fun x => if x ∈ closedReferenceCube (d := d) τ then f x else Hx x
    with hψdef
  have hψnn := hnn (fun x _ => hf0 x)
  obtain ⟨hint, htest⟩ := Weighted.IsWeightedSubsolution.testing hV hne ha hu hψ hψnn
  have hψW := Weighted.memH1a_memW11 hV hne ha (Weighted.MemH1a0.memH1a ha hψ)
  have hfW := Weighted.memH1a_memW11 hV hne ha hf
  have hinner : G' =ᵐ[volume.restrict (originCube τ)] Fg := by
    refine PowerCacc.gradient_ae_eq_on_open (PowerCacc.isOpen_originCube τ) hsub hψW.2.2.1 hψW.2.1
      (HasWeakGradientOn.restrict (PowerCacc.isOpen_originCube τ) hsub hfW.2.2.1)
      (fun i => (hfW.2.1 i).mono_set hsub) ?_
    intro x hx
    simp only [hψdef, ite_eq_left (PowerCacc.originCube_subset_closedReferenceCube τ hx)]
  have houter : G' =ᵐ[volume.restrict (originCube 1 \ closedReferenceCube τ)] GHx := by
    refine PowerCacc.gradient_ae_eq_on_open PowerCacc.isOpen_exterior sdiff_subset hψW.2.2.1
      hψW.2.1 hHw (fun i => (hGHint.eval i)) ?_
    intro x hx
    simp only [hψdef, ite_eq_right hx.2]
  have he := setIntegral_sdiff (μ := volume) ((PowerCacc.isOpen_originCube τ).measurableSet) hint hsub
  have hleftInner : (∫ x in originCube τ, vecDot (G' x) (matVecMul (a x) (G x))) =
      ∫ x in originCube τ, vecDot (Fg x) (matVecMul (a x) (G x)) := by
    apply integral_congr_ae
    filter_upwards [hinner] with x hx
    rw [hx]
  have hleftOuter : (∫ x in originCube 1 \ originCube τ,
      vecDot (G' x) (matVecMul (a x) (G x))) =
      ∫ x in originCube 1 \ closedReferenceCube τ,
        vecDot (GHx x) (matVecMul (a x) (G x)) := by
    rw [PowerCacc.integral_exterior_closedReferenceCube hτ0 _ hU]
    apply integral_congr_ae
    filter_upwards [houter] with x hx
    rw [hx]
  rw [hleftInner, hleftOuter] at he
  have habs := neg_le_abs (∫ x in originCube 1 \ closedReferenceCube τ,
    vecDot (GHx x) (matVecMul (a x) (G x)))
  linarith only [he, htest, habs]

end CoarseDeGiorgi.GoodRadiusEnergy
