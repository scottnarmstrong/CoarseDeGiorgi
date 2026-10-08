import CoarseDeGiorgi.Whitney.Harmonic.AdmissibleWide
import CoarseDeGiorgi.Whitney.Harmonic.GlueData
import CoarseDeGiorgi.Whitney.Harmonic.Cellwise2Wide

/-! The glued Lipschitz extension and the admissible correction. -/

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

open scoped Classical in
/-- For every Lipschitz `w` on the closed cube agreeing with `f` on the surface there are a
globally Lipschitz `Φ` (equal to `w` inside and `L_h f` outside) and a correction `ξ ∈ H¹_{a,0}`
with `H_h f = Φ + ξ` off the cube. -/
theorem glued_correction (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    {a : CoeffField d} (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {f : Vec d → ℝ} (hfacts : AffFacts τ h ρ₂ hτ0 hτ1 f)
    {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH)
    {K₂ : ℝ≥0} {w : Vec d → ℝ}
    (hw : LipschitzOnWith K₂ w (CoarseDeGiorgi.closedReferenceCube (d := d) τ))
    (hwf : ∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, w y = f y) :
    ∃ (Φ : Vec d → ℝ) (K : ℝ≥0) (ξ : Vec d → ℝ) (Gξ : Vec d → Vec d),
      LipschitzWith K Φ ∧
      (∀ x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ, Φ x = w x) ∧
      MemH1a0 a (CoarseDeGiorgi.originCube 1) ξ Gξ ∧
      MemH1a0 a (CoarseDeGiorgi.originCube 1) (Φ + ξ) (CoarseDeGiorgi.smoothGrad Φ + Gξ) ∧
      (∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.originCube (d := d) 1 \
          CoarseDeGiorgi.closedReferenceCube (d := d) τ),
        H x = Φ x + ξ x ∧ GH x = CoarseDeGiorgi.smoothGrad Φ x + Gξ x) ∧
      (∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.closedReferenceCube (d := d) τ),
        ξ x = 0 ∧ Gξ x = 0) := by
  have hτpos : 0 < τ := by linarith
  obtain ⟨F, hFL, hFf, hFlip⟩ := hfacts.lipF
  obtain ⟨K, hK⟩ := exists_glued hτpos hFlip hFf hw hwf
  set Φ : Vec d → ℝ := fun x =>
    if x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ then w x else F x with hΦ
  have hΦB : ∀ x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ, Φ x = w x := fun x hx => by
    simp only [hΦ, hx, ite_true]
  have hΦL : ∀ x ∈ (CoarseDeGiorgi.closedReferenceCube (d := d) τ)ᶜ,
      Φ x = CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x := fun x hx => by
    have : x ∉ CoarseDeGiorgi.closedReferenceCube (d := d) τ := hx
    simp only [hΦ, this, ite_false]
    exact hFL x hx
  have hKcO : CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h) ⊆
      CoarseDeGiorgi.originCube 1 :=
    hfacts.suppO.trans (fun x hx i => by
      have := hx i
      constructor <;> linarith [this.1, this.2])
  have hBK : CoarseDeGiorgi.closedReferenceCube (d := d) τ ⊆
      CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h) := by
    intro x hx i
    exact (hx i).trans (by linarith)
  have hΦKc : ∀ x, x ∉ CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h) → Φ x = 0 := by
    intro x hx
    have hxB : x ∉ CoarseDeGiorgi.closedReferenceCube (d := d) τ := fun h' => hx (hBK h')
    rw [hΦL x hxB]
    by_contra hne
    exact hx (hfacts.supp (subset_closure ⟨hxB, hne⟩))
  obtain ⟨ξ, Gξ, h1, h2, h3, h4⟩ := admissible_correction hd hτ0 hτ1 hρ₂ hτρ hh hwidth a ha f hK
    hΦL hfacts.zero (isCompact_closedRef (by linarith)) hKcO hΦKc hHGH
  exact ⟨Φ, K, ξ, Gξ, hK, hΦB, h1, h2, h3, h4⟩

end CoarseDeGiorgi.Whitney.Harmonic.Wide
