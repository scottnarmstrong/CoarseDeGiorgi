module

public import CoarseDeGiorgi.SharpnessExamples.ScalarFluxDefs
public import CoarseDeGiorgi.SharpnessExamples.ScalarTest

/-! # Lipschitz transverse coordinates of the cutoff flux -/

@[expose] public section

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Sharpness
open scoped NNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem lipschitzOn_real_bounded {d : ℕ} {V : Set (Vec d)}
    (hV : Bornology.IsBounded V) {f : Vec d → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f V) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ V, |f x| ≤ M := by
  obtain ⟨E, hE, heq⟩ := hf.extend_real
  obtain ⟨C, hC⟩ := (hE.isBounded_image hV).exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hb := hC (E x) (Set.mem_image_of_mem E hx)
  rw [heq hx]
  have hb' : |E x| ≤ C := by simpa only [Real.norm_eq_abs] using hb
  exact hb'.trans (le_max_left _ _)

/-- Products of real Lipschitz functions remain Lipschitz on a bounded set. -/
theorem exists_lipschitzOn_real_mul {d : ℕ} {V : Set (Vec d)}
    (hV : Bornology.IsBounded V) {f g : Vec d → ℝ} {K L : ℝ≥0}
    (hf : LipschitzOnWith K f V) (hg : LipschitzOnWith L g V) :
    ∃ J : ℝ≥0, LipschitzOnWith J (fun x => f x * g x) V := by
  obtain ⟨M, hM0, hM⟩ := lipschitzOn_real_bounded hV hf
  obtain ⟨N, hN0, hN⟩ := lipschitzOn_real_bounded hV hg
  let C : ℝ := N * (K : ℝ) + M * (L : ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨Real.toNNReal C, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hFx : |f x - f y| ≤ (K : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using hf.dist_le_mul x hx y hy
  have hGx : |g x - g y| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using hg.dist_le_mul x hx y hy
  rw [Real.dist_eq, Real.coe_toNNReal _ hC]
  calc
    _ = |(f x - f y) * g x + f y * (g x - g y)| := by congr 1; ring
    _ ≤ |(f x - f y) * g x| + |f y * (g x - g y)| := abs_add_le _ _
    _ = |f x - f y| * |g x| + |f y| * |g x - g y| := by rw [abs_mul, abs_mul]
    _ ≤ ((K : ℝ) * dist x y) * N + M * ((L : ℝ) * dist x y) :=
      add_le_add (mul_le_mul hFx (hN x hx) (abs_nonneg _) (by positivity))
        (mul_le_mul (hM y hy) hGx (abs_nonneg _) hM0)
    _ = C * dist x y := by dsimp [C]; ring

theorem contDiff_exists_lipschitzOn_cube {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (1 : WithTop ℕ∞) f) :
    ∃ K : ℝ≥0, LipschitzOnWith K f (originCube 1) := by
  have hV := Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by simp)
    hV.convex.closure hV.isBoundedDomain.isBounded.isCompact_closure
  exact ⟨K, hK.mono subset_closure⟩

/-- Only the transverse flux coordinates need Lipschitz regularity across
the inner sphere; the matching radial factor provides it. -/
theorem scalarCutoffFlux_transverse_exists_lipschitzOn {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) (n : ℕ) (ζ δ : ℝ) {i : Fin d} (hi : i ≠ 0) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fun x => scalarCutoffFlux n ζ δ x i) (originCube 1) := by
  let c := cylinderCenter (d := d) (cylinderB n)
  let ρ : Vec d → ℝ := fun x => transverseNorm (x - c)
  let X : Vec d → ℝ := fun x => scalarAxialProfile d n ζ (x 0)
  have hV := Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨KX, hX⟩ := contDiff_exists_lipschitzOn_cube (f := X) (by
    dsimp [X, scalarAxialProfile]
    fun_prop)
  obtain ⟨KH, hH⟩ := scalarRadialFluxFactor_exists_lipschitz hd n ζ
  obtain ⟨KC, hC⟩ := scalarOuterFluxCutoff_exists_lipschitz
    (cylinderRadius d n ζ (cylinderRadialConstant d)) δ
  have hρ := scalarShiftedRadius_lipschitz (d := d) c
  have hHρ := hH.comp hρ
  have hCρ := hC.comp hρ
  obtain ⟨K1, h1⟩ := exists_lipschitzOn_real_mul hV.isBoundedDomain.isBounded hX hHρ.lipschitzOnWith
  obtain ⟨K2, h2⟩ := exists_lipschitzOn_real_mul hV.isBoundedDomain.isBounded h1 hCρ.lipschitzOnWith
  obtain ⟨KY, hY⟩ := contDiff_exists_lipschitzOn_cube (f := fun x : Vec d => (x - c) i) (by fun_prop)
  obtain ⟨K3, h3⟩ := exists_lipschitzOn_real_mul hV.isBoundedDomain.isBounded h2 hY
  refine ⟨K3, ?_⟩
  have heq : (fun x => scalarCutoffFlux n ζ δ x i) =
      fun x => X x * scalarRadialFluxFactor d n ζ (ρ x) *
        scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ (ρ x) * (x - c) i := by
    funext x
    simp only [scalarCutoffFlux, ite_eq_right hi]
    rfl
  rw [heq]
  simpa only [Function.comp_def] using h3

end

end CoarseDeGiorgi.SharpnessExamples
