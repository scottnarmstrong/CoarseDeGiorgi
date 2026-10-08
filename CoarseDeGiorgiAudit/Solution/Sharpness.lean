module

public import Mathlib
public import CoarseDeGiorgi.Statements.Sharpness
public import CoarseDeGiorgiAudit.Solution.BridgeBesov

/-!
# Theorem F (Sharpness of the range)

Let `d ≥ 3`, `1 < ξ, ζ < ∞` and `α, β ≥ 0` with
`θ₀ = 1 − (α+β)/2 − (d−1)/2 · (1/ξ + 1/ζ) ≤ 0`. Writing `x = (x₁, y)` with
`y ∈ ℝ^(d−1)`, there is a positive Borel function `a`, depending only on `y`
(that is, not on the first coordinate `x 0`), such that `𝐚(x) = a(y) I`
satisfies `tr 𝐚, tr 𝐚⁻¹ ∈ L¹(□₀)`, and a weak solution `u` of `∇·𝐚∇u = 0` in `□₀`
with `u ≥ 1` almost everywhere. The coefficient has finite cube quasi-norm (1.12)
`‖𝐚‖_{B̊^{-α}_{ξ,1/2}(□₀)} < ∞` if `α > 0` (order `s = α/2`, integrability `ξ`),
and `‖𝐚‖_{L^ξ(□₀)} < ∞` if `α = 0`; likewise `𝐚⁻¹` with `β`, `ζ`. Moreover
`ess sup_{□₀/2} u = ∞`, `0 < ess inf_{□₀/2} u < ∞`, and `u` is essentially
unbounded in every neighbourhood of every point `(x₁, 0)` with `|x₁| < 1/2`.

The cube quasi-norm is defined in this file as
`‖b‖ = (∑_{k ≥ 0} 3^{-ks} (avg_{z ∈ 3^{-k}ℤ^d ∩ □₀} |(b)_{z + □_{-k}}|^p)^{1/(2p)})²`,
`□_{-k} = 3^{-k} □₀`, `(b)_U` the entrywise average and `|·|` the operator norm.
Weak solutions are defined by the smooth-core closure `H¹ₐ` and the flux
equation against smooth compactly supported tests.
-/

@[expose] public section

open MeasureTheory Topology
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.Sharpness

attribute [-instance] Homogenization.instMeasurableSpaceVec

/-! ## Ambient space and cubes -/

/-- Vectors in the ambient space `ℝᵈ`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on ambient vectors. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The open cube `(-ρ/2, ρ/2)ᵈ`. -/
def originCube {d : ℕ} (ρ : ℝ) : Set (Vec d) :=
  {x | ∀ i, (-(ρ / 2)) < x i ∧ x i < ρ / 2}

/-! ## Coefficient fields -/

/-- A coefficient field assigns a real matrix to each point. -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

/-- A weighted coefficient is measurable and positive definite a.e.; its trace
and inverse trace are integrable on the domain. -/
def IsWeightedCoeffOn {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) : Prop :=
  AEStronglyMeasurable a (volume.restrict V) ∧
    (∀ᵐ x ∂(volume.restrict V), (a x).PosDef) ∧
    Integrable (fun x => (a x).trace) (volume.restrict V) ∧
    Integrable (fun x => ((a x)⁻¹).trace) (volume.restrict V)

/-! ## Averages and energies -/

/-- The weighted energy `∫_U G·aG`, as an extended nonnegative real. -/
noncomputable def weightedEnergy {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal (G x ⬝ᵥ ((a x) *ᵥ G x))

/-- The normalized volume average `⨍_U f = |U|⁻¹ ∫_U f`. -/
noncomputable def averageOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, f x ∂volume

/-! ## The weighted space `H¹ₐ` -/

/-- The coordinate gradient `(∇φ x)ᵢ = Dφ(x)eᵢ`. -/
noncomputable def smoothGrad {d : ℕ} (φ : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => fderiv ℝ φ x (Pi.single i (1 : ℝ))

/-- A smooth-core function is smooth on `V`, integrable there, and has finite
weighted energy. -/
noncomputable def IsSmoothCore {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) φ V ∧
    Integrable φ (volume.restrict V) ∧
    weightedEnergy a V (smoothGrad φ) < ⊤

/-- `H¹ₐ(V)` is the smooth-core closure in squared mean plus weighted energy;
approximants converge locally in `L¹` and their gradients converge in energy. -/
noncomputable def MemH1a {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  AEStronglyMeasurable u (volume.restrict V) ∧
    AEStronglyMeasurable G (volume.restrict V) ∧
    ∃ φ : ℕ → Vec d → ℝ,
      (∀ n, IsSmoothCore a V (φ n)) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
          ENNReal.ofReal ((averageOn V (fun x => φ n x - φ m x)) ^ 2) +
            weightedEnergy a V
              (fun x => smoothGrad (φ n) x - smoothGrad (φ m) x) <
            ENNReal.ofReal ε) ∧
      (∀ K : Set (Vec d), IsCompact K → K ⊆ V →
        Filter.Tendsto
          (fun n => ∫⁻ x in K, ‖φ n x - u x‖ₑ)
          Filter.atTop (nhds (0 : ENNReal))) ∧
      Filter.Tendsto
        (fun n => weightedEnergy a V (fun x => smoothGrad (φ n) x - G x))
        Filter.atTop (nhds (0 : ENNReal))

/-! ## Weighted solutions -/

/-- A weighted solution has zero flux pairing with every smooth compactly
supported test: `∫_V ∇φ·a∇u = 0`. -/
noncomputable def IsWeightedSolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      Integrable
        (fun x => smoothGrad φ x ⬝ᵥ ((a x) *ᵥ G x))
        (volume.restrict V) ∧
      ∫ x in V, smoothGrad φ x ⬝ᵥ ((a x) *ᵥ G x) ∂volume = 0

/-! ## Essential infimum -/

/-- Essential infimum of the nonnegative lift of `u` on `V`
(equal to `ess inf u` when `u ≥ 0` a.e.). -/
noncomputable def nonnegativeEssInf {d : ℕ}
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict V)

/-! ## Cube quasi-norm (1.12) -/

/-- Center the grid index by `j ↦ j − (3^k−1)/2`; the points `3^{-k} • gridOffset k j`
are the `3^{kd}` points of `3^{-k}ℤ^d ∩ □₀`. -/
def gridOffset {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Fin d → ℤ :=
  fun i => (j i : ℤ) - (((3 ^ k - 1) / 2 : ℕ) : ℤ)

/-- Entrywise volume average of a matrix field over `V`. -/
noncomputable def volumeAverageMat {d : ℕ} (V : Set (Vec d))
    (b : CoeffField d) : Mat d :=
  fun i j => averageOn V (fun x => b x i j)

/-- The cube quasi-norm (1.12) of order `-2s` and integrability `p`, for `s > 0`,
`1 ≤ p < ∞`:
`(∑_{k ≥ 0} 3^{-ks} (avg_{z ∈ 3^{-k}ℤ^d ∩ □₀} |(b)_{z + □_{-k}}|^p)^{1/(2p)})²`
with `□_{-k} = 3^{-k} □₀`, `|·|` the operator norm; a value in `[0,∞]`. -/
noncomputable def cubeQuasiNorm {d : ℕ} (b : CoeffField d) (s p : ℝ) : ℝ≥0∞ := by
  classical
  exact
    (∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal
          ((∑ j : Fin d → Fin (3 ^ k),
              Real.rpow ‖volumeAverageMat
                {x : Vec d | x - (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) ∈
                  originCube ((3 : ℝ) ^ (-(k : ℤ)))} b‖ p) /
            ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ))).rpow
              (1 / (2 * p))) ^ 2

/-! ## Theorem F -/

/-- **Theorem F (Sharpness of the range).** See the module docstring. -/
theorem sharpness
    -- parameters
    (d : ℕ) (_hd : 3 ≤ d) (ξ ζ α β : ℝ)
    (hξ : 1 < ξ) (hζ : 1 < ζ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (θ₀ : ℝ)
    (_hθ₀def : θ₀ = 1 - (α + β) / 2 - ((d : ℝ) - 1) / 2 * (1 / ξ + 1 / ζ))
    (_hθ₀ : θ₀ ≤ 0) :
    ∃ a : Vec d → ℝ,
      Measurable a ∧ (∀ x, 0 < a x) ∧
      -- `a` does not depend on the first coordinate
      (∀ x x' : Vec d, (∀ i : Fin d, (i : ℕ) ≠ 0 → x i = x' i) → a x = a x') ∧
      IsWeightedCoeffOn (originCube 1) (fun x => a x • (1 : Mat d)) ∧
      (0 < α → cubeQuasiNorm (fun x => a x • (1 : Mat d)) (α / 2) ξ < ⊤) ∧
      (α = 0 →
        eLpNorm (fun x => ‖a x • (1 : Mat d)‖) (ENNReal.ofReal ξ)
          (volume.restrict (originCube 1)) < ⊤) ∧
      (0 < β → cubeQuasiNorm (fun x => (a x • (1 : Mat d))⁻¹) (β / 2) ζ < ⊤) ∧
      (β = 0 →
        eLpNorm (fun x => ‖(a x • (1 : Mat d))⁻¹‖) (ENNReal.ofReal ζ)
          (volume.restrict (originCube 1)) < ⊤) ∧
      ∃ (u : Vec d → ℝ) (G : Vec d → Vec d),
        IsWeightedSolution (fun x => a x • (1 : Mat d)) (originCube 1) u G ∧
        (∀ᵐ x ∂(volume.restrict (originCube 1)), 1 ≤ u x) ∧
        eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) = ⊤ ∧
        0 < nonnegativeEssInf (originCube (1 / 2)) u ∧
        nonnegativeEssInf (originCube (1 / 2)) u < ⊤ ∧
        -- essentially unbounded near every point `(x₁, 0)` of the axis, `|x₁| < 1/2`
        ∀ x : Vec d, |x ⟨0, Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) _hd⟩| < 1 / 2 →
          (∀ i : Fin d, (i : ℕ) ≠ 0 → x i = 0) →
          ∀ N ∈ 𝓝 x, eLpNorm u ⊤ (volume.restrict (N ∩ originCube 1)) = ⊤ := by
  classical
  obtain ⟨a, ha, hapos, hax, hcoef, hA, hAinv, h1, h2, h3, h4, u, hu, hge, hsup, hinf, hinfTop, hnear⟩ :=
    CoarseDeGiorgi.sharpness d _hd ξ ζ α β hξ hζ hα hβ θ₀ _hθ₀def _hθ₀
  refine ⟨a, ?_, hapos, hax, ?_⟩
  · rw [← BorelSpace.measurable_eq] at ha
    exact ha
  · obtain ⟨G, hG⟩ := hu
    refine ⟨?_, ?_, h2, ?_, h4, u, G, hG, hge, hsup, hinf, hinfTop, hnear⟩
    · change CoarseDeGiorgi.IsWeightedCoeffOn (originCube 1) (fun x => a x • (1 : Mat d))
      exact hcoef
    · intro hα'
      exact h1 hα'
    · intro hβ'
      exact h3 hβ'

end CoarseDeGiorgiAudit.Sharpness
