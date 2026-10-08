import Mathlib

/-!
Harnack inequality for uniformly elliptic coefficients.

Let `d ≥ 3`. There is `C = C(d)` such that, whenever `a` is measurable and symmetric with
`λ|ξ|² ≤ ξ·a(x)ξ ≤ Λ|ξ|²` for a.e. `x ∈ cube 1` (`0 < λ ≤ Λ`; the code writes `lam`, since `λ`
is a Lean keyword), every nonnegative weighted solution `u` on `cube 1` satisfies
  `esssup_{cube(1/2)} u ≤ exp(C √(Λ/λ)) · essinf_{cube(1/2)} u`.
Solutions are taken in the weighted space `H¹ₐ` (limits of smooth functions in squared mean plus
weighted energy, converging in `L¹` on compact subsets). This follows from Theorem D(i) of the
manuscript with `p = q = d`.
-/

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.HarnackUniform

/-! ## Ambient space and cubes -/

/-- Vectors in the ambient space `ℝᵈ`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on ambient vectors. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The open cube `(-ρ/2, ρ/2)ᵈ`. -/
def cube {d : ℕ} (ρ : ℝ) : Set (Vec d) :=
  {x | ∀ i, (-(ρ / 2)) < x i ∧ x i < ρ / 2}


/-! ## Coefficient fields -/

/-- A coefficient field: a `d × d` matrix at each point (no regularity is assumed here). -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

/-- A.e. symmetric bounds `lam|ξ|² ≤ ξ·aξ ≤ Λ|ξ|²` on `cube 1`. -/
def UniformlyElliptic {d : ℕ} (lam Λ : ℝ) (a : CoeffField d) : Prop :=
  ∀ᵐ x ∂(volume.restrict (cube 1)),
    (a x).IsHermitian ∧
      ∀ ξ : Vec d,
        lam * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ (a x *ᵥ ξ) ∧
        ξ ⬝ᵥ (a x *ᵥ ξ) ≤ Λ * (ξ ⬝ᵥ ξ)


/-! ## Averages and energies -/

/-- Weighted energy `∫_U G · aG` of a vector field `G` (for `G = ∇u`, the energy of `u`),
as an extended nonnegative real. -/
noncomputable def weightedEnergy {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal (G x ⬝ᵥ (a x *ᵥ G x))

/-- Normalized average `⨍_U f = |U|⁻¹ ∫_U f`. -/
noncomputable def averageOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, f x ∂volume


/-! ## The weighted space `H¹ₐ` -/

/-- Coordinate gradient of a smooth function: `(∇φ x)ᵢ = Dφ(x)eᵢ`. -/
noncomputable def smoothGrad {d : ℕ} (φ : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => fderiv ℝ φ x (Pi.single i (1 : ℝ))

/-- A smooth core function is `C^∞` on `V`, integrable on `V`, and has finite weighted energy. -/
noncomputable def IsSmoothCore {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) φ V ∧
    Integrable φ (volume.restrict V) ∧
    weightedEnergy a V (smoothGrad φ) < ⊤

/-- `H¹ₐ(V)` is the smooth-core closure in squared mean plus weighted energy.
Approximants converge in `L¹` on compact subsets and gradients in weighted energy. -/
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


/-! ## Subsolutions, supersolutions, and solutions -/

/-- A weighted solution has zero flux pairing with every smooth compactly
supported test: `∫_V ∇φ · a∇u = 0`. -/
noncomputable def IsWeightedSolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      Integrable
        (fun x => smoothGrad φ x ⬝ᵥ (a x *ᵥ G x))
        (volume.restrict V) ∧
      ∫ x in V,
        smoothGrad φ x ⬝ᵥ (a x *ᵥ G x) ∂volume = 0


/-! ## Norms, moments, and parameters -/

/-- Essential infimum of `u` on `V`, encoded in `ℝ≥0∞` for `u ≥ 0` a.e. -/
noncomputable def essInfNonneg {d : ℕ}
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict V)


/-! ## The theorem -/

theorem harnackUniform
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀
        -- ellipticity constants and coefficient field
        (lam Λ : ℝ), 0 < lam → lam ≤ Λ →
        ∀ (a : CoeffField d),
          AEStronglyMeasurable a (volume.restrict (cube 1)) →
          UniformlyElliptic lam Λ a →
          ∀
            -- nonnegative weighted solution
            (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (cube 1)), 0 ≤ u x) →
            IsWeightedSolution a (cube 1) u G →
            -- conclusion
            eLpNorm u ⊤ (volume.restrict (cube (1 / 2))) ≤
              ENNReal.ofReal (Real.exp (C * Real.sqrt (Λ / lam))) *
                essInfNonneg (cube (1 / 2)) u := by
  sorry

end CoarseDeGiorgiAudit.HarnackUniform
