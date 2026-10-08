import Mathlib

/-!
Harnack inequality under coefficient moments (Theorem D(i) of the manuscript with Theorem C, Harnack part).

Let `d ≥ 3` and `p, q > 1` with `1/p + 1/q < 2/(d−1)`. There is `C = C(d,p,q)` such that, for every
coefficient field `a` with `|a| ∈ Lᵖ(cube 1)` and `|a⁻¹| ∈ Lᑫ(cube 1)` (`|·|` the ℓ² operator norm)
and every nonnegative weighted solution `u` on `cube 1`,
  `esssup_{cube(1/2)} u ≤ exp(C √M) · essinf_{cube(1/2)} u`,   `M = ‖|a|‖_{Lᵖ} ‖|a⁻¹|‖_{Lᑫ}`.
Solutions are taken in the weighted space `H¹ₐ`: limits of smooth functions in squared mean plus
weighted energy, converging in `L¹` on compact subsets, with an explicit gradient `G`.
-/

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.HarnackLpLq

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

/-- Coefficients are measurable and positive definite a.e.
Their trace and inverse trace are integrable on the domain. -/
def IsWeightedCoeffOn {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) : Prop :=
  AEStronglyMeasurable a (volume.restrict V) ∧
    (∀ᵐ x ∂(volume.restrict V), (a x).PosDef) ∧
    Integrable (fun x => (a x).trace) (volume.restrict V) ∧
    Integrable (fun x => ((a x)⁻¹).trace) (volume.restrict V)


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

theorem harnackLpLq
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) (p q : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hrange : 1 / p + 1 / q < 2 / ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀
        -- coefficient field and coefficient moments
        (a : CoeffField d), IsWeightedCoeffOn (cube 1) a →
        eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
          (volume.restrict (cube 1)) < ⊤ →
        eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
          (volume.restrict (cube 1)) < ⊤ →
        let M : ℝ≥0∞ :=
          eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
            (volume.restrict (cube 1)) *
          eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
            (volume.restrict (cube 1))
        ∀
          -- nonnegative weighted solution
        (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (cube 1)), 0 ≤ u x) →
          IsWeightedSolution a (cube 1) u G →
          -- conclusion
          eLpNorm u ⊤ (volume.restrict (cube (1 / 2))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt M.toReal)) *
              essInfNonneg (cube (1 / 2)) u := by
  sorry

end CoarseDeGiorgiAudit.HarnackLpLq
