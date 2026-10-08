module

public import Mathlib

/-!
Local boundedness for uniformly elliptic coefficients.

Let `d ≥ 3` and `κ > (d−1)/4`. There are `γ > 0` and `C = C(d,κ)` such that, whenever `a` is
measurable and symmetric with `λ|ξ|² ≤ ξ·a(x)ξ ≤ Λ|ξ|²` for a.e. `x ∈ cube 1`
(`0 < λ ≤ Λ`; the code writes `lam`, since `λ` is a Lean keyword), every weighted subsolution `u`
on `cube 1` is locally bounded above and, for `1/2 ≤ ρ < R ≤ 1`,
  `‖u₊‖_{L∞(cube ρ)} ≤ C (R−ρ)^{−γ} (1+Λ/λ)^κ ‖u₊‖_{L²(cube R)}`,
with the right side finite when `R < 1`.
Derivation: Theorem D(i) of the manuscript, in the setting of the discussion after it, with
`θ = (d−1)/(4κ) ∈ (0,1)`, `s = t = (1−θ)/4`, `p = q = 2(d−1)/(1−θ)`,
using `‖|a|‖_{Lᵖ} ‖|a⁻¹|‖_{Lᑫ} ≤ Λ/λ` on the unit cube.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.LocalBoundednessUniform

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

/-- A weighted subsolution has nonpositive flux pairing with every nonnegative
smooth compactly supported test: `∫_V ∇φ · a∇u ≤ 0`. -/
noncomputable def IsWeightedSubsolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) →
      Integrable
        (fun x => smoothGrad φ x ⬝ᵥ (a x *ᵥ G x))
        (volume.restrict V) ∧
      ∫ x in V,
        smoothGrad φ x ⬝ᵥ (a x *ᵥ G x) ∂volume ≤ 0

/-- `u` is essentially bounded above on every compact subset of `V`. -/
def LocallyBoundedAbove {d : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∀ K : Set (Vec d), IsCompact K → K ⊆ V →
    ∃ M : ℝ, ∀ᵐ x ∂(volume.restrict K), u x ≤ M

/-- Positive part `u₊ = max(u, 0)`. -/
def positivePart {d : ℕ} (u : Vec d → ℝ) : Vec d → ℝ :=
  fun x => max (u x) 0


/-! ## The theorem -/

theorem localBoundednessUniform
    -- parameters
    (d : ℕ) (hd : 3 ≤ d)
    -- coefficient-growth exponent
    (κ : ℝ) (hκ : ((d : ℝ) - 1) / 4 < κ) :
    ∃ γ : ℝ, 0 < γ ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀
          -- ellipticity constants and coefficient field
          (lam Λ : ℝ), 0 < lam → lam ≤ Λ →
          ∀ (a : CoeffField d),
            AEStronglyMeasurable a (volume.restrict (cube 1)) →
            UniformlyElliptic lam Λ a →
            ∀
              -- weighted subsolution
              (u : Vec d → ℝ) (G : Vec d → Vec d),
              IsWeightedSubsolution a (cube 1) u G →
              -- conclusion
              LocallyBoundedAbove (cube 1) u ∧
              ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                let rhs := ENNReal.ofReal C *
                  (ENNReal.ofReal (R - ρ)).rpow (-γ) *
                  (ENNReal.ofReal (1 + Λ / lam)).rpow κ *
                  eLpNorm (positivePart u) 2 (volume.restrict (cube R))
                eLpNorm (positivePart u) ⊤
                    (volume.restrict (cube ρ)) ≤ rhs ∧
                  (R < 1 →
                    eLpNorm (positivePart u) 2
                      (volume.restrict (cube R)) < ⊤) := by
  sorry

end CoarseDeGiorgiAudit.LocalBoundednessUniform
