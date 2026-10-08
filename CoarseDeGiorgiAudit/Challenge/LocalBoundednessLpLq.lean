import Mathlib

/-!
Local boundedness under coefficient moments (Theorem A and Corollary B of the manuscript, via
Theorem D(i)).

Let `d ≥ 3`, `p, q > 1` with `1/p + 1/q < 2/(d−1)`, and `θ₀ = 1 − (d−1)(1/p+1/q)/2 > 0`. For every
`κ > (d−1)/(4θ₀)` there is `γ > 0` such that, with `M = ‖|a|‖_{Lᵖ} ‖|a⁻¹|‖_{Lᑫ}`, every weighted
subsolution `u` on `cube 1` is locally bounded above and, for `1/2 ≤ ρ < R ≤ 1`,
  `‖u₊‖_{L∞(cube ρ)} ≤ C (R−ρ)^{−γ} (1+M)^κ ‖u₊‖_{L²(cube R)}`,
  `‖u₊‖_{L∞(cube ρ)} ≤ C_η (R−ρ)^{−2γ/η} (1+M)^{2κ/η} ‖u₊‖_{Lη(cube R)}`   for each `0 < η < 2`,
with `C = C(d,p,q,κ)`, `C_η = C_η(d,p,q,κ,η)`, and the right-hand norms finite when `R < 1`.
Derivation: `θ = (d−1)/(4κ) ∈ (0,θ₀)` and `s = t = (θ₀−θ)/2` in the discussion after Theorem D(i) (indices with `θ > 0`), whose exponent is then
`θ`.
-/

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.LocalBoundednessLpLq

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

/-! ## Integrability margin -/

/-- `θ₀ = 1 − (d−1)(1/p+1/q)/2`, the positive margin in the moment range. -/
noncomputable def theta0 (d : ℕ) (p q : ℝ) : ℝ :=
  1 - (((d : ℝ) - 1) / 2) * (1 / p + 1 / q)

/-! ## The theorem -/

theorem localBoundednessLpLq
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) (p q : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hrange : 1 / p + 1 / q < 2 / ((d : ℝ) - 1))
    -- coefficient-growth exponent
    (κ : ℝ) (hκ : ((d : ℝ) - 1) / (4 * theta0 d p q) < κ) :
    ∃ γ : ℝ, 0 < γ ∧
      ((∃ C_A : ℝ, 0 ≤ C_A ∧
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
            -- weighted subsolution
            (u : Vec d → ℝ) (G : Vec d → Vec d),
            IsWeightedSubsolution a (cube 1) u G →
            -- conclusion
            LocallyBoundedAbove (cube 1) u ∧
            ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
              let rhs := ENNReal.ofReal C_A *
                (ENNReal.ofReal (R - ρ)).rpow (-γ) *
                (1 + M).rpow κ *
                eLpNorm (positivePart u) 2 (volume.restrict (cube R))
              eLpNorm (positivePart u) ⊤
                  (volume.restrict (cube ρ)) ≤ rhs ∧
                (R < 1 →
                  eLpNorm (positivePart u) 2
                    (volume.restrict (cube R)) < ⊤)) ∧
      (∀ η : ℝ, 0 < η → η < 2 →
        ∃ C_η : ℝ, 0 ≤ C_η ∧
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
              -- weighted subsolution
              (u : Vec d → ℝ) (G : Vec d → Vec d),
              IsWeightedSubsolution a (cube 1) u G →
              -- conclusion
              ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                let rhs := ENNReal.ofReal C_η *
                  (ENNReal.ofReal (R - ρ)).rpow (-(2 * γ / η)) *
                  (1 + M).rpow (2 * κ / η) *
                  eLpNorm (positivePart u) (ENNReal.ofReal η)
                    (volume.restrict (cube R))
                eLpNorm (positivePart u) ⊤
                    (volume.restrict (cube ρ)) ≤ rhs ∧
                  (R < 1 →
                    eLpNorm (positivePart u) (ENNReal.ofReal η)
                      (volume.restrict (cube R)) < ⊤))) := by
  sorry

end CoarseDeGiorgiAudit.LocalBoundednessLpLq
