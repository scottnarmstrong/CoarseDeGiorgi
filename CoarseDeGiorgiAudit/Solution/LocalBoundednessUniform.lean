module

public import Mathlib
public import CoarseDeGiorgiAudit.Solution.LocalBoundednessLpLq
public import CoarseDeGiorgiAudit.Solution.Uniform.Bounds

@[expose] public section

attribute [-instance] Homogenization.instMeasurableSpaceVec

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
  let D : ℝ := (d : ℝ) - 1
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd1 : 0 < D := by dsimp [D]; linarith
  have hd2 : 2 ≤ D := by dsimp [D]; linarith
  have hκpos : 0 < κ := by
    have hpos : 0 < D / 4 := by positivity
    exact lt_trans hpos hκ
  let θ : ℝ := D / (4 * κ)
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact div_pos hd1 (by positivity)
  have hθlt : θ < 1 := by
    dsimp [θ]
    rw [div_lt_one (by positivity : 0 < 4 * κ)]
    nlinarith [hκ]
  have hden : 0 < 1 - θ := by linarith
  let p : ℝ := 2 * D / (1 - θ)
  have hp : 1 < p := by
    dsimp [p]
    apply (lt_div_iff₀ hden).2
    nlinarith [hd2, hθlt]
  have hrecip : 1 / p = (1 - θ) / (2 * D) := by
    dsimp [p]
    field_simp [ne_of_gt hden, ne_of_gt hd1]
  have hsum : 1 / p + 1 / p = (1 - θ) / D := by
    rw [hrecip]
    field_simp [ne_of_gt hd1]
    ring
  have hrange : 1 / p + 1 / p < 2 / D := by
    rw [hsum]
    apply (div_lt_div_iff₀ hd1 hd1).2
    nlinarith [hθpos, hd1]
  have htheta0 : LocalBoundednessLpLq.theta0 d p p = (1 + θ) / 2 := by
    unfold LocalBoundednessLpLq.theta0
    rw [hsum]
    rw [show (d : ℝ) - 1 = D by rfl]
    field_simp [ne_of_gt hd1]
    ring
  have htheta_den₁ : 0 < 4 * ((1 + θ) / 2) := by positivity
  have htheta_den₂ : 0 < 4 * θ := by positivity
  have hquotient : D / (4 * ((1 + θ) / 2)) < D / (4 * θ) := by
    apply (div_lt_div_iff₀ htheta_den₁ htheta_den₂).2
    nlinarith [hd1, hθlt]
  have hθeq : D / (4 * θ) = κ := by
    dsimp [θ]
    field_simp [ne_of_gt hd1, ne_of_gt hκpos]
  have hκLp : D / (4 * LocalBoundednessLpLq.theta0 d p p) < κ := by
    rw [htheta0]
    exact hquotient.trans_eq hθeq
  obtain ⟨γ, hγ, hbranches⟩ :=
    LocalBoundednessLpLq.localBoundednessLpLq d hd p p hp hp hrange κ hκLp
  obtain ⟨C, hC, hA⟩ := hbranches.1
  refine ⟨γ, hγ, C, hC, ?_⟩
  intro lam Λ hlam hLam a hmeas hEll u G hsub
  have hmeasRoot : AEStronglyMeasurable a
      (volume.restrict (CoarseDeGiorgiAudit.originCube 1)) := by
    simpa [cube, CoarseDeGiorgiAudit.originCube] using hmeas
  have hEllRoot : ∀ᵐ x ∂(volume.restrict (CoarseDeGiorgiAudit.originCube 1)),
      (a x).IsHermitian ∧ ∀ ξ : Vec d,
        lam * dotProduct ξ ξ ≤ dotProduct ξ ((a x).mulVec ξ) ∧
        dotProduct ξ ((a x).mulVec ξ) ≤ Λ * dotProduct ξ ξ := by
    simpa [UniformlyElliptic, cube, CoarseDeGiorgiAudit.originCube] using hEll
  have haRoot := CoarseDeGiorgiAudit.Solution.Uniform.uniformly_elliptic_isWeightedCoeffOn
    a hlam hLam hmeasRoot hEllRoot
  have hmomRoot := CoarseDeGiorgiAudit.Solution.Uniform.uniform_moment_bounds
    (p := p) (q := p) a hlam hLam (by positivity : 0 < p) (by positivity : 0 < p)
    hmeasRoot hEllRoot
  have haC4 : LocalBoundednessLpLq.IsWeightedCoeffOn
      (LocalBoundednessLpLq.cube 1) a := by
    change CoarseDeGiorgiAudit.IsWeightedCoeffOn
      (CoarseDeGiorgiAudit.originCube 1) a
    exact haRoot
  have hLpBound : eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
      (volume.restrict (LocalBoundednessLpLq.cube 1)) ≤ ENNReal.ofReal Λ := by
    simpa [LocalBoundednessLpLq.cube, CoarseDeGiorgiAudit.originCube] using hmomRoot.1
  have hInvLpBound : eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal p)
      (volume.restrict (LocalBoundednessLpLq.cube 1)) ≤ ENNReal.ofReal (lam⁻¹) := by
    simpa [LocalBoundednessLpLq.cube, CoarseDeGiorgiAudit.originCube] using hmomRoot.2
  have hLp : eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
      (volume.restrict (LocalBoundednessLpLq.cube 1)) < ⊤ :=
    lt_of_le_of_lt hLpBound ENNReal.ofReal_lt_top
  have hInvLp : eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal p)
      (volume.restrict (LocalBoundednessLpLq.cube 1)) < ⊤ :=
    lt_of_le_of_lt hInvLpBound ENNReal.ofReal_lt_top
  have hsubC4 : LocalBoundednessLpLq.IsWeightedSubsolution
      a (LocalBoundednessLpLq.cube 1) u G := by
    exact hsub
  have hAdata := hA a haC4 hLp hInvLp u G hsubC4
  let M : ℝ≥0∞ :=
    eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
      (volume.restrict (LocalBoundednessLpLq.cube 1)) *
    eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal p)
      (volume.restrict (LocalBoundednessLpLq.cube 1))
  have hΛ0 : 0 ≤ Λ := le_trans (le_of_lt hlam) hLam
  have hratio0 : 0 ≤ Λ / lam := div_nonneg hΛ0 (le_of_lt hlam)
  have hMle : M ≤ ENNReal.ofReal (Λ / lam) := by
    dsimp [M]
    calc
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (lam⁻¹) :=
        mul_le_mul hLpBound hInvLpBound bot_le bot_le
      _ = ENNReal.ofReal (Λ / lam) := by
        rw [div_eq_mul_inv, ← ENNReal.ofReal_mul hΛ0]
  have hbase : 1 + M ≤ ENNReal.ofReal (1 + Λ / lam) := by
    calc
      1 + M = M + 1 := by rw [add_comm]
      _ ≤ ENNReal.ofReal (Λ / lam) + 1 := by gcongr
      _ = ENNReal.ofReal (1 + Λ / lam) := by
        rw [add_comm, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num : 0 ≤ (1 : ℝ)) hratio0]
  have hpow : (1 + M).rpow κ ≤ (ENNReal.ofReal (1 + Λ / lam)).rpow κ :=
    ENNReal.rpow_le_rpow hbase (le_of_lt hκpos)
  constructor
  · exact hAdata.1
  · intro ρ R hρ hρR hR
    have hinner := hAdata.2 ρ R hρ hρR hR
    have hfactor := mul_le_mul_of_nonneg_left hpow (by positivity :
      0 ≤ ENNReal.ofReal C * (ENNReal.ofReal (R - ρ)).rpow (-γ))
    have hfull := mul_le_mul_of_nonneg_right hfactor (by positivity :
      0 ≤ eLpNorm (LocalBoundednessLpLq.positivePart u) 2
        (volume.restrict (LocalBoundednessLpLq.cube R)))
    have hbound := le_trans hinner.1 hfull
    constructor
    · change eLpNorm (LocalBoundednessLpLq.positivePart u) ⊤
        (volume.restrict (LocalBoundednessLpLq.cube ρ)) ≤
          ENNReal.ofReal C * (ENNReal.ofReal (R - ρ)).rpow (-γ) *
            (ENNReal.ofReal (1 + Λ / lam)).rpow κ *
            eLpNorm (LocalBoundednessLpLq.positivePart u) 2
              (volume.restrict (LocalBoundednessLpLq.cube R))
      exact hbound
    · intro hRlt
      change eLpNorm (LocalBoundednessLpLq.positivePart u) 2
        (volume.restrict (LocalBoundednessLpLq.cube R)) < ⊤
      exact hinner.2 hRlt

end CoarseDeGiorgiAudit.LocalBoundednessUniform
