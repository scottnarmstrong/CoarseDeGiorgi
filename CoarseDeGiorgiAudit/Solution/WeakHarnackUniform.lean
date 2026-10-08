module

public import Mathlib
public import CoarseDeGiorgiAudit.Solution.WeakHarnackLpLq
public import CoarseDeGiorgiAudit.Solution.Uniform.Bounds

@[expose] public section

attribute [-instance] Homogenization.instMeasurableSpaceVec

/-!
Weak Harnack inequality for uniformly elliptic coefficients.

Let `d ≥ 3`. For every `0 < η < d/(d−2)` there is `C = C(η,d)` such that, whenever `a` is
measurable and symmetric with `λ|ξ|² ≤ ξ·a(x)ξ ≤ Λ|ξ|²` for a.e. `x ∈ cube 1` (`0 < λ ≤ Λ`; the
code writes `lam`), every nonnegative weighted supersolution `u` on `cube 1` satisfies
  `(⨍_{cube(5/8)} u^η)^{1/η} ≤ exp(C √(Λ/λ)) · essinf_{cube(1/2)} u`.
Supersolutions are taken in the weighted space `H¹ₐ` (limits of smooth functions in squared mean
plus weighted energy, converging in `L¹` on compact subsets), and `u` is a supersolution when `−u`
is a subsolution. This follows from Theorems C and D(i) of the manuscript: such coefficients have
`|a| ∈ Lᵖ`, `|a⁻¹| ∈ Lᑫ` for all `p, q`, and the union over the admissible `p, q, s, t` of the
ranges `0 < η ≤ r*/2` of Theorem C is `0 < η < d/(d−2)`. The endpoint `d/(d−2)` is not included.
-/

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.WeakHarnackUniform

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

/-- `u` is a weighted supersolution when `-u` is a weighted subsolution. -/
noncomputable def IsWeightedSupersolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  IsWeightedSubsolution a V (fun x => -u x) (fun x => -G x)


/-! ## Norms, moments, and parameters -/

/-- Essential infimum of `u` on `V`, encoded in `ℝ≥0∞` for `u ≥ 0` a.e. -/
noncomputable def essInfNonneg {d : ℕ}
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict V)

/-- Normalized `Lᵇ` moment `(|V|⁻¹ ∫_V |u|ᵇ)^(1/b)`.
Used with `b = η > 0`. -/
noncomputable def normalizedLpMoment {d : ℕ} (b : ℝ)
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  ((volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |u x|).rpow b).rpow (1 / b)

/-! ## The theorem -/

theorem weakHarnackUniform
    -- dimension
    (d : ℕ) (hd : 3 ≤ d) :
    -- exponent: 0 < η < d/(d − 2)
    ∀ η : ℝ, 0 < η → η < (d : ℝ) / ((d : ℝ) - 2) →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀
        -- ellipticity constants and coefficient field
        (lam Λ : ℝ), 0 < lam → lam ≤ Λ →
        ∀ (a : CoeffField d),
          AEStronglyMeasurable a (volume.restrict (cube 1)) →
          UniformlyElliptic lam Λ a →
        ∀
          -- nonnegative weighted supersolution
          (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (cube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (cube 1) u G →
          -- conclusion
          normalizedLpMoment η (cube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (Λ / lam))) *
              essInfNonneg (cube (1 / 2)) u := by
  intro η hη hηlt
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : 0 < (d : ℝ) := by linarith
  have hd1 : 0 < (d : ℝ) - 1 := by linarith
  have hd2 : 0 < (d : ℝ) - 2 := by linarith
  have hgap : 0 < (d : ℝ) - η * ((d : ℝ) - 2) := by
    have h := (lt_div_iff₀ hd2).mp hηlt
    linarith
  -- the exponent `p = q = Q` is so large that `η` lies below `dQ/(dQ + d − 2Q)`
  let Q : ℝ := (d : ℝ) + η * d / ((d : ℝ) - η * ((d : ℝ) - 2))
  have hQd : (d : ℝ) ≤ Q := by
    have h : 0 ≤ η * d / ((d : ℝ) - η * ((d : ℝ) - 2)) := by positivity
    dsimp [Q]
    linarith
  have hp : 1 < Q := by linarith
  have hrange : 1 / Q + 1 / Q < 2 / ((d : ℝ) - 1) := by
    rw [show 1 / Q + 1 / Q = 2 / Q by ring]
    exact div_lt_div_of_pos_left (by norm_num) hd1 (by linarith)
  have hηQ : η < (d : ℝ) * Q / ((d : ℝ) * Q + (d : ℝ) - 2 * Q) := by
    have hden : 0 < (d : ℝ) * Q + (d : ℝ) - 2 * Q := by nlinarith
    have hQgap : Q * ((d : ℝ) - η * ((d : ℝ) - 2)) =
        (d : ℝ) * ((d : ℝ) - η * ((d : ℝ) - 2)) + η * d := by
      dsimp [Q]
      field_simp
    rw [lt_div_iff₀ hden]
    nlinarith [mul_pos hd0 hgap]
  obtain ⟨Cw, hCw, hWeak⟩ :=
    WeakHarnackLpLq.weakHarnackLpLq d hd Q Q hp hp hrange η hη hηQ
  refine ⟨Cw, hCw, ?_⟩
  intro lam Λ hlam hLam a hmeas hEll u G hu hsuper
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
    (p := Q) (q := Q) a hlam hLam (by linarith) (by linarith)
    hmeasRoot hEllRoot
  have haLp : WeakHarnackLpLq.IsWeightedCoeffOn
      (WeakHarnackLpLq.cube 1) a := by
    change CoarseDeGiorgiAudit.IsWeightedCoeffOn
      (CoarseDeGiorgiAudit.originCube 1) a
    exact haRoot
  have hLpBound : eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal Q)
      (volume.restrict (WeakHarnackLpLq.cube 1)) ≤ ENNReal.ofReal Λ := by
    simpa [WeakHarnackLpLq.cube, CoarseDeGiorgiAudit.originCube] using hmomRoot.1
  have hInvLpBound : eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal Q)
      (volume.restrict (WeakHarnackLpLq.cube 1)) ≤ ENNReal.ofReal (lam⁻¹) := by
    simpa [WeakHarnackLpLq.cube, CoarseDeGiorgiAudit.originCube] using hmomRoot.2
  have hLp : eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal Q)
      (volume.restrict (WeakHarnackLpLq.cube 1)) < ⊤ :=
    lt_of_le_of_lt hLpBound ENNReal.ofReal_lt_top
  have hInvLp : eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal Q)
      (volume.restrict (WeakHarnackLpLq.cube 1)) < ⊤ :=
    lt_of_le_of_lt hInvLpBound ENNReal.ofReal_lt_top
  have huLp : ∀ᵐ x ∂(volume.restrict (WeakHarnackLpLq.cube 1)), 0 ≤ u x := by
    simpa [cube, WeakHarnackLpLq.cube] using hu
  have hsuperLp : WeakHarnackLpLq.IsWeightedSupersolution
      a (WeakHarnackLpLq.cube 1) u G := hsuper
  let M : ℝ≥0∞ :=
    eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal Q)
      (volume.restrict (WeakHarnackLpLq.cube 1)) *
    eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal Q)
      (volume.restrict (WeakHarnackLpLq.cube 1))
  have hΛ0 : 0 ≤ Λ := le_trans (le_of_lt hlam) hLam
  have hMle : M ≤ ENNReal.ofReal (Λ / lam) := by
    dsimp [M]
    calc
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (lam⁻¹) :=
        mul_le_mul hLpBound hInvLpBound bot_le bot_le
      _ = ENNReal.ofReal (Λ / lam) := by
        rw [div_eq_mul_inv, ← ENNReal.ofReal_mul hΛ0]
  have hMreal : M.toReal ≤ Λ / lam := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMle
    simpa [ENNReal.toReal_ofReal (div_nonneg hΛ0 (le_of_lt hlam))] using h
  have hweak := hWeak a haLp hLp hInvLp u G huLp hsuperLp
  have hInfNonneg : 0 ≤ essInfNonneg (cube (1 / 2)) u := bot_le
  have hExp : Real.exp (Cw * Real.sqrt M.toReal) ≤
      Real.exp (Cw * Real.sqrt (Λ / lam)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hMreal) hCw
  have hFactor : ENNReal.ofReal (Real.exp (Cw * Real.sqrt M.toReal)) ≤
      ENNReal.ofReal (Real.exp (Cw * Real.sqrt (Λ / lam))) :=
    ENNReal.ofReal_le_ofReal hExp
  have hfinal := le_trans hweak
    (mul_le_mul_of_nonneg_right hFactor hInfNonneg)
  simpa [M, cube, WeakHarnackLpLq.cube, normalizedLpMoment,
    WeakHarnackLpLq.normalizedLpMoment,
    essInfNonneg, WeakHarnackLpLq.essInfNonneg] using hfinal

end CoarseDeGiorgiAudit.WeakHarnackUniform
