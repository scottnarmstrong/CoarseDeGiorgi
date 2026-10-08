import Mathlib

/-!
# Harnack inequality under finite cube quasi-norms (Theorems C, D(ii))

Assume `d ≥ 3`, `p,q > 1`, `s,t > 0`, and
`θ = 1 − s − t − (d−1)(1/p+1/q)/2 > 0`. Let `a` be a weighted coefficient field
on `cube 1` whose cube quasi-norms (1.12) `N_a = ‖a‖_{B̊^{−2s}_{p,1/2}}` and
`N_{a⁻¹} = ‖a⁻¹‖_{B̊^{−2t}_{q,1/2}}` are finite, and put `N = N_a N_{a⁻¹}`.
By Theorem D(ii), the moments and the contrast of `a` satisfy
`Λ_{s,1,p} ≤ d!(1−3^{−s})²N_a`, `λ_{t,1,q}⁻¹ ≤ d!(1−3^{−t})²N_{a⁻¹}` and
`Θ ≤ (d!)² N`, so Theorems A, C and Corollary B hold with `Θ` replaced by `N`.

There is `C = C(d,p,q,s,t) ≥ 0` such that every nonnegative
weighted solution satisfies

$$
\operatorname*{ess\,sup}_{\mathrm{cube}(1/2)} u
\le \exp(C\sqrt N)\,\operatorname*{ess\,inf}_{\mathrm{cube}(1/2)} u.
$$

The weighted space is the smooth-core closure `H¹ₐ`, and solutions satisfy
the weak flux equation against smooth compactly supported tests. The
quasi-norm is written out below as `cubeQuasiNorm`.
-/

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.HarnackBesov

/-! ## Ambient space and cubes -/

/-- Vectors in the ambient space `ℝᵈ`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on ambient vectors. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The open cube `(-ρ/2, ρ/2)ᵈ`. -/
def cube {d : ℕ} (ρ : ℝ) : Set (Vec d) :=
  {x | ∀ i, (-(ρ / 2)) < x i ∧ x i < ρ / 2}

/-! ## Coefficient fields -/

/-- A coefficient field assigns a real matrix to each point. -/
abbrev CoeffField (d : ℕ) := Vec d → Mat d

/-- Coefficients are measurable and positive definite a.e.; their traces
and inverse traces are integrable on the domain. -/
def IsWeightedCoeffOn {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) : Prop :=
  AEStronglyMeasurable a (volume.restrict V) ∧
    (∀ᵐ x ∂(volume.restrict V), (a x).PosDef) ∧
    Integrable (fun x => (a x).trace) (volume.restrict V) ∧
    Integrable (fun x => ((a x)⁻¹).trace) (volume.restrict V)

/-! ## Averages and energies -/

/-- The weighted energy `∫_U G·aG` (the energy of `u` when `G = ∇u`),
as an extended nonnegative real. -/
noncomputable def weightedEnergy {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal (G x ⬝ᵥ ((a x) *ᵥ G x))

/-- Normalized average `⨍_U f = |U|⁻¹ ∫_U f`. -/
noncomputable def averageOn {d : ℕ} (U : Set (Vec d)) (f : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, f x ∂volume

/-! ## The weighted space `H¹ₐ` -/

/-- Coordinate gradient `(∇φ x)ᵢ = Dφ(x)eᵢ`. -/
noncomputable def smoothGrad {d : ℕ} (φ : Vec d → ℝ) : Vec d → Vec d :=
  fun x i => fderiv ℝ φ x (Pi.single i (1 : ℝ))

/-- A smooth-core function is smooth on `V`, integrable there, and has
finite weighted energy. -/
noncomputable def IsSmoothCore {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) φ V ∧
    Integrable φ (volume.restrict V) ∧
    weightedEnergy a V (smoothGrad φ) < ⊤

/-- `H¹ₐ(V)` is the smooth-core closure in squared mean plus weighted energy;
approximants converge in local `L¹` and their gradients converge in energy. -/
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

/-! ## Solutions -/

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
        (fun x => smoothGrad φ x ⬝ᵥ ((a x) *ᵥ G x))
        (volume.restrict V) ∧
      ∫ x in V, smoothGrad φ x ⬝ᵥ ((a x) *ᵥ G x) ∂volume = 0

/-! ## Norms and parameters -/

/-- Essential infimum of `u` on `V`, encoded in `ℝ≥0∞` for `u ≥ 0` a.e. -/
noncomputable def essInfNonneg {d : ℕ}
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict V)

/-- `θ = 1 − s − t − (d−1)(1/p+1/q)/2`. -/
noncomputable def theta (d : ℕ) (p q s t : ℝ) : ℝ :=
  1 - s - t - (((d : ℝ) - 1) / 2) * (1 / p + 1 / q)

/-! ## Triadic cubes and the cube quasi-norm -/

/-- Center the grid index by the formula `j ↦ j − (3^k−1)/2`. -/
def gridOffset {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Fin d → ℤ :=
  fun i => (j i : ℤ) - (((3 ^ k - 1) / 2 : ℕ) : ℤ)

/-- The triadic cube `z + (−3⁻ᵏ/2, 3⁻ᵏ/2)ᵈ` of side `3⁻ᵏ` with center
`z = 3⁻ᵏ · gridOffset k j`. As `j` ranges over `Fin d → Fin (3^k)` these
`3^(kd)` cubes tile `cube 1` up to a null set. -/
def triadicCube {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Set (Vec d) :=
  {x | x - (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) ∈
    cube ((3 : ℝ) ^ (-(k : ℤ)))}

/-- Entrywise volume average of a matrix field over a set. -/
noncomputable def volumeAverageMat {d : ℕ} (V : Set (Vec d))
    (b : CoeffField d) : Mat d :=
  fun i j => averageOn V (fun x => b x i j)

/-- The cube quasi-norm (1.12), `‖b‖_{B̊^{−2s}_{p,1/2}(□₀)}` for `1 ≤ p < ∞`:
`(∑_{k ≥ 0} 3^{−ks} (avg_{Q} |(b)_Q|^p)^{1/(2p)})²`, where `Q` runs over the `3^(kd)`
triadic cubes of side `3⁻ᵏ` tiling `cube 1`, `(b)_Q` is the entrywise average of `b`
over `Q`, and `|·|` is the `ℓ²` operator norm. It takes values in `[0,∞]`. -/
noncomputable def cubeQuasiNorm {d : ℕ} (b : CoeffField d)
    (s p : ℝ) : ℝ≥0∞ := by
  classical
  exact
    (∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal
          ((∑ j : Fin d → Fin (3 ^ k),
              Real.rpow ‖volumeAverageMat (triadicCube k j) b‖ p) /
            (Fintype.card (Fin d → Fin (3 ^ k)) : ℝ))).rpow
          (1 / (2 * p))) ^ 2

/-! ## The theorem -/

theorem harnackBesov
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < theta d p q s t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀
        -- coefficient field with finite quasi-norms
        (a : CoeffField d), IsWeightedCoeffOn (cube 1) a →
        cubeQuasiNorm a s p < ⊤ →
        cubeQuasiNorm (fun x => (a x)⁻¹) t q < ⊤ →
        let N : ℝ≥0∞ :=
          cubeQuasiNorm a s p * cubeQuasiNorm (fun x => (a x)⁻¹) t q
        ∀
          -- nonnegative weighted solution
          (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (cube 1)), 0 ≤ u x) →
          IsWeightedSolution a (cube 1) u G →
          -- conclusion
          eLpNorm u ⊤ (volume.restrict (cube (1 / 2))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt N.toReal)) *
              essInfNonneg (cube (1 / 2)) u := by
  sorry

end CoarseDeGiorgiAudit.HarnackBesov
