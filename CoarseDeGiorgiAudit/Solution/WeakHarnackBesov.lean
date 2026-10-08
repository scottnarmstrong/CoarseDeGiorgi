import Mathlib
import CoarseDeGiorgiAudit.Defs
import CoarseDeGiorgiAudit.DefsCells
import CoarseDeGiorgiAudit.Solution.Bridge
import CoarseDeGiorgiAudit.Solution.BridgeBesov
import CoarseDeGiorgiAudit.Solution.BridgeChallengeLp
import CoarseDeGiorgiAudit.Solution.WeakHarnackLpLq
import CoarseDeGiorgi.Statements.WeakHarnackRange
import CoarseDeGiorgiAudit.Solution.BridgeBesovCube

open private instModuleVecOCS from Homogenization.Sobolev.H1.OriginCubeSymmetry
attribute [-instance] instModuleVecOCS

/-!
# Weak Harnack inequality under finite cube quasi-norms (Theorems C, D(ii))

Assume `d ≥ 3`, `p,q > 1`, `s,t > 0`, and
`θ = 1 − s − t − (d−1)(1/p+1/q)/2 > 0`. Let `a` be a weighted coefficient field
on `cube 1` whose cube quasi-norms (1.12) `N_a = ‖a‖_{B̊^{−2s}_{p,1/2}}` and
`N_{a⁻¹} = ‖a⁻¹‖_{B̊^{−2t}_{q,1/2}}` are finite, and put `N = N_a N_{a⁻¹}`.
By Theorem D(ii), the moments and the contrast of `a` satisfy
`Λ_{s,1,p} ≤ d!(1−3^{−s})²N_a`, `λ_{t,1,q}⁻¹ ≤ d!(1−3^{−t})²N_{a⁻¹}` and
`Θ ≤ (d!)² N`, so Theorems A, C and Corollary B hold with `Θ` replaced by `N`.

Let `r = 2q/(q+1)` and let `r* = dr/(d − (1−t)r)`, where `−2t` is the order of the
quasi-norm of `a⁻¹`. For every `0 < η ≤ r*/2` there is `C = C(η,d,p,q,s,t) ≥ 0`
such that every nonnegative weighted supersolution satisfies

$$
\left(\fint_{\mathrm{cube}(5/8)} u^{\eta}\right)^{1/\eta}
\le \exp(C\sqrt N)\,\operatorname*{ess\,inf}_{\mathrm{cube}(1/2)} u.
$$

Supersolutions mean that the negative is a subsolution in the smooth-core
closure `H¹ₐ`. The quasi-norm is written out below as `cubeQuasiNorm`.
-/

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.WeakHarnackBesov

attribute [-instance] Homogenization.instMeasurableSpaceVec

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

/-! ## Subsolutions and supersolutions -/

/-- A subsolution has nonpositive flux pairing with every nonnegative smooth,
compactly supported test: `∫_V ∇φ · a∇u ≤ 0`. -/
noncomputable def IsWeightedSubsolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  MemH1a a V u G ∧
    ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ V →
      (∀ x, 0 ≤ φ x) →
      Integrable
        (fun x => smoothGrad φ x ⬝ᵥ ((a x) *ᵥ G x))
        (volume.restrict V) ∧
      ∫ x in V, smoothGrad φ x ⬝ᵥ ((a x) *ᵥ G x) ∂volume ≤ 0

/-- `u` is a weighted supersolution when `−u` is a weighted subsolution. -/
noncomputable def IsWeightedSupersolution {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  IsWeightedSubsolution a V (fun x => -u x) (fun x => -G x)

/-! ## Norms and parameters -/

/-- Essential infimum of `u` on `V`, encoded in `ℝ≥0∞` for `u ≥ 0` a.e. -/
noncomputable def essInfNonneg {d : ℕ}
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict V)

/-- Normalized moment `(|V|⁻¹ ∫_V |u|ᵇ)^(1/b)`, defined for every `b`. -/
noncomputable def normalizedLpMoment {d : ℕ} (b : ℝ)
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  ((volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |u x|).rpow b).rpow (1 / b)

/-- `θ = 1 − s − t − (d−1)(1/p+1/q)/2`. -/
noncomputable def theta (d : ℕ) (p q s t : ℝ) : ℝ :=
  1 - s - t - (((d : ℝ) - 1) / 2) * (1 / p + 1 / q)

/-- The exponent `r = 2q/(q+1)` of (1.7). -/
noncomputable def paramR (q : ℝ) : ℝ := 2 * q / (q + 1)

/-- The Sobolev exponent `r* = dr/(d − (1−t)r)` of `W^{1−t,r}` (Theorem C, (3.22)).
The critical weak Harnack exponent is `η_c = r*/2`. -/
noncomputable def rStar (d : ℕ) (q t : ℝ) : ℝ :=
  (d : ℝ) * paramR q / ((d : ℝ) - (1 - t) * paramR q)

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

theorem cubeQuasiNorm_eq {d : ℕ} (b : CoeffField d)
    (hb : ∀ i j, Integrable (fun x => b x i j)
      (volume.restrict (CoarseDeGiorgi.originCube 1)))
    (s p : ℝ) (hs : 0 < s) (hp : 1 ≤ p) :
    cubeQuasiNorm b s p = CoarseDeGiorgi.besovCubeNorm b hb s p hs hp := rfl

theorem normalizedLpMoment_eq_root {d : ℕ} (b : ℝ) (hb : 0 < b)
    (V : Set (Vec d)) (u : Vec d → ℝ) :
    normalizedLpMoment b V u =
      CoarseDeGiorgi.normalizedLpMoment b hb V u := rfl

/-! ## The theorem -/

theorem weakHarnackBesov
    -- parameters
    (d : ℕ) (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q)
    (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < theta d p q s t) :
    -- exponent: 0 < η ≤ r*/2
    ∀ η : ℝ, 0 < η → η ≤ rStar d q t / 2 →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀
        -- coefficient field with finite quasi-norms
        (a : CoeffField d), IsWeightedCoeffOn (cube 1) a →
        cubeQuasiNorm a s p < ⊤ →
        cubeQuasiNorm (fun x => (a x)⁻¹) t q < ⊤ →
        let N : ℝ≥0∞ :=
          cubeQuasiNorm a s p * cubeQuasiNorm (fun x => (a x)⁻¹) t q
        ∀
          -- nonnegative weighted supersolution
          (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (cube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (cube 1) u G →
          -- conclusion
          normalizedLpMoment η (cube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt N.toReal)) *
              essInfNonneg (cube (1 / 2)) u := by
  classical
  intro η hη hηr
  obtain ⟨C₀, hC₀, hroot⟩ :=
    CoarseDeGiorgi.weak_harnack_range d hd p q s t hp hq hs ht hθ η hη hηr
  let D : ℝ := (d.factorial : ℝ) ^ 2
  have hD : 0 ≤ D := by positivity
  refine ⟨C₀ * Real.sqrt D, mul_nonneg hC₀ (Real.sqrt_nonneg _), ?_⟩
  intro a ha hAfinite hAinvfinite N u G hu hsuper
  have haLp : CoarseDeGiorgiAudit.WeakHarnackLpLq.IsWeightedCoeffOn
      (CoarseDeGiorgiAudit.WeakHarnackLpLq.cube 1) a := ha
  have haAudit :=
    (CoarseDeGiorgiAudit.WeakHarnackLpLq.isWeightedCoeffOn_iff
      (CoarseDeGiorgiAudit.WeakHarnackLpLq.cube 1) a).mp haLp
  have haAudit : CoarseDeGiorgiAudit.IsWeightedCoeffOn
      (CoarseDeGiorgiAudit.originCube 1) a := by
    simpa only [CoarseDeGiorgiAudit.WeakHarnackLpLq.cube_eq] using haAudit
  have haRoot := (CoarseDeGiorgiAudit.isWeightedCoeffOn_iff
    (CoarseDeGiorgiAudit.originCube 1) a).mp haAudit
  obtain ⟨hAentries, hAinvEntries⟩ :=
    CoarseDeGiorgiAudit.Solution.BridgeBesov.weightedCoeff_entries_integrable haRoot
  obtain ⟨hup, hlow, hcb⟩ :=
    CoarseDeGiorgiAudit.Solution.BridgeBesovCube.moment_data d hd p q s t
      hp hq hs ht a haRoot hAentries hAinvEntries hAfinite hAinvfinite
  have hprodFinite : cubeQuasiNorm a s p * cubeQuasiNorm (fun x => (a x)⁻¹) t q ≠ ⊤ :=
    ENNReal.mul_ne_top hAfinite.ne hAinvfinite.ne
  have hsqrt := CoarseDeGiorgiAudit.Solution.BridgeBesov.sqrt_toReal_le_mul
    (x := CoarseDeGiorgi.contrast a haRoot s t p q hs ht hp.le hq.le)
    (y := cubeQuasiNorm a s p * cubeQuasiNorm (fun x => (a x)⁻¹) t q)
    (c := D) hD hprodFinite hcb
  have hsqrtD : Real.sqrt D = (d.factorial : ℝ) := by
    simp only [D]; exact Real.sqrt_sq (by positivity)
  have hN : N = cubeQuasiNorm a s p * cubeQuasiNorm (fun x => (a x)⁻¹) t q := rfl
  have hExp :
      Real.exp (C₀ * Real.sqrt
          (CoarseDeGiorgi.contrast a haRoot s t p q hs ht hp.le hq.le).toReal) ≤
        Real.exp ((C₀ * Real.sqrt D) * Real.sqrt N.toReal) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ C₀ * (Real.sqrt D * Real.sqrt
          (cubeQuasiNorm a s p * cubeQuasiNorm (fun x => (a x)⁻¹) t q).toReal) :=
        mul_le_mul_of_nonneg_left hsqrt hC₀
      _ = _ := by rw [hN]; ring
  have hnonnegRoot : ∀ᵐ x ∂(volume.restrict (CoarseDeGiorgi.originCube 1)),
      0 ≤ u x := by
    simpa [CoarseDeGiorgi.originCube, cube] using hu
  have hsuperLp : CoarseDeGiorgiAudit.WeakHarnackLpLq.IsWeightedSupersolution a
      (CoarseDeGiorgiAudit.WeakHarnackLpLq.cube 1) u G := hsuper
  have hsuperAudit :=
    (CoarseDeGiorgiAudit.WeakHarnackLpLq.isWeightedSupersolution_iff
      a (CoarseDeGiorgiAudit.WeakHarnackLpLq.cube 1) u G).mp hsuperLp
  have hsuperAudit : CoarseDeGiorgiAudit.IsWeightedSupersolution a
      (CoarseDeGiorgiAudit.originCube 1) u G := by
    simpa only [CoarseDeGiorgiAudit.WeakHarnackLpLq.cube_eq] using hsuperAudit
  have hsuperRoot :=
    (CoarseDeGiorgiAudit.isWeightedSupersolution_iff
      a (CoarseDeGiorgiAudit.originCube 1) u G).mp hsuperAudit
  have hbound := hroot a haRoot hup hlow u G hnonnegRoot hsuperRoot
  calc
    normalizedLpMoment η (cube (5 / 8)) u =
        CoarseDeGiorgi.normalizedLpMoment η hη
          (CoarseDeGiorgi.originCube (5 / 8)) u := by
      rw [normalizedLpMoment_eq_root η hη (cube (5 / 8)) u]
      rfl
    _ ≤ ENNReal.ofReal (Real.exp (C₀ * Real.sqrt
          (CoarseDeGiorgi.contrast a haRoot s t p q hs ht hp.le hq.le).toReal)) *
        CoarseDeGiorgi.nonnegativeEssInf
          (CoarseDeGiorgi.originCube (1 / 2)) u := hbound
    _ ≤ ENNReal.ofReal (Real.exp ((C₀ * Real.sqrt D) * Real.sqrt N.toReal)) *
        essInfNonneg (cube (1 / 2)) u := by
      rw [show essInfNonneg (cube (1 / 2)) u =
        CoarseDeGiorgi.nonnegativeEssInf
          (CoarseDeGiorgi.originCube (1 / 2)) u by rfl]
      gcongr

end CoarseDeGiorgiAudit.WeakHarnackBesov
