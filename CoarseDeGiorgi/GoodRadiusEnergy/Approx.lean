module

public import CoarseDeGiorgi.PowerCacc.CapApprox
public import CoarseDeGiorgi.PowerCacc.Geometry
public import CoarseDeGiorgi.Harnack.WeakHarnack.ApproximationBridge
public import CoarseDeGiorgi.Weighted.Truncation.Continuity
public import CoarseDeGiorgi.Statements.PositiveCap
public import CoarseDeGiorgi.Statements.PositiveCapGradient
public import CoarseDeGiorgi.Statements.H1aWeightedNorm

/-! # The truncations `(vᵢ - k)₊` of the smooth approximants

For smooth cores `vᵢ → v` in `H¹_a(□₀)` and a level `k`, the Lipschitz truncations `(vᵢ - k)₊` are
weighted Sobolev pairs converging to `(v - k)₊` in `L¹` and in energy of the gradients; they are
Lipschitz on every closed cube `τ□̄₀`, `τ < 1`. Used in the proof of Proposition
`p.good.radius.energy`. -/

@[expose] public section

namespace CoarseDeGiorgi.GoodRadiusEnergy

open Homogenization MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

variable {d : ℕ}

theorem positiveCap_top_eq (v : Vec d → ℝ) (k : ℝ) :
    positiveCap v k ⊤ = fun x => max (v x - k) 0 := by
  funext x
  simp [positiveCap, positivePart]

theorem positiveCapGradient_top_eq (v : Vec d → ℝ) (G : Vec d → Vec d) (k : ℝ) :
    positiveCapGradient v G k ⊤ = {x | k < v x}.indicator G := by
  funext x
  by_cases hx : k < v x <;>
    simp [positiveCapGradient, positiveTruncationGradient, hx]

theorem lipschitzWith_posPart (k : ℝ) : LipschitzWith 1 (fun y : ℝ => max (y - k) 0) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have := abs_max_sub_max_le_abs (x - k) (y - k) 0
  simpa [Real.dist_eq] using this

/-- The truncations of the smooth approximants converge to the truncation, in `L¹` and in energy. -/
theorem trunc_approx_tendsto [NeZero d] {a : CoeffField d}
    (ha : IsWeightedCoeffOn (originCube 1) a) {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : MemH1a a (originCube 1) v G)
    (vi : ℕ → Vec d → ℝ) (hvi : ∀ i, IsSmoothCore a (originCube 1) (vi i))
    (hN : Tendsto (fun i => h1aWeightedNorm a (originCube 1)
      (fun x => vi i x - v x) (fun x => smoothGrad (vi i) x - G x)) atTop (𝓝 0))
    (k : ℝ) :
    (∀ i, MemH1a a (originCube 1) (positiveCap (vi i) k ⊤)
      (positiveCapGradient (vi i) (smoothGrad (vi i)) k ⊤)) ∧
    Tendsto (fun i => eLpNorm (positiveCap (vi i) k ⊤ - positiveCap v k ⊤) 1
      (volume.restrict (originCube 1))) atTop (𝓝 0) ∧
    Tendsto (fun i => weightedEnergy a (originCube 1)
      (positiveCapGradient (vi i) (smoothGrad (vi i)) k ⊤ -
        positiveCapGradient v G k ⊤)) atTop (𝓝 0) := by
  let hV := Assembly.theoremA_unitCube_domain (d := d)
  have hmem (i : ℕ) : MemH1a a (originCube 1) (vi i) (smoothGrad (vi i)) :=
    Weighted.memH1a_of_isSmoothCore hV.1.isOpen ha (hvi i)
  have hsub (i : ℕ) : MemH1a a (originCube 1) (fun x => vi i x - v x)
      (fun x => smoothGrad (vi i) x - G x) := Weighted.MemH1a.sub hV.1 hV.2 ha (hmem i) hv
  obtain ⟨hL1, hE⟩ := Harnack.WeakHarnack.h1aWeightedNorm_tendsto_l1_and_energy a ha
    (fun i x => vi i x - v x) (fun i x => smoothGrad (vi i) x - G x) hsub hN
  simp only [positiveCap_top_eq, positiveCapGradient_top_eq]
  refine ⟨fun i => Weighted.MemH1a.max_sub_const hV.1 hV.2 ha (hmem i) k, ?_, ?_⟩
  · have h := Weighted.tendsto_l1_lipschitz_comp (fun i => (hmem i).1) hv.1 hL1
      (lipschitzWith_posPart k)
    exact h
  · exact Weighted.tendsto_energy_positivePart hV.1 hV.2 ha hmem hv hL1 hE k

end CoarseDeGiorgi.GoodRadiusEnergy
