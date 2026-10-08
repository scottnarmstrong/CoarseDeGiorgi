module

public import Mathlib
public import CoarseDeGiorgiAudit.DefsCells

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit

noncomputable def upperDirectionalResponseSol {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (e : Vec d) : EReal :=
  ⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
    (_ : IsWeightedSolution a V w G),
    ((volumeAverage V
      (fun x =>
        -vecDot (G x) (matVecMul (a x) (G x)) +
          2 * vecDot e (matVecMul (a x) (G x))) : ℝ) : EReal)

noncomputable def lowerDirectionalResponse {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (e : Vec d) : EReal :=
  ⨆ (w : Vec d → ℝ) (G : Vec d → Vec d)
    (_ : IsWeightedSolution a V w G),
    ((volumeAverage V
      (fun x =>
        -vecDot (G x) (matVecMul (a x) (G x)) +
          2 * vecDot e (G x)) : ℝ) : EReal)

noncomputable def upperCellAverageOf {d : ℕ}
    (A : (k : ℕ) → SimplexIndex d k → Mat d) (k : ℕ) (p : ℝ) : ℝ := by
  classical
  exact
    ((triangulation (d := d) k).attach.sum fun η =>
      Real.rpow ‖A k ⟨η.1, η.2⟩‖ p) /
        ((triangulation (d := d) k).card : ℝ)

noncomputable def lowerCellAverageOf {d : ℕ}
    (B : (k : ℕ) → SimplexIndex d k → Mat d) (k : ℕ) (q : ℝ) : ℝ := by
  classical
  exact
    ((triangulation (d := d) k).attach.sum fun η =>
      Real.rpow ‖B k ⟨η.1, η.2⟩‖ q) /
        ((triangulation (d := d) k).card : ℝ)

noncomputable def upperMomentOf {d : ℕ}
    (A : (k : ℕ) → SimplexIndex d k → Mat d) (s p : ℝ)
    (_hs : 0 < s) (_hp : 1 ≤ p) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
    ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal (upperCellAverageOf A k p)).rpow (1 / (2 * p))) ^ 2

noncomputable def lowerMomentOf {d : ℕ}
    (B : (k : ℕ) → SimplexIndex d k → Mat d) (t q : ℝ)
    (_ht : 0 < t) (_hq : 1 ≤ q) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 - Real.rpow 3 (-t)) *
    ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
        (ENNReal.ofReal (lowerCellAverageOf B k q)).rpow (1 / (2 * q))).rpow (-2)

noncomputable def contrastOf {d : ℕ}
    (A B : (k : ℕ) → SimplexIndex d k → Mat d) (s t p q : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hp : 1 ≤ p) (hq : 1 ≤ q) : ℝ≥0∞ :=
  upperMomentOf A s p hs hp / lowerMomentOf B t q ht hq

end CoarseDeGiorgiAudit
