import Mathlib
import CoarseDeGiorgiAudit.Defs
import CoarseDeGiorgi.Statements.NegSobolevNorm

/-!
Bridge for the Sobolev-norm challenges (`LocalBoundednessSobolev`, `HarnackSobolev`): Mathlib-only
copies of the challenges' weak derivative arrays, fractional seminorm, Sobolev norm and negative
Sobolev norm (the same text as in the challenges), and their equality with the library
definitions `CoarseDeGiorgi.IsWeakDerivArray`, `CoarseDeGiorgi.arrayFracSeminorm`,
`CoarseDeGiorgi.sobolevNorm` and `CoarseDeGiorgi.negSobolevNorm`.
-/

open MeasureTheory
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

namespace CoarseDeGiorgiAudit.Solution.BridgeSobolev

def IsWeakDerivArray {d : ℕ} (U : Set (Vec d)) (j : ℕ) (w : Vec d → ℝ)
    (D : (Fin j → Fin d) → Vec d → ℝ) : Prop :=
  LocallyIntegrableOn w U volume ∧
    ∀ ι : Fin j → Fin d,
      LocallyIntegrableOn (D ι) U volume ∧
        ∀ φ : Vec d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ →
          HasCompactSupport φ →
          tsupport φ ⊆ U →
          ∫ x in U, w x * iteratedFDeriv ℝ j φ x (fun k => Pi.single (ι k) (1 : ℝ)) ∂volume =
            (-1 : ℝ) ^ j * ∫ x in U, D ι x * φ x ∂volume

noncomputable def euclidDist {d : ℕ} (x y : Vec d) : ℝ :=
  Real.sqrt (∑ i, (x i - y i) ^ 2)

noncomputable def arrayFracSeminorm {d : ℕ} {ι : Type*} [Fintype ι] (V : Set (Vec d))
    (σ r : ℝ) (F : ι → Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ z : Vec d × Vec d,
      ENNReal.ofReal
        (Real.sqrt (∑ i, (F i z.1 - F i z.2) ^ 2) ^ r /
          euclidDist z.1 z.2 ^ ((d : ℝ) + σ * r))
    ∂((volume.restrict V).prod (volume.restrict V))).rpow (1 / r)

noncomputable def sobolevNorm {d : ℕ} (U : Set (Vec d)) (s ξ : ℝ) (w : Vec d → ℝ) : ℝ≥0∞ :=
  ⨅ (D : (j : Fin (⌊s⌋₊ + 1)) → (Fin j → Fin d) → Vec d → ℝ)
    (_ : ∀ j : Fin (⌊s⌋₊ + 1), IsWeakDerivArray U j w (D j)),
    ((∑ j : Fin (⌊s⌋₊ + 1),
        (eLpNorm (fun x => Real.sqrt (∑ ι, D j ι x ^ 2)) (ENNReal.ofReal ξ)
          (volume.restrict U)).rpow ξ) +
      (if s - ⌊s⌋₊ = 0 then 0
        else (arrayFracSeminorm U (s - ⌊s⌋₊) ξ (D (Fin.last ⌊s⌋₊))).rpow ξ)).rpow
      (1 / ξ)

noncomputable def negSobolevNorm {d : ℕ} (U : Set (Vec d)) (b : CoeffField d)
    (s p : ℝ) : ℝ≥0∞ :=
  ⨆ (g : Vec d → ℝ) (_ : MemLp g ⊤ (volume.restrict U))
    (_ : sobolevNorm U s (p / (p - 1)) g ≤ 1),
    ENNReal.ofReal ‖Matrix.of fun i j => ∫ x in U, g x * b x i j ∂volume‖

theorem isWeakDerivArray_iff {d : ℕ} (U : Set (Vec d)) (j : ℕ) (w : Vec d → ℝ)
    (D : (Fin j → Fin d) → Vec d → ℝ) :
    IsWeakDerivArray U j w D ↔ CoarseDeGiorgi.IsWeakDerivArray U j w D := Iff.rfl

theorem euclidDist_eq {d : ℕ} (x y : Vec d) :
    euclidDist x y = CoarseDeGiorgi.euclidDist x y := by
  unfold euclidDist CoarseDeGiorgi.euclidDist Homogenization.vecNormSq Homogenization.vecDot
  simp only [sq, Pi.sub_apply]

theorem arrayFracSeminorm_eq {d : ℕ} {ι : Type*} [Fintype ι] (V : Set (Vec d))
    (σ r : ℝ) (F : ι → Vec d → ℝ) :
    arrayFracSeminorm V σ r F = CoarseDeGiorgi.arrayFracSeminorm V σ r F := by
  unfold arrayFracSeminorm CoarseDeGiorgi.arrayFracSeminorm
  simp only [euclidDist_eq]

theorem sobolevNorm_eq {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) {s ξ : ℝ} (hs : 0 ≤ s)
    (hξ : 1 ≤ ξ) (w : Vec d → ℝ) :
    sobolevNorm U s ξ w = CoarseDeGiorgi.sobolevNorm U hU s ξ hs hξ w := by
  unfold sobolevNorm CoarseDeGiorgi.sobolevNorm
  simp only [arrayFracSeminorm_eq]
  rfl

theorem negSobolevNorm_eq {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) (b : CoeffField d)
    (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U)) {s p : ℝ} (hs : 0 ≤ s)
    (hp : 1 < p) :
    negSobolevNorm U b s p = CoarseDeGiorgi.negSobolevNorm U hU b hb s p hs hp := by
  have hξ : 1 ≤ p / (p - 1) := (le_div_iff₀ (sub_pos.mpr hp)).mpr (by linarith)
  unfold negSobolevNorm CoarseDeGiorgi.negSobolevNorm
  simp only [sobolevNorm_eq hU hs hξ]

end CoarseDeGiorgiAudit.Solution.BridgeSobolev
