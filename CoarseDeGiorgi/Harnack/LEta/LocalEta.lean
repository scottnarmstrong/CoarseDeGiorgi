import CoarseDeGiorgi.Statements.LocalBoundedness
import CoarseDeGiorgi.Statements.Csub

/-!
The Theorem A / Corollary B local boundedness bounds in the form used by the Harnack chain
(`Csub`, `1 + Θ` base, `ℝ≥0∞` constants), derived from `local_boundedness`
(base `Θ`, `Θ ≤ 1 + Θ`).
-/

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.LEta

theorem cg_local_boundedness_eta_of_local_boundedness :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ γ : ℝ, 0 < γ ∧
      (∃ C_A : ℝ≥0∞, C_A < ⊤ ∧
        ∀ (a : CoeffField d),
          (ha : IsWeightedCoeffOn (originCube 1) a) →
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
          ∀ u : Vec d → ℝ, u ∈ Csub a (originCube 1) →
          LocallyBoundedAbove (originCube 1) u ∧
          ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
            eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤
              C_A * (ENNReal.ofReal (R - ρ)).rpow (-γ) *
                (1 + contrast a ha s t p q hs ht hp.le hq.le).rpow
                  (((d : ℝ) - 1) / (4 * paramTheta d p q s t)) *
                eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) ∧
            (R < 1 → eLpNorm (positivePart u) 2
              (volume.restrict (originCube R)) < ⊤)) ∧
      (∀ η : ℝ, 0 < η → η < 2 →
        ∃ C_η : ℝ≥0∞, C_η < ⊤ ∧
          ∀ (a : CoeffField d),
            (ha : IsWeightedCoeffOn (originCube 1) a) →
            upperMoment a ha s p hs hp.le < ⊤ →
            0 < lowerMoment a ha t q ht hq.le →
            ∀ u : Vec d → ℝ, u ∈ Csub a (originCube 1) →
            LocallyBoundedAbove (originCube 1) u ∧
            ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
              eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤
                C_η * (ENNReal.ofReal (R - ρ)).rpow (-2 * γ / η) *
                  (1 + contrast a ha s t p q hs ht hp.le hq.le).rpow
                    (((d : ℝ) - 1) / (2 * η * paramTheta d p q s t)) *
                  eLpNorm (positivePart u) (ENNReal.ofReal η)
                    (volume.restrict (originCube R)) ∧
              (R < 1 → eLpNorm (positivePart u) (ENNReal.ofReal η)
                (volume.restrict (originCube R)) < ⊤)) := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨γ, hγ, ⟨C_A, hCA, hA⟩, hB⟩ :=
    CoarseDeGiorgi.local_boundedness d hd p q s t hp hq hs ht hθ
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    linarith
  refine ⟨γ, hγ, ⟨ENNReal.ofReal C_A, ENNReal.ofReal_lt_top, ?_⟩, ?_⟩
  · intro a ha hup hlow u hu
    obtain ⟨G, hsub⟩ := hu
    obtain ⟨hloc, hest⟩ := hA a ha hup hlow u G hsub
    refine ⟨hloc, fun ρ R hρ hρR hR => ?_⟩
    obtain ⟨h1, h2⟩ := hest ρ R hρ hρR hR
    refine ⟨h1.trans ?_, h2⟩
    have hmono : (contrast a ha s t p q hs ht hp.le hq.le).rpow
        (((d : ℝ) - 1) / (4 * paramTheta d p q s t)) ≤
        (1 + contrast a ha s t p q hs ht hp.le hq.le).rpow
          (((d : ℝ) - 1) / (4 * paramTheta d p q s t)) :=
      ENNReal.rpow_le_rpow le_add_self (by positivity)
    simp only [ENNReal.rpow_eq_pow] at hmono ⊢
    gcongr
  · intro η hη hη2
    obtain ⟨C_η, hCη, hη'⟩ := hB η hη hη2
    refine ⟨ENNReal.ofReal C_η, ENNReal.ofReal_lt_top, ?_⟩
    intro a ha hup hlow u hu
    obtain ⟨G, hsub⟩ := hu
    obtain ⟨hloc, _⟩ := hA a ha hup hlow u G hsub
    refine ⟨hloc, fun ρ R hρ hρR hR => ?_⟩
    obtain ⟨h1, h2⟩ := hη' a ha hup hlow u G hsub ρ R hρ hρR hR
    refine ⟨?_, h2⟩
    refine h1.trans ?_
    have hmono : (contrast a ha s t p q hs ht hp.le hq.le).rpow
        (((d : ℝ) - 1) / (2 * η * paramTheta d p q s t)) ≤
        (1 + contrast a ha s t p q hs ht hp.le hq.le).rpow
          (((d : ℝ) - 1) / (2 * η * paramTheta d p q s t)) :=
      ENNReal.rpow_le_rpow le_add_self (by positivity)
    have e : -(2 * γ / η) = -2 * γ / η := by ring
    simp only [ENNReal.rpow_eq_pow, e] at hmono ⊢
    gcongr

end CoarseDeGiorgi.Harnack.LEta
