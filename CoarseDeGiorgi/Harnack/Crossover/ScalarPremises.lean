import CoarseDeGiorgi.Harnack.Crossover.Normalization
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

namespace CoarseDeGiorgi.Harnack.Crossover

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- The reverse estimate required by the scalar lemma is invariant under a fixed
positive scalar multiple. This is stated for unnormalized `eLpNorm`s, so the two
different cubes retain their literal measures. -/
theorem reverseMoment_positive_scale {d : ℕ} (f : Vec d → ℝ) (k : ℝ)
    (hk : 0 < k) (A : ℝ≥0∞) {a ρ R : ℝ}
    (hrev : eLpNorm f 1 (volume.restrict (originCube ρ)) ≤
      A * eLpNorm f (ENNReal.ofReal a) (volume.restrict (originCube R))) :
    eLpNorm (k • f) 1 (volume.restrict (originCube ρ)) ≤
      A * eLpNorm (k • f) (ENNReal.ofReal a)
        (volume.restrict (originCube R)) := by
  have hleft : eLpNorm (k • f) 1 (volume.restrict (originCube ρ)) =
      ENNReal.ofReal k * eLpNorm f 1 (volume.restrict (originCube ρ)) := by
    simp [eLpNorm_const_smul, Real.enorm_of_nonneg hk.le]
  have hright : eLpNorm (k • f) (ENNReal.ofReal a)
      (volume.restrict (originCube R)) =
      ENNReal.ofReal k * eLpNorm f (ENNReal.ofReal a)
        (volume.restrict (originCube R)) := by
    simp [eLpNorm_const_smul, Real.enorm_of_nonneg hk.le]
  rw [hleft, hright]
  calc
    ENNReal.ofReal k * eLpNorm f 1 (volume.restrict (originCube ρ)) ≤
        ENNReal.ofReal k * (A * eLpNorm f (ENNReal.ofReal a)
          (volume.restrict (originCube R))) := by
          gcongr
    _ = A * (ENNReal.ofReal k * eLpNorm f (ENNReal.ofReal a)
        (volume.restrict (originCube R))) := by ac_rfl

/-- Instantiate scale invariance for a shifted positive power and its negative
power. `hplus` and `hminus` are the fully quantified outputs of the moment
iterations (`l.moment.iterations`); the conclusion is precisely the two reverse
inequalities required by `l.bombieri`, with `A₂ = 2^d C₃` and `ξ = γ₆`. -/
theorem crossover_reverse_moments_of_iterations {d : ℕ}
    (U : Vec d → ℝ) (p A₂ γ₆ : ℝ) (_hA₂ : 1 ≤ A₂)
    (hplus : ∀ {a ρ R : ℝ}, 0 < a → a < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
      eLpNorm (fun x => U x ^ p) 1 (volume.restrict (originCube ρ)) ≤
        (ENNReal.ofReal (A₂ * (R - ρ) ^ (-γ₆))) ^ (1 / a) *
          eLpNorm (fun x => U x ^ p) (ENNReal.ofReal a)
            (volume.restrict (originCube R)))
    (hminus : ∀ {a ρ R : ℝ}, 0 < a → a < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
      eLpNorm (fun x => U x ^ (-p)) 1 (volume.restrict (originCube ρ)) ≤
        (ENNReal.ofReal (A₂ * (R - ρ) ^ (-γ₆))) ^ (1 / a) *
          eLpNorm (fun x => U x ^ (-p)) (ENNReal.ofReal a)
            (volume.restrict (originCube R))) :
    (∀ {a ρ R : ℝ}, 0 < a → a < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
      eLpNorm (centeredWeight (originCube (7 / 8)) U p) 1
          (volume.restrict (originCube ρ)) ≤
        (ENNReal.ofReal (A₂ * (R - ρ) ^ (-γ₆))) ^ (1 / a) *
          eLpNorm (centeredWeight (originCube (7 / 8)) U p)
            (ENNReal.ofReal a) (volume.restrict (originCube R))) ∧
    (∀ {a ρ R : ℝ}, 0 < a → a < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
      eLpNorm (centeredWeightInv (originCube (7 / 8)) U p) 1
          (volume.restrict (originCube ρ)) ≤
        (ENNReal.ofReal (A₂ * (R - ρ) ^ (-γ₆))) ^ (1 / a) *
          eLpNorm (centeredWeightInv (originCube (7 / 8)) U p)
            (ENNReal.ofReal a) (volume.restrict (originCube R))) := by
  let kplus := Real.exp (-p * volumeAverage (originCube (7 / 8))
    (fun y => Real.log (U y)))
  let kminus := Real.exp (p * volumeAverage (originCube (7 / 8))
    (fun y => Real.log (U y)))
  have hkplus : 0 < kplus := Real.exp_pos _
  have hkminus : 0 < kminus := Real.exp_pos _
  constructor
  · intro a ρ R ha0 ha1 hρ hρR hR
    have hscale := reverseMoment_positive_scale (fun x => U x ^ p) kplus hkplus
      ((ENNReal.ofReal (A₂ * (R - ρ) ^ (-γ₆))) ^ (1 / a))
      (hplus ha0 ha1 hρ hρR hR)
    have hfun : centeredWeight (originCube (7 / 8)) U p =
        kplus • (fun x => U x ^ p) := by
      funext x
      simp [centeredWeight, kplus, smul_eq_mul]
    rw [hfun]
    exact hscale
  · intro a ρ R ha0 ha1 hρ hρR hR
    have hscale := reverseMoment_positive_scale (fun x => U x ^ (-p)) kminus hkminus
      ((ENNReal.ofReal (A₂ * (R - ρ) ^ (-γ₆))) ^ (1 / a))
      (hminus ha0 ha1 hρ hρR hR)
    have hfun : centeredWeightInv (originCube (7 / 8)) U p =
        kminus • (fun x => U x ^ (-p)) := by
      funext x
      simp [centeredWeightInv, kminus, smul_eq_mul]
    rw [hfun]
    exact hscale

end
end CoarseDeGiorgi.Harnack.Crossover
