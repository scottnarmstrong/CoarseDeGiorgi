module

public import CoarseDeGiorgi.Harnack.Iterations.MomentDomain
public import CoarseDeGiorgi.Harnack.Iterations.PowerMomentChain

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- Iterate the powered positive moment bounds up to the stopping index, then
transfer the stopped moment to a lower exponent on a fixed subset.
-/
theorem normalizedLpMoment_stopped_chain_subset_bound {d : ℕ}
    (E : Set (Vec d)) (V : ℕ → Set (Vec d)) (f : Vec d → ℝ)
    (p : ℕ → ℝ) (K : ℕ → ℝ≥0∞) (N : ℕ)
    (hp : ∀ j, 0 < p j)
    (hstep : ∀ j < N,
      (CoarseDeGiorgi.normalizedLpMoment (p (j + 1)) (hp (j + 1))
        (V (j + 1)) f) ^ (p j) ≤
          K j * (CoarseDeGiorgi.normalizedLpMoment (p j) (hp j)
            (V j) f) ^ (p j))
    (η : ℝ) (hη : 0 < η) (hηN : η ≤ p N)
    (hsubset : E ⊆ V N)
    (hf : AEStronglyMeasurable f (volume.restrict (V N)))
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤)
    (hVpos : 0 < volume (V N)) (hVtop : volume (V N) ≠ ⊤)
    (B : ℝ≥0∞)
    (hcost : (∏ j ∈ Finset.range N, K j ^ (1 / p j)) ≤ B) :
    CoarseDeGiorgi.normalizedLpMoment η hη E f ≤
      (volume E) ^ (-(1 / p N)) * (volume (V N)) ^ (1 / p N) * B *
        CoarseDeGiorgi.normalizedLpMoment (p 0) (hp 0) (V 0) f := by
  let M : ℕ → ℝ≥0∞ := fun j =>
    CoarseDeGiorgi.normalizedLpMoment (p j) (hp j) (V j) f
  have hstep' : ∀ j < N, M (j + 1) ^ (p j) ≤ K j * M j ^ (p j) := by
    intro j hj
    simpa [M] using hstep j hj
  have hchain : M N ≤
      (∏ j ∈ Finset.range N, K j ^ (1 / p j)) * M 0 :=
    finite_rpow_iteration_chain_product M K p N (fun j _ => hp j) hstep'
  have htransfer := normalizedLpMoment_subset_bound E (V N) f hη (hp N)
    hηN hsubset hf hEpos hEtop hVpos hVtop
  let F : ℝ≥0∞ := (volume E) ^ (-(1 / p N)) *
    (volume (V N)) ^ (1 / p N)
  calc
    CoarseDeGiorgi.normalizedLpMoment η hη E f ≤ F * M N := by
      simpa [F, M] using htransfer
    _ ≤ F * ((∏ j ∈ Finset.range N, K j ^ (1 / p j)) * M 0) :=
      mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = (F * (∏ j ∈ Finset.range N, K j ^ (1 / p j))) * M 0 := by ac_rfl
    _ ≤ (F * B) * M 0 := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hcost (by positivity)
    _ = (volume E) ^ (-(1 / p N)) * (volume (V N)) ^ (1 / p N) * B *
        CoarseDeGiorgi.normalizedLpMoment (p 0) (hp 0) (V 0) f := by
      simp only [F, M]

end CoarseDeGiorgi.Harnack.Iterations
