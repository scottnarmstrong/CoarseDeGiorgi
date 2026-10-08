module

public import CoarseDeGiorgi.Whitney.SeedPartition
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The signed exterior distance

The signed sup-norm distance `‖x‖ - τ/2` to the reference cube `τ□̄₀`, positive outside it.
-/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization

noncomputable section

variable {d : ℕ}

/-- Signed exterior sup-norm distance; positive outside the reference cube. -/
def seedGap (τ : ℝ) (x : Vec d) : ℝ := ‖x‖ - τ / 2

end

end CoarseDeGiorgi.Whitney

