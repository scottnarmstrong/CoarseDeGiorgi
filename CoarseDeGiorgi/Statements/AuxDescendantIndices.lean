module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Int.Interval

@[expose] public section

namespace CoarseDeGiorgi

noncomputable section

def auxDescendantIndices {d : ℕ} (m k : ℤ) : Finset (Fin d → ℤ) := by
  classical
  by_cases h : m ≤ k
  · let N : ℤ := (((3 ^ (k - m).toNat - 1) / 2 : ℕ) : ℤ)
    let box := Finset.pi Finset.univ (fun _ : Fin d => Finset.Icc (-N) N)
    exact box.map ⟨fun f i => f i (Finset.mem_univ i), by
      intro f g hfg
      funext i
      funext hi
      have hp : hi = Finset.mem_univ i := Subsingleton.elim _ _
      cases hp
      exact congrFun hfg i⟩
  · exact ∅

end

end CoarseDeGiorgi
