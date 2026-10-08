import CoarseDeGiorgi.Foundations.FracGeometry.Defs
import CoarseDeGiorgi.Statements.EuclidNorm
import CoarseDeGiorgi.Statements.AuxAverage
import CoarseDeGiorgi.Statements.AuxCube
import CoarseDeGiorgi.Statements.FracSeminorm

/-! # Exact auxiliary-grid definitions for fractional reconstruction -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Euclidean length on the project carrier, whose default norm is the sup norm. -/
def euclidNorm {d : ℕ} (v : Vec d) : ℝ :=
  Real.sqrt (vecNormSq v)

/-- The open auxiliary cube `z * 3^(-m) + 3 □_{-m}`, the threefold enlargement of a triadic cube. -/
def auxCube {d : ℕ} (m : ℤ) (z : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ i, |x i - (z i : ℝ) * (3 : ℝ) ^ (-m)| <
    ((3 : ℝ) ^ (1 - m)) / 2}

/-- Integer offsets indexing the open descendants of an auxiliary cube. -/
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

/-- One open descendant of an auxiliary cube, with side `3^(1-k)`. -/
def auxDescendantCube {d : ℕ} (m k : ℤ) (z n : Fin d → ℤ) : Set (Vec d) :=
  {x | ∀ i, |x i - ((z i : ℝ) * (3 : ℝ) ^ (-m) +
      (n i : ℝ) * (3 : ℝ) ^ (1 - k))| < ((3 : ℝ) ^ (1 - k)) / 2}

/-- Vector average on one auxiliary descendant, normalized by its volume `3^((1-k)d)`. -/
def auxDescendantAverage {d : ℕ} (m k : ℤ) (z n : Fin d → ℤ)
    (f : Vec d → Vec d) : Vec d := fun i =>
  (((3 : ℝ) ^ (1 - k)) ^ d)⁻¹ *
    ∫ x in auxDescendantCube m k z n, f x i ∂volume

/-- Stepwise descendant averages, zero outside the auxiliary cube. -/
def auxAverage {d : ℕ} (m k : ℤ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) : Vec d → Vec d := by
  classical
  exact fun x => (auxDescendantIndices m k).sum fun n =>
      if x ∈ auxDescendantCube m k z n then auxDescendantAverage m k z n f else 0

variable {d : ℕ}

/-- The copied Euclidean length reuses the existing comparison infrastructure. -/
theorem euclidNorm_eq_eNorm2 (v : Vec d) : euclidNorm v = Euclid.eNorm2 v := rfl

/-- Exact bridge to the `Statements/` auxiliary cube. -/
theorem auxCube_eq_statement (m : ℤ) (z : Fin d → ℤ) :
    auxCube m z = CoarseDeGiorgi.auxCube m z := rfl

theorem auxDescendantCube_eq_statement (m k : ℤ) (z n : Fin d → ℤ) :
    auxDescendantCube m k z n = CoarseDeGiorgi.auxDescendantCube m k z n := rfl

/-- The imported fractional definition is exactly the `Statements/` one. -/
theorem fracSeminorm_eq_statement (V : Set (Vec d)) (α r : ℝ) (w : Vec d → ℝ) :
    FracGeometry.fracSeminorm V α r w = CoarseDeGiorgi.fracSeminorm V α r w := rfl

end

end CoarseDeGiorgi.Foundations.Reconstruction
