module

public import CoarseDeGiorgi.Statements.SmoothGrad
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.WeightedEnergy
public import CoarseDeGiorgi.Statements.IsSmoothCore
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.MemH1a0

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization

/-- Compatibility name for the classical gradient. -/
noncomputable abbrev smoothGrad {d : ℕ} (φ : Vec d → ℝ) : Vec d → Vec d :=
  CoarseDeGiorgi.smoothGrad φ

/-- Compatibility name for the weighted coefficient hypotheses. -/
abbrev IsWeightedCoeffOn {d : ℕ} (V : Set (Vec d)) (a : CoeffField d) : Prop :=
  CoarseDeGiorgi.IsWeightedCoeffOn V a

/-- Compatibility name for the extended weighted energy. -/
noncomputable abbrev weightedEnergy {d : ℕ} (a : CoeffField d)
    (U : Set (Vec d)) (G : Vec d → Vec d) : ENNReal :=
  CoarseDeGiorgi.weightedEnergy a U G

/-- Compatibility name for the smooth core. -/
noncomputable abbrev IsSmoothCore {d : ℕ} (a : CoeffField d)
    (V : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  CoarseDeGiorgi.IsSmoothCore a V φ

/-- Compatibility name for the weighted completion. -/
noncomputable abbrev MemH1a {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  CoarseDeGiorgi.MemH1a a V u G

/-- Compatibility name for the zero-boundary completion. -/
noncomputable abbrev MemH1a0 {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (u : Vec d → ℝ) (G : Vec d → Vec d) : Prop :=
  CoarseDeGiorgi.MemH1a0 a V u G







end CoarseDeGiorgi.Weighted
