module

public import CoarseDeGiorgi.Assembly.CaccioppoliDefs
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution

@[expose] public section

namespace CoarseDeGiorgi.Assembly

open Homogenization MeasureTheory
open scoped ENNReal
open Aliases

theorem caccioppoli_cube_mono {d : ℕ} {ρ R : ℝ} (h : ρ ≤ R) :
    originCube (d := d) ρ ⊆ originCube R := by
  intro x hx i
  have hi := hx i
  constructor <;> linarith only [hi.1, hi.2, h]

theorem caccioppoli_cube_open {d : ℕ} (R : ℝ) : IsOpen (originCube (d := d) R) := by
  have he : originCube (d := d) R =
      ⋂ i : Fin d, (fun x : Vec d => x i) ⁻¹' Set.Ioo (-(R / 2)) (R / 2) := by
    ext x
    simp only [CoarseDeGiorgi.originCube, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_preimage, Set.mem_Ioo]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

theorem caccioppoli_energy_mono {d : ℕ} (a : CoeffField d) (G : Vec d → Vec d) :
    Monotone (fun R => weightedEnergy a (originCube R) G) := by
  intro ρ R h
  exact lintegral_mono_set (caccioppoli_cube_mono h)

theorem caccioppoli_energy_finite {d : ℕ} {a : CoeffField d}
    {v : Vec d → ℝ} {G : Vec d → Vec d}
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (hv : IsWeightedSubsolution a (originCube 1) v G)
    {R : ℝ} (hR : R ≤ 1) : weightedEnergy a (originCube R) G < ⊤ :=
  (caccioppoli_energy_mono a G hR).trans_lt
    (Weighted.MemH1a.energy_lt_top (caccioppoli_cube_open 1) ha hv.1)

/-- The only moment-finiteness facts used by the Caccioppoli assembly. -/
theorem caccioppoli_moments_finite {d : ℕ} {a : CoeffField d}
    {ha : IsWeightedCoeffOn (originCube 1) a} {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hrange : spatialMomentRange a ha p q s t) :
    upperMoment a ha s p hs hp.le < ⊤ ∧
      0 < lowerMoment a ha t q ht hq.le ∧
      contrast a ha s t p q hs ht hp.le hq.le < ⊤ := by
  obtain ⟨hp', hq', hs', ht', _, _, _, _, _, hU, hL⟩ := hrange
  refine ⟨hU, hL, ?_⟩
  unfold contrast
  exact ENNReal.div_lt_top hU.ne hL.ne'


end CoarseDeGiorgi.Assembly
