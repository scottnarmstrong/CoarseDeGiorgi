module

public import CoarseDeGiorgi.Whitney.LiftCell
public import CoarseDeGiorgi.Weighted.TestingCompactSupport
public import CoarseDeGiorgi.Weighted.Truncation.Continuity
public import CoarseDeGiorgi.Weighted.PairSeparation

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Negative excesses of supported perturbations have compact support in the domain. -/
private lemma supported_negative_excess (hV : IsOpenBoundedConvexDomain V)
    (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) (e : Vec d) (c : ℝ)
    (hboundary : ∀ x ∈ V, 0 ≤ Weighted.responseAffine e x + c)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ V) :
    MemH1a0 a V (fun x => max (-(Weighted.responseAffine e x + f x + c)) 0)
      ({x | 0 < -(Weighted.responseAffine e x + f x + c)}.indicator
        (-((fun _ => e) + smoothGrad f))) := by
  classical
  have hcore := Weighted.isSmoothCore_of_supported ha hf.1 hf.2.1
  have hq : MemH1a a V (fun x => -(Weighted.responseAffine e x + f x + c))
      (-((fun _ => e) + smoothGrad f)) :=
    Weighted.MemH1a.neg hV hne ha (lift_memH1a_add_const hV hne ha
      (Weighted.MemH1a.add hV hne ha (Weighted.responseAffine_memH1a hV ha e)
        (Weighted.memH1a_of_isSmoothCore hV.isOpen ha hcore)) c)
  apply Weighted.MemH1a.memH1a0_of_compact_support hV hne ha
    (Weighted.MemH1a.posPart hV hne ha hq) (K := tsupport f) hf.2.1 hf.2.2
  filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
  intro hxK
  have hfzero : f x = 0 := image_eq_zero_of_notMem_tsupport hxK
  rw [hfzero, add_zero]
  exact max_eq_right (neg_nonpos.mpr (hboundary x hx))

/-- A nonnegative affine datum makes the negative excess a zero-boundary pair. -/
private lemma negative_excess_memH1a0 (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) (c : ℝ)
    (hboundary : ∀ x ∈ V, 0 ≤ Weighted.responseAffine e x + c)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a a V u G)
    (hb : MemH1a0 a V (u - Weighted.responseAffine e) (G - fun _ => e)) :
    MemH1a0 a V (fun x => max (-(u x + c)) 0)
      ({x | 0 < -(u x + c)}.indicator (-G)) := by
  classical
  let b : Vec d → ℝ := Weighted.responseAffine e
  have hq : MemH1a a V (-(fun x => u x + c)) (-G) :=
    Weighted.MemH1a.neg hV hne ha (lift_memH1a_add_const hV hne ha hu c)
  obtain ⟨hbuM, _, f, hf, hc, hlocal, hE⟩ := hb
  have hcore := fun n => Weighted.isSmoothCore_of_supported ha (hf n).1 (hf n).2.1
  have hL := (Weighted.core_tendsto_l1 hV hne ha hcore hc hbuM hlocal).2
  let q : ℕ → Vec d → ℝ := fun n x => -(b x + (f n) x + c)
  let Q : ℕ → Vec d → Vec d := fun n => -((fun _ => e) + smoothGrad (f n))
  have hqn (n : ℕ) : MemH1a a V (q n) (Q n) := by
    exact Weighted.MemH1a.neg hV hne ha
      (lift_memH1a_add_const hV hne ha
        (Weighted.MemH1a.add hV hne ha (Weighted.responseAffine_memH1a hV ha e)
          (Weighted.memH1a_of_isSmoothCore hV.isOpen ha (hcore n))) c)
  have hLq : Tendsto (fun n => eLpNorm
      (q n - -(fun x => u x + c)) 1 (volume.restrict V)) atTop (𝓝 0) := by
    have heq (n : ℕ) : q n - -(fun x => u x + c) =
        -(f n - (u - Weighted.responseAffine e)) := by
      funext x
      dsimp [q, b]
      ring
    simpa only [heq, eLpNorm_neg] using hL
  have hEq : Tendsto (fun n => weightedEnergy a V
      (Q n - -G)) atTop (𝓝 0) := by
    have heq (n : ℕ) : Q n - -G =
        -(fun x => smoothGrad (f n) x - (G x - e)) := by
      funext x i
      dsimp [Q]
      ring
    have he (n : ℕ) : weightedEnergy a V (Q n - -G) =
        weightedEnergy a V (fun x => smoothGrad (f n) x - (G x - e)) := by
      rw [heq]
      exact Weighted.energy_neg _
    simpa only [he, Pi.sub_apply] using hE
  let p : Vec d → ℝ := fun x => max (-(u x + c)) 0
  let H : Vec d → Vec d := {x | 0 < -(u x + c)}.indicator (-G)
  have hp : MemH1a a V p H := Weighted.MemH1a.posPart hV hne ha hq
  have hpn (n : ℕ) : MemH1a0 a V (fun x => max (q n x) 0)
      ({x | 0 < q n x}.indicator (Q n)) :=
    supported_negative_excess hV hne ha e c hboundary (hf n)
  have hLp : Tendsto (fun n => eLpNorm
      ((fun x => max (q n x) 0) - p) 1 (volume.restrict V)) atTop (𝓝 0) :=
    Weighted.tendsto_l1_lipschitz_comp (Φ := fun t : ℝ => max t 0)
      (L := 1) (fun n => (hqn n).1) hq.1 hLq
      (LipschitzWith.id.max_const 0)
  have hEp := Weighted.tendsto_energy_positivePart hV hne ha hqn hq hLq hEq 0
  exact Weighted.memH1a0_of_tendsto hV hne ha hpn
    (Weighted.memH1a_memW11 hV hne ha hp).1 hp.2.1 hLp hEp

/-- The harmonic cell replacement preserves a nonnegative affine boundary datum. -/
theorem liftCellPair_range_nonneg (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) (c : ℝ)
    (hboundary : ∀ x ∈ V, 0 ≤ Weighted.responseAffine e x + c) :
    ∀ᵐ x ∂volume.restrict V, 0 ≤ (liftCellPair hV hne ha e).1 x + c := by
  classical
  obtain ⟨hsol, hb⟩ := liftCellPair_spec hV hne ha e
  let u := (liftCellPair hV hne ha e).1
  let G := (liftCellPair hV hne ha e).2
  have hu : MemH1a a V u G := hsol.1
  let p : Vec d → ℝ := fun x => max (-(u x + c)) 0
  let H : Vec d → Vec d := {x | 0 < -(u x + c)}.indicator (-G)
  have hp0 : MemH1a0 a V p H := negative_excess_memH1a0 hV hne ha e c hboundary hu hb
  have hp := Weighted.MemH1a0.memH1a ha hp0
  have hortho := Weighted.IsWeightedSolution.orthogonality hV hne ha hsol hp0
  have hquad : (fun x => vecDot (H x) (matVecMul (a x) (H x))) =
      (fun x => -vecDot (H x) (matVecMul (a x) (G x))) := by
    funext x
    by_cases hx : 0 < -(u x + c)
    · have hHx : H x = -G x := Set.indicator_of_mem
        (show x ∈ {x | 0 < -(u x + c)} from hx) _
      rw [hHx]
      simp only [matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]
    · have hHx : H x = 0 := Set.indicator_of_notMem
        (show x ∉ {x | 0 < -(u x + c)} from hx) _
      rw [hHx]
      simp only [vecDot_zero_left, neg_zero]
  have hHzero : weightedEnergy a V H = 0 := by
    have ht : (weightedEnergy a V H).toReal = 0 := by
      calc
        _ = ∫ x in V, vecDot (H x) (matVecMul (a x) (H x)) :=
          Weighted.energy_toReal ha hp.2.1
        _ = 0 := by rw [hquad, integral_neg, hortho.2, neg_zero]
    exact ((ENNReal.toReal_eq_zero_iff _).mp ht).resolve_right
      (Weighted.MemH1a.energy_lt_top hV.isOpen ha hp).ne
  have hpzero := (Weighted.MemH1a0.eq_zero_of_energy_zero hV hne ha hp0 hHzero).1
  filter_upwards [hpzero] with x hx
  have : -(u x + c) ≤ 0 := (le_max_left _ _).trans_eq hx
  exact neg_nonpos.mp this

end CoarseDeGiorgi.Whitney
