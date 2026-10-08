import CoarseDeGiorgi.Endpoint.Reconstruction.WeightedLimit
import CoarseDeGiorgi.Endpoint.Potential.Params
import CoarseDeGiorgi.Statements.UpperMoment

/-! # Dirichlet reconstruction with the endpoint scales -/
namespace CoarseDeGiorgi.Endpoint.Reconstruction
open Homogenization MeasureTheory Filter
open scoped ENNReal Topology BigOperators
noncomputable section

theorem reconstruction_lr_scale (k : ℕ) (t : ℝ) :
    ENNReal.ofReal ((3 : ℝ) ^ (-((k : ℝ) * (1 - t)))) *
      ENNReal.ofReal ((3 : ℝ) ^ (-((k : ℝ) * t))) =
        ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℤ))) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_intCast]
  congr 2
  simp only [Int.cast_neg, Int.cast_natCast]
  ring

theorem reconstruction_sup_scale {d : ℕ} (hd : 3 ≤ d) {q t : ℝ}
    (hq : 1 < q) (ht : 0 < t) (ht1 : t < 1) (k : ℕ) :
    ENNReal.ofReal ((3 : ℝ) ^ ((d : ℝ) / rStarParam (d := d) q t * (k : ℝ))) *
      ENNReal.ofReal ((3 : ℝ) ^ (-((k : ℝ) * t))) =
        ENNReal.ofReal ((3 : ℝ) ^ ((k : ℝ) * ((d : ℝ) / paramR q - 1))) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hi := (Potential.rStar_facts hd hq ht ht1).2.2.1
  congr 2
  nlinarith

theorem dirichlet_reconstruction_proof (d : ℕ) (_hd : 3 ≤ d) (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p s t : ℝ) (hp : 1 < p) (hs : 0 < s) (ht : 0 < t),
        0 < paramTheta d p q s t →
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
          MemH1a0 a (originCube 1) v G →
          ∃ vk : ℕ → Vec d → ℝ,
            Filter.Tendsto
              (fun N : ℕ => eLpNorm (fun x => v x - ∑ k ∈ Finset.Icc 1 N, vk k x)
                (ENNReal.ofReal (paramR q)) (volume.restrict (originCube 1)))
              Filter.atTop (nhds 0) ∧
            ∀ k : ℕ, 1 ≤ k →
              AEStronglyMeasurable (vk k) (volume.restrict (originCube 1)) ∧
              eLpNorm (vk k) (ENNReal.ofReal (paramR q)) (volume.restrict (originCube 1)) ≤
                ENNReal.ofReal C * ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * (1 - t)))) *
                  (ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
                    (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q))) *
                  (weightedEnergy a (originCube 1) G).rpow (1 / 2) ∧
              eLpNorm (vk k) ⊤ (volume.restrict (originCube 1)) ≤
                ENNReal.ofReal C *
                  ENNReal.ofReal (Real.rpow 3 ((d : ℝ) / rStarParam (d := d) q t * (k : ℝ))) *
                  (ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
                    (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q))) *
                  (weightedEnergy a (originCube 1) G).rpow (1 / 2)
 := by
  obtain ⟨C, hC, hblocks⟩ := exists_weighted_dirichlet_blocks _hd hq
  refine ⟨C, hC, ?_⟩
  intro p s t hp hs ht htheta a ha _hu hl v G hv
  let : NeZero d := ⟨by omega⟩
  have ht1 := Potential.lt_one_of_paramTheta_pos _hd hp hq hs htheta
  have hcost := blockCost_tsum_ne_top a ha hq ht ht1 hl
  obtain ⟨w, _hw0, hbounds⟩ := hblocks a ha v G hv
  have hw : ∀ k : ℕ, 1 ≤ k → UnitDirichletEquation (w k) (fineIncrement (k - 1) G) :=
    fun k hk => (hbounds k hk).1
  refine ⟨fun k => (w k).toH1Function.toFun, ?_, ?_⟩
  · apply weighted_reconstruction_converges hq a ha C ?_ hv w hw hcost
    intro f H hf
    obtain ⟨W, _, hW⟩ := hblocks a ha f H hf
    refine ⟨W, fun k hk => ⟨(hW k hk).1, ?_⟩⟩
    simpa only [blockCost, mul_assoc] using (hW k hk).2.1
  · intro k hk
    have hm : AEStronglyMeasurable (w k).toH1Function.toFun
        (volume.restrict (CoarseDeGiorgi.originCube 1)) := by
      rw [originCube_one_eq_openCubeSet]
      exact (w k).toH1Function.memL2.aestronglyMeasurable
    refine ⟨hm, ((hbounds k hk).2.1).trans_eq ?_, ((hbounds k hk).2.2).trans_eq ?_⟩
    · simp only [ENNReal.rpow_eq_pow, Real.rpow_eq_pow]
      rw [← reconstruction_lr_scale k t]
      ring
    · simp only [ENNReal.rpow_eq_pow, Real.rpow_eq_pow]
      rw [← reconstruction_sup_scale _hd hq ht ht1 k]
      ring

end
end CoarseDeGiorgi.Endpoint.Reconstruction
