import CoarseDeGiorgi.Endpoint.Potential.Core
import CoarseDeGiorgi.Whitney.Harmonic.Linear
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.MemH1a0
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.LowerCellAverage
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.RStarParam
import CoarseDeGiorgi.Statements.WeightedEnergy
import CoarseDeGiorgi.Statements.SmoothGrad
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Endpoint

open CoarseDeGiorgi.Endpoint.Potential Filter Topology

/-- `p.endpoint.potential`, from `l.dirichlet.reconstruction`, which is the hypothesis `hrec`. -/
theorem endpoint_potential_of_reconstruction (d : ℕ) (_hd : 3 ≤ d) (q t : ℝ) (hq : 1 < q)
    (ht : 0 < t)
    (hrec : ∃ C : ℝ, 0 ≤ C ∧
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
                  (weightedEnergy a (originCube 1) G).rpow (1 / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p s : ℝ) (hp : 1 < p) (hs : 0 < s),
        0 < paramTheta d p q s t →
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (ν : Measure (Vec d)), IsFiniteMeasure ν → ν (originCube 1)ᶜ = 0 →
          (∃ M : ℝ, 0 ≤ M ∧
            ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
              tsupport φ ⊆ originCube 1 →
              ENNReal.ofReal |∫ x, φ x ∂ν| ≤
                ENNReal.ofReal M *
                  (weightedEnergy a (originCube 1) (smoothGrad φ)).rpow (1 / 2)) →
        ∀ (v : Vec d → ℝ) (Gv : Vec d → Vec d),
          MemH1a0 a (originCube 1) v Gv →
          (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
              tsupport φ ⊆ originCube 1 →
              ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume =
                ∫ x, φ x ∂ν) →
          eLpNorm v (ENNReal.ofReal (rStarParam (d := d) q t / 2))
              (volume.restrict (originCube 1)) ≤
            ENNReal.ofReal C * (lowerMoment a ha t q ht hq.le)⁻¹ * ν (originCube 1) := by
  obtain ⟨C₀, hC₀, H⟩ := hrec
  by_cases ht1 : t < 1
  swap
  · refine ⟨0, le_rfl, ?_⟩
    intro p s hp hs hθ
    exact absurd (lt_one_of_paramTheta_pos _hd hp hq hs hθ) ht1
  obtain ⟨hg1, hrs1, hsum, hg1rs, hrlt⟩ := rStar_facts _hd hq ht ht1
  set rs := rStarParam (d := d) q t with hrs
  set g₁ : ℝ := (d : ℝ) / rs with hg₁
  set A : ℝ≥0∞ := ENNReal.ofReal (C₀ * (3 : ℝ) ^ (g₁ + (1 - t))) with hA
  set ρ₁ : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ (-g₁)) with hρ₁
  set ρ₂ : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ (-(1 - t))) with hρ₂
  set G : ℝ≥0∞ := (1 - ρ₁)⁻¹ + (1 - ρ₂)⁻¹ with hG
  set κ : ℝ≥0∞ := ENNReal.ofReal (1 - (3 : ℝ) ^ (-t)) with hκ
  set Q : ℝ≥0∞ := ENNReal.ofReal 2 * A ^ 2 * (G * κ⁻¹) ^ 2 with hQ
  have hρ₁lt : ρ₁ < 1 := by
    rw [hρ₁, ENNReal.ofReal_lt_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρ₂lt : ρ₂ < 1 := by
    rw [hρ₂, ENNReal.ofReal_lt_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hκpos : κ ≠ 0 := by
    rw [hκ]
    have : (3 : ℝ) ^ (-t) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    simpa using this
  have hκtop : κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hGtop : G ≠ ⊤ := by
    rw [hG]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩ <;> rw [Ne, ENNReal.inv_eq_top, tsub_eq_zero_iff_le, not_le]
    · exact hρ₁lt
    · exact hρ₂lt
  have hQtop : Q ≠ ⊤ := by
    rw [hQ]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) (ENNReal.pow_ne_top
        (ENNReal.mul_ne_top hGtop (ENNReal.inv_ne_top.2 hκpos)))
  refine ⟨Q.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro p s hp hs hθ a ha hup hlow ν hfin hν hM v Gv hv heq
  obtain ⟨hV, hne⟩ := originCube_one_domain (d := d)
  set b : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
    (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q)) with hb
  have hrec' : ∀ (f : Vec d → ℝ) (Gf : Vec d → Vec d), MemH1a0 a (originCube 1) f Gf →
      ∃ vk : ℕ → Vec d → ℝ,
        Tendsto (fun N : ℕ => eLpNorm (fun x => f x - ∑ k ∈ Finset.Icc 1 N, vk k x)
          (ENNReal.ofReal (paramR q)) (volume.restrict (originCube 1))) atTop (𝓝 0) ∧
        ∀ k : ℕ, 1 ≤ k →
          AEStronglyMeasurable (vk k) (volume.restrict (originCube 1)) ∧
          eLpNorm (vk k) (ENNReal.ofReal (paramR q)) (volume.restrict (originCube 1)) ≤
            ENNReal.ofReal C₀ * ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * (1 - t)))) * b k *
              (weightedEnergy a (originCube 1) Gf).rpow (1 / 2) ∧
          eLpNorm (vk k) ⊤ (volume.restrict (originCube 1)) ≤
            ENNReal.ofReal C₀ *
              ENNReal.ofReal (Real.rpow 3 ((d : ℝ) / rStarParam (d := d) q t * (k : ℝ))) * b k *
                (weightedEnergy a (originCube 1) Gf).rpow (1 / 2) :=
    fun f Gf hf => H p s t hp hs ht hθ a ha hup hlow f Gf hf
  -- a measurable representative
  have hvm0 : AEStronglyMeasurable v (volume.restrict (originCube 1)) := hv.1
  set v₀ := hvm0.mk v with hv₀
  have hvv₀ : v =ᵐ[volume.restrict (originCube 1)] v₀ := hvm0.ae_eq_mk
  have hv₀m : Measurable v₀ := hvm0.stronglyMeasurable_mk.measurable
  have hv₀H : MemH1a0 a (originCube 1) v₀ Gv :=
    Whitney.Harmonic.memH1a0_congr_ae hv hvv₀ Filter.EventuallyEq.rfl
  have hcore := core_bound _hd hq ht ht1 hC₀ ha b hrec' ν hν hv₀m hv₀H heq
  rw [eLpNorm_congr_ae hvv₀]
  refine hcore.trans ?_
  have hlow_eq : (lowerMoment a ha t q ht hq.le)⁻¹ = (κ * ∑' k, b k) ^ 2 := by
    show ((κ * ∑' k, b k) ^ (-2 : ℝ))⁻¹ = _
    rw [ENNReal.rpow_neg, inv_inv]
    exact_mod_cast ENNReal.rpow_natCast (κ * ∑' k, b k) 2
  have hQ' : ENNReal.ofReal Q.toReal = Q := ENNReal.ofReal_toReal hQtop
  rw [hlow_eq, hQ']
  apply le_of_eq
  congr 1
  calc ENNReal.ofReal 2 * A ^ 2 * (G * ∑' k, b k) ^ 2
      = ENNReal.ofReal 2 * A ^ 2 * ((G * κ⁻¹) * (κ * ∑' k, b k)) ^ 2 := by
        congr 2
        rw [mul_assoc, ← mul_assoc κ⁻¹, ENNReal.inv_mul_cancel hκpos hκtop, one_mul]
    _ = Q * (κ * ∑' k, b k) ^ 2 := by rw [hQ]; ring

end CoarseDeGiorgi.Endpoint
