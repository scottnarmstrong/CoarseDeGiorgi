import CoarseDeGiorgi.Cubical.WhitneyIdx

/-! # Layers of the Whitney decomposition: disjointness, coverage and the volume bound -/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal

variable {d : ℕ}

/-- The maximal good cubes of level `k + l`, as indices in `𝒬_{k+l}`. -/
noncomputable def Wl (S : Set (Vec d)) (k l : ℕ) : Finset (Fin d → Fin (3 ^ (k + l))) := by
  classical
  exact Finset.univ.filter (fun z => maxGood S k (k + l) (fun i => (z i : ℕ)))

theorem mem_Wl {S : Set (Vec d)} {k l : ℕ} {z : Fin d → Fin (3 ^ (k + l))} :
    z ∈ Wl S k l ↔ maxGood S k (k + l) (fun i => (z i : ℕ)) := by
  classical
  simp [Wl]

theorem Wl_disjoint {S : Set (Vec d)} {k l l' : ℕ} {z : Fin d → Fin (3 ^ (k + l))}
    {z' : Fin d → Fin (3 ^ (k + l'))} (h : z ∈ Wl S k l) (h' : z' ∈ Wl S k l')
    (hne : (⟨l, z⟩ : Σ l, Fin d → Fin (3 ^ (k + l))) ≠ ⟨l', z'⟩) :
    Disjoint (box (k + l) (fun i => (z i : ℕ))) (box (k + l') (fun i => (z' i : ℕ))) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨hj, hz⟩ := maxGood_unique (mem_Wl.mp h) (mem_Wl.mp h') hx hx'
  have hl : l = l' := by omega
  subst hl
  apply hne
  have : z = z' := by funext i; exact Fin.ext (congrFun hz i)
  rw [this]

theorem box_subset_of_mem_Wl {S : Set (Vec d)} {k l : ℕ} {z : Fin d → Fin (3 ^ (k + l))}
    (h : z ∈ Wl S k l) : box (k + l) (fun i => (z i : ℕ)) ⊆ S :=
  box_subset_of_good (mem_Wl.mp h).2.1

theorem layer_weight {S : Set (Vec d)} (hS : IsOpenBoundedConvexDomain S) (hd : 1 ≤ d) (k : ℕ)
    (c₀ : Vec d)
    (hball : ∀ y : Vec d, (∀ i, |y i - c₀ i| < ((3 : ℝ) ^ k)⁻¹ / (2 * (d + 1))) → y ∈ S) (l : ℕ) :
    ∑ z ∈ Wl S k l, (volume (box (k + l) (fun i => (z i : ℕ)))).toReal ≤
      (10 * d * (d + 1) * ((3 : ℝ) ^ l)⁻¹) * (volume S).toReal := by
  classical
  have hSfin : volume S ≠ ⊤ := hS.isBoundedDomain.isBounded.measure_lt_top.ne
  set F : Set (Vec d) := ⋃ z ∈ Wl S k l, box (k + l) (fun i => (z i : ℕ)) with hF
  have hFS : F ⊆ S := Set.iUnion₂_subset fun z hz => box_subset_of_mem_Wl hz
  have hvolF : (volume F).toReal =
      ∑ z ∈ Wl S k l, (volume (box (k + l) (fun i => (z i : ℕ)))).toReal := by
    rw [hF, measure_biUnion_finset, ENNReal.toReal_sum]
    · intro z _
      rw [volume_box]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    · intro z hz z' hz' hne
      exact Wl_disjoint hz hz' (fun h => hne (by simpa using h))
    · intro z _; exact measurableSet_box _ _
  rw [← hvolF]
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl3 : (0 : ℝ) < (3 : ℝ) ^ l := by positivity
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have : (volume F).toReal ≤ (volume S).toReal := ENNReal.toReal_mono hSfin (measure_mono hFS)
    refine this.trans ?_
    have : (1 : ℝ) ≤ 10 * d * (d + 1) * ((3 : ℝ) ^ 0)⁻¹ := by simp; nlinarith
    nlinarith [ENNReal.toReal_nonneg (a := volume S)]
  · have hρ : 0 < ((3 : ℝ) ^ k)⁻¹ / (2 * (d + 1)) := by positivity
    set θ : ℝ := 10 * (d + 1) * ((3 : ℝ) ^ l)⁻¹ with hθ
    have hθ0 : 0 < θ := by positivity
    have key := layer_volume_le hS c₀ hρ hball hFS hθ0 (by
      intro x hx
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
      have hmax := mem_Wl.mp hz
      obtain ⟨hsub, hng⟩ := maxGood_parent (fun a => (z a).isLt) hmax (by omega : k < k + l)
      unfold good at hng
      push Not at hng
      obtain ⟨y, hy, hyS⟩ := hng
      refine ⟨y, hyS, fun a => ?_⟩
      have h1 := abs_sub_bc_lt (hsub hxz) a
      have h2 := hy a
      have hpow : ((3 : ℝ) ^ (k + l - 1))⁻¹ = 3 * ((3 : ℝ) ^ (k + l))⁻¹ := by
        obtain ⟨m, hm⟩ : ∃ m, k + l = m + 1 := ⟨k + l - 1, by omega⟩
        rw [hm, Nat.add_sub_cancel, pow_succ]; field_simp
      have e1 : θ * (((3 : ℝ) ^ k)⁻¹ / (2 * (d + 1))) = 5 * ((3 : ℝ) ^ (k + l))⁻¹ := by
        rw [hθ, pow_add]; field_simp; norm_num
      have hp : (0 : ℝ) < ((3 : ℝ) ^ (k + l))⁻¹ := by positivity
      rw [e1]
      have : |x a - y a| ≤ |x a - bc (k + l - 1) (fun a => (z a : ℕ) / 3) a| +
          |bc (k + l - 1) (fun a => (z a : ℕ) / 3) a - y a| := abs_sub_le _ _ _
      rw [abs_sub_comm (bc _ _ _) (y a)] at this
      rw [hpow] at h1 h2
      linarith)
    calc (volume F).toReal ≤ (d * θ) * (volume S).toReal := key
      _ = _ := by rw [hθ]; ring

end CoarseDeGiorgi.Cubical
