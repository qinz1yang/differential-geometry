/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Set Matrix

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem dotProduct_cross_eq_zero_of_mem_affineSpan_triple {z a b x : Fin 3 → ℝ}
    (hx : x ∈ affineSpan ℝ {z, a, b}) : (x - z) ⬝ᵥ ((a - z) ⨯₃ (b - z)) = 0 := by
  have hz : z ∈ ({z, a, b} : Set (Fin 3 → ℝ)) := mem_insert z _
  have hdir : x -ᵥ z ∈ vectorSpan ℝ ({z, a, b} : Set (Fin 3 → ℝ)) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hx (subset_affineSpan ℝ _ hz)
  rw [vectorSpan_eq_span_vsub_set_right ℝ hz, vsub_eq_sub] at hdir
  refine Submodule.span_induction (p := fun w _ => w ⬝ᵥ ((a - z) ⨯₃ (b - z)) = 0)
    ?_ ?_ ?_ ?_ hdir
  · rintro w ⟨q, hq, rfl⟩
    rcases hq with rfl | rfl | rfl
    · simp
    · change (q - z) ⬝ᵥ _ = 0
      exact dot_self_cross _ _
    · change (q - z) ⬝ᵥ _ = 0
      exact dot_cross_self _ _
  · exact zero_dotProduct _
  · intro u v _ _ hu hv
    rw [add_dotProduct, hu, hv, add_zero]
  · intro c u _ hu
    rw [smul_dotProduct, hu, smul_zero]

theorem mem_affineSpan_pair_of_cross_eq_zero {z a b : Fin 3 → ℝ} (hab : a ≠ b)
    (h : (a - z) ⨯₃ (b - z) = 0) : z ∈ line[ℝ, a, b] := by
  have hdep : ¬LinearIndependent ℝ ![a - z, b - z] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent, not_not]
    exact h
  rw [LinearIndependent.pair_iff] at hdep
  push Not at hdep
  obtain ⟨s, t, hst, hne⟩ := hdep
  have hsum : s + t ≠ 0 := by
    intro h0
    have ht : t = -s := by linarith
    have hs : s • (a - b) = 0 := by
      rw [ht] at hst
      linear_combination (norm := module) hst
    rcases smul_eq_zero.mp hs with h1 | h1
    · exact hne h1 (by rw [ht, h1, neg_zero])
    · exact hab (sub_eq_zero.mp h1)
  have hc : (s + t) * (t / (s + t)) = t := by field_simp
  have hz : z = AffineMap.lineMap a b (t / (s + t)) := by
    rw [AffineMap.lineMap_apply_module']
    apply smul_right_injective (Fin 3 → ℝ) hsum
    change (s + t) • z = (s + t) • ((t / (s + t)) • (b - a) + a)
    rw [smul_add, smul_smul, hc]
    linear_combination (norm := module) -hst
  rw [hz]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

theorem mem_of_mem_affineSpan_triple_inter {z a₁ a₂ b₁ b₂ x : Fin 3 → ℝ} (ha : a₁ ≠ a₂)
    (hb : b₁ ≠ b₂) (hb₁ : b₁ ∉ line[ℝ, a₁, a₂]) (hxa : x ∈ affineSpan ℝ {z, a₁, a₂})
    (hxb : x ∈ affineSpan ℝ {z, b₁, b₂}) :
    x ∈ line[ℝ, a₁, a₂] ∨ x ∈ line[ℝ, b₁, b₂] ∨ x ∈ affineSpan ℝ {a₁, a₂, b₁} ∨
      ∃ s : ℝ, x = z + s • (((a₁ - z) ⨯₃ (a₂ - z)) ⨯₃ ((b₁ - z) ⨯₃ (b₂ - z))) := by
  have h₁ := dotProduct_cross_eq_zero_of_mem_affineSpan_triple hxa
  have h₂ := dotProduct_cross_eq_zero_of_mem_affineSpan_triple hxb
  by_cases hn₁ : (a₁ - z) ⨯₃ (a₂ - z) = 0
  · left
    have hz := mem_affineSpan_pair_of_cross_eq_zero ha hn₁
    refine (affineSpan_le.mpr ?_) hxa
    rintro q (rfl | rfl | rfl)
    · exact hz
    · exact left_mem_affineSpan_pair ℝ _ _
    · exact right_mem_affineSpan_pair ℝ _ _
  by_cases hn₂ : (b₁ - z) ⨯₃ (b₂ - z) = 0
  · right
    left
    have hz := mem_affineSpan_pair_of_cross_eq_zero hb hn₂
    refine (affineSpan_le.mpr ?_) hxb
    rintro q (rfl | rfl | rfl)
    · exact hz
    · exact left_mem_affineSpan_pair ℝ _ _
    · exact right_mem_affineSpan_pair ℝ _ _
  right
  right
  by_cases hN : ((a₁ - z) ⨯₃ (a₂ - z)) ⨯₃ ((b₁ - z) ⨯₃ (b₂ - z)) = 0
  · left
    set n₁ := (a₁ - z) ⨯₃ (a₂ - z) with hn₁def
    set n₂ := (b₁ - z) ⨯₃ (b₂ - z) with hn₂def
    have hdep : ¬LinearIndependent ℝ ![n₁, n₂] := by
      rw [← crossProduct_ne_zero_iff_linearIndependent, not_not]
      exact hN
    rw [LinearIndependent.pair_iff' hn₁] at hdep
    push Not at hdep
    obtain ⟨c, hc⟩ := hdep
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hn₂ hc.symm
    have hv₁ : (b₁ - z) ⬝ᵥ n₁ = 0 := by
      have h := dot_self_cross (b₁ - z) (b₂ - z)
      rw [← hn₂def, ← hc, dotProduct_smul, smul_eq_mul] at h
      exact (mul_eq_zero.mp h).resolve_left hc0
    have hu₁ : (a₁ - z) ⬝ᵥ n₁ = 0 := dot_self_cross _ _
    have hu₂ : (a₂ - z) ⬝ᵥ n₁ = 0 := dot_cross_self _ _
    let f : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => y ⬝ᵥ n₁
        map_add' := fun u v => add_dotProduct u v n₁
        map_smul' := fun r u => smul_dotProduct r u n₁ }
    have hfn : f n₁ ≠ 0 := by
      change n₁ ⬝ᵥ n₁ ≠ 0
      exact fun h => hn₁ (dotProduct_self_eq_zero.mp h)
    have hrange : LinearMap.range f = ⊤ := by
      refine eq_top_iff.mpr fun r _ => ⟨(r / f n₁) • n₁, ?_⟩
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ r hfn]
    have hker : Module.finrank ℝ (LinearMap.ker f) = 2 := by
      have h := LinearMap.finrank_range_add_finrank_ker f
      rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
      omega
    have hP : a₂ - a₁ ∈ LinearMap.ker f := by
      change (a₂ - a₁) ⬝ᵥ n₁ = 0
      have heq : a₂ - a₁ = (a₂ - z) - (a₁ - z) := by abel
      rw [heq, sub_dotProduct, hu₂, hu₁, sub_zero]
    have hQ : b₁ - a₁ ∈ LinearMap.ker f := by
      change (b₁ - a₁) ⬝ᵥ n₁ = 0
      have heq : b₁ - a₁ = (b₁ - z) - (a₁ - z) := by abel
      rw [heq, sub_dotProduct, hv₁, hu₁, sub_zero]
    have hy : x - a₁ ∈ LinearMap.ker f := by
      change (x - a₁) ⬝ᵥ n₁ = 0
      have heq : x - a₁ = (x - z) - (a₁ - z) := by abel
      rw [heq, sub_dotProduct, h₁, hu₁, sub_zero]
    have hind : LinearIndependent ℝ ![a₂ - a₁, b₁ - a₁] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · rw [ht, zero_smul, add_zero] at hst
        refine ⟨(smul_eq_zero.mp hst).resolve_right (sub_ne_zero.mpr ha.symm), ht⟩
      · exfalso
        apply hb₁
        have hb₁eq : b₁ = AffineMap.lineMap a₁ a₂ (-(s / t)) := by
          rw [AffineMap.lineMap_apply_module']
          apply smul_right_injective (Fin 3 → ℝ) ht
          change t • b₁ = t • ((-(s / t)) • (a₂ - a₁) + a₁)
          have hts : t * (-(s / t)) = -s := by field_simp
          rw [smul_add, smul_smul, hts]
          linear_combination (norm := module) hst
        rw [hb₁eq]
        exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
    have hspan : Submodule.span ℝ (range ![a₂ - a₁, b₁ - a₁]) = LinearMap.ker f := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]
        rintro q ⟨i, rfl⟩
        fin_cases i
        · exact hP
        · exact hQ
      · rw [finrank_span_eq_card hind, hker, Fintype.card_fin]
    rw [← hspan, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, union_empty,
      singleton_union, Submodule.mem_span_pair] at hy
    obtain ⟨α, β, hαβ⟩ := hy
    have hdir : α • (a₂ - a₁) + β • (b₁ - a₁) ∈
        (affineSpan ℝ ({a₁, a₂, b₁} : Set (Fin 3 → ℝ))).direction := by
      rw [direction_affineSpan]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
      · exact vsub_mem_vectorSpan ℝ (by simp) (by simp)
      · exact vsub_mem_vectorSpan ℝ (by simp) (by simp)
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hdir
      (subset_affineSpan ℝ ({a₁, a₂, b₁} : Set (Fin 3 → ℝ)) (mem_insert a₁ _))
    rw [hαβ, vadd_eq_add, sub_add_cancel] at hmem
    exact hmem
  · right
    set N := ((a₁ - z) ⨯₃ (a₂ - z)) ⨯₃ ((b₁ - z) ⨯₃ (b₂ - z)) with hNdef
    have hcr : N ⨯₃ (x - z) = 0 := by
      rw [← cross_anticomm, hNdef, cross_cross_eq_smul_sub_smul', h₂, dotProduct_comm, h₁,
        zero_smul, zero_smul, sub_zero, neg_zero]
    have hdep : ¬LinearIndependent ℝ ![N, x - z] := by
      rw [← crossProduct_ne_zero_iff_linearIndependent, not_not]
      exact hcr
    rw [LinearIndependent.pair_iff' hN] at hdep
    push Not at hdep
    obtain ⟨s, hs⟩ := hdep
    exact ⟨s, by rw [hs]; abel⟩

theorem exists_contDiff_of_mem_affineSpan_triple_inter
    (p d a₁ a₂ b₁ b₂ : EuclideanSpace ℝ (Fin 3)) (ha : a₁ ≠ a₂) (hb : b₁ ≠ b₂)
    (hb₁ : b₁ ∉ line[ℝ, a₁, a₂]) :
    ∃ f : ℝ × ℝ → EuclideanSpace ℝ (Fin 3), ContDiff ℝ 1 f ∧
      ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)),
        x ∈ affineSpan ℝ {p + t • d, a₁, a₂} → x ∈ affineSpan ℝ {p + t • d, b₁, b₂} →
          x ∈ line[ℝ, a₁, a₂] ∨ x ∈ line[ℝ, b₁, b₂] ∨ x ∈ affineSpan ℝ {a₁, a₂, b₁} ∨
            x ∈ range f := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] (Fin 3 → ℝ) := e.toLinearEquiv.toLinearMap.toAffineMap
  let A' : (Fin 3 → ℝ) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    e.symm.toLinearEquiv.toLinearMap.toAffineMap
  have hmap : ∀ {S : Set (EuclideanSpace ℝ (Fin 3))} {x : EuclideanSpace ℝ (Fin 3)},
      x ∈ affineSpan ℝ S → e x ∈ affineSpan ℝ (e '' S) := by
    intro S x hx
    have h := AffineSubspace.mem_map_of_mem A hx
    rw [AffineSubspace.map_span] at h
    exact h
  have hmap' : ∀ {S : Set (Fin 3 → ℝ)} {x : Fin 3 → ℝ},
      x ∈ affineSpan ℝ S → e.symm x ∈ affineSpan ℝ (e.symm '' S) := by
    intro S x hx
    have h := AffineSubspace.mem_map_of_mem A' hx
    rw [AffineSubspace.map_span] at h
    exact h
  have hback : ∀ (S : Set (EuclideanSpace ℝ (Fin 3))) (x : EuclideanSpace ℝ (Fin 3)),
      e x ∈ affineSpan ℝ (e '' S) → x ∈ affineSpan ℝ S := by
    intro S x hx
    have h := hmap' hx
    rwa [e.symm_apply_apply, ← image_comp, show e.symm ∘ e = id from funext e.symm_apply_apply,
      image_id] at h
  let C : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : ((Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ≃ₗ[ℝ] _).toLinearMap
        ∘ₗ crossProduct)
  have hC : ∀ u v : Fin 3 → ℝ, C u v = u ⨯₃ v := fun _ _ => rfl
  let z : ℝ → Fin 3 → ℝ := fun t => e (p + t • d)
  let g : ℝ × ℝ → Fin 3 → ℝ := fun ts =>
    z ts.1 + ts.2 • C (C (e a₁ - z ts.1) (e a₂ - z ts.1)) (C (e b₁ - z ts.1) (e b₂ - z ts.1))
  have hz : ContDiff ℝ 1 fun ts : ℝ × ℝ => z ts.1 :=
    e.contDiff.comp (contDiff_const.add (contDiff_fst.smul contDiff_const))
  have hsub : ∀ q : EuclideanSpace ℝ (Fin 3), ContDiff ℝ 1 fun ts : ℝ × ℝ => e q - z ts.1 :=
    fun q => contDiff_const.sub hz
  have hcross : ∀ {u v : ℝ × ℝ → Fin 3 → ℝ}, ContDiff ℝ 1 u → ContDiff ℝ 1 v →
      ContDiff ℝ 1 fun ts => C (u ts) (v ts) :=
    fun hu hv => (C.contDiff.comp hu).clm_apply hv
  have hg : ContDiff ℝ 1 g :=
    hz.add (contDiff_snd.smul (hcross (hcross (hsub a₁) (hsub a₂)) (hcross (hsub b₁) (hsub b₂))))
  refine ⟨fun ts => e.symm (g ts), e.symm.contDiff.comp hg, fun t x hxa hxb => ?_⟩
  have hxa' : e x ∈ affineSpan ℝ {z t, e a₁, e a₂} := by
    have h := hmap hxa
    rwa [image_insert_eq, image_insert_eq, image_singleton] at h
  have hxb' : e x ∈ affineSpan ℝ {z t, e b₁, e b₂} := by
    have h := hmap hxb
    rwa [image_insert_eq, image_insert_eq, image_singleton] at h
  have hb₁' : e b₁ ∉ line[ℝ, e a₁, e a₂] := by
    intro h
    apply hb₁
    apply hback
    rwa [image_insert_eq, image_singleton]
  rcases mem_of_mem_affineSpan_triple_inter (e.injective.ne ha) (e.injective.ne hb) hb₁' hxa'
      hxb' with h | h | h | ⟨s, hs⟩
  · left
    apply hback
    rwa [image_insert_eq, image_singleton]
  · right
    left
    apply hback
    rwa [image_insert_eq, image_singleton]
  · right
    right
    left
    apply hback
    rwa [image_insert_eq, image_insert_eq, image_singleton]
  · right
    right
    right
    refine ⟨(t, s), ?_⟩
    change e.symm (g (t, s)) = x
    rw [← e.symm_apply_apply x, hs]
    rfl

end DifferentialGeometry.Topology.PiecewiseLinear
