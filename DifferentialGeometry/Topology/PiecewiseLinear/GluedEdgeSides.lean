/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.ConeComplex
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_linearEquiv_prod_of_independent_pair {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2) {e n : E}
    (hen : ∀ α β : ℝ, α • e + β • n = 0 → α = 0 ∧ β = 0) :
    ∃ G : E ≃ₗ[ℝ] ℝ × ℝ, ∀ α β : ℝ, G (α • e + β • n) = (α, β) := by
  let T : (ℝ × ℝ) →ₗ[ℝ] E :=
    { toFun := fun p => p.1 • e + p.2 • n
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, RingHom.id_apply,
          smul_add] }
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    obtain ⟨h0, h1⟩ := hen p.1 p.2 hp
    exact Prod.ext h0 h1
  have hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ E := by
    rw [hE, Module.finrank_prod, Module.finrank_self]
  let Te : (ℝ × ℝ) ≃ₗ[ℝ] E := LinearEquiv.ofBijective T
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  refine ⟨Te.symm, fun α β => ?_⟩
  have h : Te (α, β) = α • e + β • n := rfl
  rw [← h, LinearEquiv.symm_apply_apply]

section Sides

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_apply_sub_eq_mul_of_mem_convexHull_insert [DecidableEq E] {s : Finset E}
    {c x z : E}
    (hc : c ∉ s) (f : E →ₗ[ℝ] ℝ) (hs : ∀ v ∈ s, f (v - x) = 0)
    (hz : z ∈ convexHull ℝ ((insert c s : Finset E) : Set E)) :
    ∃ r : ℝ, 0 ≤ r ∧ f (z - x) = r * f (c - x) := by
  have hconv : Convex ℝ {q : E | f (q - x) = 0} := by
    have h : {q : E | f (q - x) = 0} =
        (f.toAffineMap.comp ((AffineEquiv.vaddConst ℝ x).symm.toAffineMap)) ⁻¹' {0} := by
      ext q
      simp [vsub_eq_sub]
    rw [h]
    exact (convex_singleton (0 : ℝ)).affine_preimage _
  have hhull : ∀ q ∈ convexHull ℝ (s : Set E), f (q - x) = 0 :=
    fun q hq => convexHull_min (fun v hv => hs v (Finset.mem_coe.mp hv)) hconv hq
  rcases exists_combo_of_mem_convexHull_insert hc hz with rfl | ⟨q, hq, t, ht0, ht1, rfl⟩
  · exact ⟨1, zero_le_one, (one_mul _).symm⟩
  · refine ⟨1 - t, by linarith, ?_⟩
    have h1 : c + t • (q - c) - x = (1 - t) • (c - x) + t • (q - x) := by
      simp only [sub_smul, one_smul, smul_sub]
      abel
    rw [h1, map_add, map_smul, map_smul, hhull q hq, smul_eq_mul, smul_eq_mul, mul_zero,
      add_zero]

theorem exists_pos_forall_mem_ball_mem_convexHull_insert [FiniteDimensional ℝ E] [DecidableEq E]
    {s : Finset E} {c x : E} (hind : AffineIndependent ℝ ((↑) : ↥(insert c s : Finset E) → E))
    (hx : x ∈ openSimplex s) (hc : c ∉ s) (f : E →ₗ[ℝ] ℝ)
    (hker : ∀ ζ, f ζ = 0 → ζ ∈ vectorSpan ℝ (s : Set E)) (hfc : f (c - x) ≠ 0) :
    ∃ ρ > 0, ∀ z ∈ ball x ρ, 0 ≤ f (z - x) * f (c - x) →
      z ∈ convexHull ℝ ((insert c s : Finset E) : Set E) := by
  classical
  have hev : ∀ᶠ y in 𝓝 x, y ∈ convexHull ℝ ((insert c s : Finset E) : Set E) ↔
      ∃ z ∈ vectorSpan ℝ (s : Set E), ∃ t : ℝ, 0 ≤ t ∧ y - x = z + t • (c - x) := by
    convert eventually_mem_convexHull_insert_iff (by convert hind) hx hc using 6
    ext
    simp
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun z hz hsign => ?_⟩
  refine (hball (mem_ball.mp hz)).mpr ⟨(z - x) - (f (z - x) / f (c - x)) • (c - x), ?_,
    f (z - x) / f (c - x), ?_, by abel⟩
  · refine hker _ ?_
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfc, sub_self]
  · have hsq : 0 < f (c - x) * f (c - x) := mul_self_pos.mpr hfc
    have heq : f (z - x) / f (c - x) = f (z - x) * f (c - x) / (f (c - x) * f (c - x)) := by
      field_simp
    rw [heq]
    exact div_nonneg hsign hsq.le

end Sides

section Plane

open Classical in
theorem exists_insert_mem_faces_of_mem_closure_interior
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) [Finite K.faces]
    {σ : Finset (EuclideanSpace ℝ (Fin 2))} (hσ : σ ∈ K.faces) (h2 : σ.card = 2)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ openSimplex σ)
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hKS : K.space ∈ 𝓝[S] x)
    (hxS : x ∈ closure (interior S)) : ∃ c, c ∉ σ ∧ insert c σ ∈ K.faces := by
  by_contra hno
  push Not at hno
  have hcard3 : ∀ u ∈ K.faces, u.card ≤ 3 := by
    intro u hu
    have h := (K.indep hu).card_le_finrank_succ
    have h2' := Submodule.finrank_le
      (vectorSpan ℝ (Set.range ((↑) : u → EuclideanSpace ℝ (Fin 2))))
    rw [Fintype.card_coe] at h
    rw [finrank_euclideanSpace_fin] at h2'
    omega
  have hcof : ∀ u ∈ K.faces, σ ⊆ u → u = σ := by
    intro u hu hσu
    by_contra hne
    have hlt : σ.card < u.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hσu, fun h => hne h.symm⟩)
    have hu3 : u.card = 3 := by have := hcard3 u hu; omega
    obtain ⟨c, hcu, hcσ⟩ : ∃ c ∈ u, c ∉ σ := Finset.exists_of_ssubset
      (Finset.ssubset_iff_subset_ne.mpr ⟨hσu, fun h => hne h.symm⟩)
    have hins : insert c σ = u := by
      refine Finset.eq_of_subset_of_card_le (Finset.insert_subset hcu hσu) ?_
      rw [Finset.card_insert_of_notMem hcσ, h2, hu3]
    exact hno c hcσ (hins ▸ hu)
  have hloc := eventually_mem_space_iff_mem_coface K hσ hx
  obtain ⟨U, hU, hUK⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hKS
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp (Filter.inter_mem hU hloc)
  have hsub : S ∩ V ⊆ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) := by
    rintro z ⟨hzS, hzV⟩
    have hzK : z ∈ K.space := hUK ⟨(hVsub hzV).1, hzS⟩
    obtain ⟨u, hu, hσu, hzu⟩ := ((hVsub hzV).2).mp hzK
    rw [hcof u hu hσu] at hzu
    exact hzu
  obtain ⟨w, hwV, hwint⟩ := mem_closure_iff.mp hxS V hV hxV
  have hsub2 : V ∩ interior S ⊆ convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) :=
    fun z hz => hsub ⟨interior_subset hz.2, hz.1⟩
  have hne : (interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))).Nonempty :=
    ⟨w, interior_maximal hsub2 (hV.inter isOpen_interior) ⟨hwV, hwint⟩⟩
  have htop := interior_convexHull_nonempty_iff_affineSpan_eq_top.mp hne
  have hcard := ((K.indep hσ).affineSpan_eq_top_iff_card_eq_finrank_add_one).mp
    (by rwa [Subtype.range_coe])
  rw [Fintype.card_coe, h2, finrank_euclideanSpace_fin] at hcard
  omega

end Plane

end DifferentialGeometry.Topology.PiecewiseLinear
