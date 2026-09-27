/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Homogeneity
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies
import Mathlib.Analysis.LocallyConvex.Separation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_linearMap_lt_on_convexHull_sdiff_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 2 ≤ T.card)
    {a : E} (ha : a ∈ T) :
    ∃ ℓ : E →ₗ[ℝ] ℝ, ℓ ≠ 0 ∧ ∀ x ∈ convexHull ℝ (T : Set E) \ {a}, ℓ a < ℓ x := by
  classical
  let F := T.erase a
  have haF : a ∉ convexHull ℝ (F : Set E) := by
    intro h
    exact Finset.notMem_erase a T (mem_of_mem_convexHull_of_affineIndependent hT
      (Finset.erase_subset a T) ha h)
  obtain ⟨ℓ, u, hau, hu⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ (F : Set E))
    (F.finite_toSet.isCompact_convexHull ℝ).isClosed haF
  have hFne : F.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [F]
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb⟩ := hFne
  have hℓ : ℓ.toLinearMap ≠ 0 := by
    intro h
    have hlt := hau.trans (hu b (subset_convexHull ℝ _ hb))
    change ℓ.toLinearMap a < ℓ.toLinearMap b at hlt
    simp only [h, LinearMap.zero_apply, lt_self_iff_false] at hlt
  refine ⟨ℓ.toLinearMap, hℓ, ?_⟩
  rintro x ⟨hx, hxa⟩
  rw [← Finset.insert_erase ha] at hx
  rcases exists_combo_of_mem_convexHull_insert (Finset.notMem_erase a T) hx with h | ⟨z, hz, s, hs,
      -, rfl⟩
  · exact (hxa h).elim
  · change ℓ a < ℓ (a + s • (z - a))
    rw [map_add, map_smul, map_sub, smul_eq_mul]
    have hpos := mul_pos hs (sub_pos.mpr (hau.trans (hu z hz)))
    linarith

theorem exists_isPLHomeomorphOn_convex_image_strict_separation
    {D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsPLBall 2 D)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∉ interior D)
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
      (C : Set (EuclideanSpace ℝ (Fin 2))) (ℓ : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ),
      IsPLHomeomorphOn h univ univ ∧ EqOn h id Uᶜ ∧ h '' D = C ∧ Convex ℝ C ∧
        ℓ ≠ 0 ∧ ∀ x ∈ C \ {h p}, ℓ (h p) < ℓ x := by
  classical
  obtain ⟨g, C, hC, hg, hgD, hgfront, hgfix⟩ :=
    exists_isPLHomeomorphOn_straighten_of_isPLBall_two hD hU hDU
  have hCU : C ⊆ U := by
    rintro y hy
    obtain ⟨x, hx, rfl⟩ := hgD.symm ▸ hy
    by_contra hxU
    have hgg : g (g x) = g x := hgfix hxU
    have heq : g x = x := g.injective hgg
    exact hxU (heq.symm ▸ hDU hx)
  by_cases hpD : p ∈ D
  · have hpfront : p ∈ frontier D := by
      rw [hD.isPolyhedron.isCompact.isClosed.frontier_eq]
      exact ⟨hpD, hp⟩
    have hgp : g p ∈ frontier C := hgfront ▸ mem_image_of_mem g hpfront
    obtain ⟨v, hv, rfl⟩ := hC
    let T : Finset (EuclideanSpace ℝ (Fin 2)) := Finset.univ.image v
    have hTrange : (T : Set (EuclideanSpace ℝ (Fin 2))) = Set.range v := by simp [T]
    have hT : AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 2)) :=
      AffineIndependent.mono (t := Set.range v) hv.range (by rw [hTrange])
    have hcard : T.card = 3 := by
      rw [Finset.card_image_of_injective _ hv.injective]
      simp
    have hspan : affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin 2))) = ⊤ := by
      have h := hT.affineSpan_eq_top_iff_card_eq_finrank_add_one
      rw [Subtype.range_coe] at h
      exact h.mpr (by simpa using hcard)
    have hboundary : (simplexBoundary T hT).space = frontier (convexHull ℝ (T : Set _)) := by
      rw [simplexBoundary_space T hT (by omega), frontier_convexHull_eq_biUnion_erase T hT hspan]
    obtain ⟨k, hk, hkC, hkp, hkfix⟩ := exists_isPLHomeomorphOn_simplex_boundary_mem_vertices T hT
      (by omega) hspan (by rwa [hboundary, hTrange]) hU (by rwa [hTrange])
    obtain ⟨ℓ, hℓ, hsep⟩ := exists_linearMap_lt_on_convexHull_sdiff_singleton T hT (by omega) hkp
    have himage : (g.trans k) '' D = convexHull ℝ (T : Set _) := by
      change (k ∘ g) '' D = _
      rw [image_comp, hgD, ← hTrange, hkC]
    refine ⟨g.trans k, convexHull ℝ (T : Set _), ℓ, hg.trans hk, ?_, himage,
      convex_convexHull ℝ _, hℓ, hsep⟩
    intro x hx
    change k (g x) = x
    rw [hgfix hx, id_eq, hkfix hx, id_eq]
  · have hgp : g p ∉ C := by
      rw [← hgD]
      exact fun ⟨x, hx, hxp⟩ => hpD (g.injective hxp ▸ hx)
    obtain ⟨ℓ, u, hpu, hu⟩ := geometric_hahn_banach_point_closed hC.convex hC.isCompact.isClosed hgp
    have hCne : C.Nonempty := by
      obtain ⟨v, -, rfl⟩ := hC
      exact ⟨v 0, subset_convexHull ℝ _ (mem_range_self 0)⟩
    have hℓ : ℓ.toLinearMap ≠ 0 := by
      intro h
      obtain ⟨y, hy⟩ := hCne
      have hlt := hpu.trans (hu y hy)
      change ℓ.toLinearMap (g p) < ℓ.toLinearMap y at hlt
      simp only [h, LinearMap.zero_apply, lt_self_iff_false] at hlt
    exact ⟨g, C, ℓ.toLinearMap, hg, hgfix, hgD, hC.convex, hℓ,
      fun x hx => hpu.trans (hu x hx.1)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
