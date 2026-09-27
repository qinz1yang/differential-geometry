/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CircleMarkedArcs
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSeams

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCombinatorialSolidTorus.exists_annulus_between_essential_circles_of_ne_colors
    {S : Set E3} (hS : IsCombinatorialSolidTorus S) {ι κ : Type*} [Finite ι]
    (G : ι → Set E3) (hG : ∀ i, IsPLSphere 1 (G i))
    (hGS : ∀ i, G i ⊆ frontier S) (hdisj : Pairwise fun i j => Disjoint (G i) (G j))
    (hess : ∀ i, ¬ boundsDiskIn (G i) (frontier S)) (c : ι → κ)
    {i₀ j₀ : ι} (hc : c i₀ ≠ c j₀) :
    ∃ (i j : ι) (B : Set E3), c i ≠ c j ∧ IsPLAnnulusWithEnds B (G i) (G j) ∧
      B ⊆ frontier S ∧ Disjoint (B \ (G i ∪ G j)) (⋃ k, G k) ∧
      IsClosed (frontier S \ (B \ (G i ∪ G j))) ∧ closure (B \ (G i ∪ G j)) = B ∧
      ∀ x ∈ B \ (G i ∪ G j),
        connectedComponentIn (frontier S \ ⋃ k, G k) x = B \ (G i ∪ G j) := by
  classical
  let _ := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hn : 1 < Fintype.card ι :=
    Fintype.one_lt_card_iff.mpr ⟨i₀, j₀, fun h => hc (congrArg c h)⟩
  obtain ⟨J, Q, f, q₀, hJ, hQ, hf, hq₀, hq₀inj, hlabel₀⟩ :=
    exists_product_coordinates_for_disjoint_essential_polygons hS (G ∘ e) hn
      (fun i => hG (e i)) (fun i => hGS (e i))
      (fun i j hij => hdisj (e.injective.ne hij)) (fun i => hess (e i))
  let q : ι → E3 := q₀ ∘ e.symm
  have hq : ∀ i, q i ∈ Q := fun i => hq₀ (e.symm i)
  have hqinj : Function.Injective q := hq₀inj.comp e.symm.injective
  have hlabel : ∀ i, G i = f '' (J ×ˢ {q i}) := fun i => by
    simpa only [q, Function.comp_apply, Equiv.apply_symm_apply] using hlabel₀ (e.symm i)
  obtain ⟨i, j, β, hcolors, hβ, hβ₀, hβ₁, hβQ, hmarks, hclosed⟩ :=
    hQ.exists_arc_between_marks_of_ne_colors q hq hqinj c hc
  let B := f '' (J ×ˢ (β '' Icc 0 1))
  let U := f '' (J ×ˢ (β '' Ioo 0 1))
  have hβpoly : IsPolyhedron (β '' Icc 0 1) :=
    ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hβ).isPolyhedron
  have hρ : IsPLHomeomorphOn (f ∘ Prod.map id β) (J ×ˢ Icc 0 1) B :=
    (hJ.isPolyhedron.isPLHomeomorphOn_id.prodMap hβ).trans
      (hf.restrict (hJ.isPolyhedron.prod hβpoly) (prod_mono Subset.rfl hβQ))
  have hBann : IsPLAnnulusWithEnds B (G i) (G j) := by
    refine ⟨J, f ∘ Prod.map id β, hJ, hρ, ?_, ?_⟩
    · rw [image_comp, prodMap_image_prod, image_id, image_singleton, hβ₀, hlabel i]
    · rw [image_comp, prodMap_image_prod, image_id, image_singleton, hβ₁, hlabel j]
  have hBsub : B ⊆ frontier S :=
    (image_mono (prod_mono Subset.rfl hβQ)).trans hf.image_eq.subset
  have hUsub : U ⊆ B := image_mono (prod_mono Subset.rfl (image_mono Ioo_subset_Icc_self))
  have hinterior : B \ (G i ∪ G j) = U := by
    have hends : J ×ˢ {q i} ∪ J ×ˢ {q j} ⊆ J ×ˢ (β '' Icc 0 1) := by
      refine union_subset (prod_mono Subset.rfl ?_) (prod_mono Subset.rfl ?_)
      · exact singleton_subset_iff.mpr ⟨0, ⟨le_rfl, zero_le_one⟩, hβ₀⟩
      · exact singleton_subset_iff.mpr ⟨1, ⟨zero_le_one, le_rfl⟩, hβ₁⟩
    have hprod : J ×ˢ (β '' Ioo 0 1) =
        (J ×ˢ (β '' Icc 0 1)) \ (J ×ˢ {q i} ∪ J ×ˢ {q j}) := by
      rw [hβ.image_Ioo_eq_sdiff_endpoints (by norm_num : (0 : ℝ) < 1), hβ₀, hβ₁]
      ext p
      simp only [mem_prod, mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff]
      tauto
    change f '' (J ×ˢ (β '' Icc 0 1)) \ (G i ∪ G j) = _
    rw [hlabel i, hlabel j, ← image_union,
      ← (hf.bijOn.injOn.mono (prod_mono Subset.rfl hβQ)).image_sdiff_subset hends]
    exact congrArg (fun V => f '' V) hprod.symm
  have hUdis : Disjoint U (⋃ k, G k) := by
    apply disjoint_left.mpr
    rintro x ⟨p, hp, hpx⟩ hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    rw [hlabel k] at hk
    obtain ⟨z, hz, hzx⟩ := hk
    have hpQ : p ∈ J ×ˢ Q := ⟨hp.1, hβQ ((image_mono Ioo_subset_Icc_self) hp.2)⟩
    have hzQ : z ∈ J ×ˢ Q := ⟨hz.1, (mem_singleton_iff.mp hz.2) ▸ hq k⟩
    have hzp := hf.bijOn.injOn hzQ hpQ (hzx.trans hpx.symm)
    exact hmarks k (by simpa only [← hzp, mem_singleton_iff.mp hz.2] using hp.2)
  have hUclosed : IsClosed (frontier S \ U) := by
    have hopenQ : β '' Ioo 0 1 ⊆ Q := (image_mono Ioo_subset_Icc_self).trans hβQ
    have heq : frontier S \ U = f '' (J ×ˢ (Q \ β '' Ioo 0 1)) := by
      rw [← hf.image_eq]
      change f '' (J ×ˢ Q) \ f '' (J ×ˢ (β '' Ioo 0 1)) = _
      rw [← hf.bijOn.injOn.image_sdiff_subset (prod_mono Subset.rfl hopenQ)]
      congr 1
      ext p
      simp only [mem_sdiff, mem_prod]
      tauto
    rw [heq]
    exact ((hJ.isPolyhedron.isCompact.prod
      (hQ.isPolyhedron.isCompact.of_isClosed_subset hclosed sdiff_subset)).image_of_continuousOn
      (hf.isPiecewiseAffineOn.continuousOn.mono (prod_mono Subset.rfl sdiff_subset))).isClosed
  have hρopen : (f ∘ Prod.map id β) '' (J ×ˢ Ioo 0 1) = U := by
    rw [image_comp, prodMap_image_prod, image_id]
  have hUconn : IsConnected U := by
    rw [← hρopen]
    exact (hJ.isConnected.prod (isConnected_Ioo (by norm_num : (0 : ℝ) < 1))).image _
      (hρ.isPiecewiseAffineOn.continuousOn.mono (prod_mono Subset.rfl Ioo_subset_Icc_self))
  have hclosure : closure U = B := by
    rw [← hρopen, ← hρ.image_closure (hJ.isPolyhedron.isCompact.prod isCompact_Icc)
      (prod_mono Subset.rfl Ioo_subset_Icc_self), closure_prod_eq,
      hJ.isPolyhedron.isClosed.closure_eq, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), hρ.image_eq]
  refine ⟨i, j, B, hcolors, hBann, hBsub, hinterior.symm ▸ hUdis,
    hinterior.symm ▸ hUclosed, ?_, ?_⟩
  · rwa [hinterior]
  · rw [hinterior]
    intro x hx
    have hUcut : U ⊆ frontier S \ ⋃ k, G k := fun y hy =>
      ⟨hBsub (hUsub hy), disjoint_left.mp hUdis hy⟩
    have hCcut := connectedComponentIn_subset (frontier S \ ⋃ k, G k) x
    have hendsUnion : G i ∪ G j ⊆ ⋃ k, G k :=
      union_subset (subset_iUnion G i) (subset_iUnion G j)
    apply Subset.antisymm ?_ (hUconn.isPreconnected.subset_connectedComponentIn hx hUcut)
    have hcover : connectedComponentIn (frontier S \ ⋃ k, G k) x ⊆
        B ∪ (frontier S \ U) := by
      intro y hy
      by_cases hyU : y ∈ U
      · exact Or.inl (hUsub hyU)
      · exact Or.inr ⟨(hCcut hy).1, hyU⟩
    have hmeet : connectedComponentIn (frontier S \ ⋃ k, G k) x ∩
        (B ∩ (frontier S \ U)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro y ⟨hyC, hyB, -, hynU⟩
      apply hynU
      rw [← hinterior]
      exact ⟨hyB, fun hyends => (hCcut hyC).2 (hendsUnion hyends)⟩
    have hBclosed : IsClosed B := hclosure ▸ isClosed_closure
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_connectedComponentIn
      B (frontier S \ U) hBclosed hUclosed hcover hmeet with hCB | hCR
    · intro y hy
      rw [← hinterior]
      exact ⟨hCB hy, fun hyends => (hCcut hy).2 (hendsUnion hyends)⟩
    · exact (hCR (mem_connectedComponentIn (hUcut hx))).2 hx |>.elim

end DifferentialGeometry.Topology.PiecewiseLinear
