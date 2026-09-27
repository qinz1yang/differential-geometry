/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteIncidentNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphNeighborhoodSubdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M}

theorem graphSkeletonSpace_inter_simplexBody_eq_simplexRim
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M U) (s : Section34SimplexIndex 𝒦 3) :
    graphSkeletonSpace 𝒦 ∩ simplexBody 𝒦 s.1 = simplexRim 𝒦 s.1 := by
  classical
  apply Subset.antisymm
  · rintro y ⟨hyΓ, a, ha, hay⟩
    obtain ⟨t, ht, b, hb, hby⟩ := mem_iUnion₂.mp hyΓ
    have hab : a = b := 𝒦.bijOn.injOn (𝒦.complex.convexHull_subset_space s.2.1 ha)
      (𝒦.complex.convexHull_subset_space ht.1 hb) (hay.trans hby.symm)
    have hsmall : (s.1 ∩ t).card < s.1.card :=
      lt_of_le_of_lt (Finset.card_le_card Finset.inter_subset_right)
        (by have := ht.2; have := s.2.2; omega)
    refine mem_iUnion₂.mpr ⟨s.1 ∩ t,
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩, a, ?_, hay⟩
    · exact fun h => (ne_of_lt hsmall) (congrArg Finset.card h)
    · simpa only [Finset.coe_inter] using
        𝒦.complex.inter_subset_convexHull s.2.1 ht.1 ⟨ha, hab ▸ hb⟩
  · intro y hy
    obtain ⟨t, ht, a, ha, rfl⟩ := mem_iUnion₂.mp hy
    have hne : t.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.coe_empty, convexHull_empty] at ha
      exact ha
    have hface := 𝒦.complex.down_closed s.2.1 ht.1 hne
    have hcard : t.card ≤ 2 := by have hlt := Finset.card_lt_card ht; omega
    exact ⟨mem_iUnion₂.mpr ⟨t, ⟨hface, hcard⟩, a, ha, rfl⟩,
      a, convexHull_mono (Finset.coe_subset.mpr ht.1) ha, rfl⟩

theorem exists_graph_subdivision_with_incident_buffer_control
    [FiniteDimensional ℝ Ea] [T2Space M] {ι : Type*} {W : Set M}
    (hU : IsOpen U) (𝒦 : LocallyFinitePLPieceIn Ea 3 M U)
    (h𝒦 : IsCombinatorialManifold 3 𝒦.complex) (hW : IsOpen W)
    (hΓW : graphSkeletonSpace 𝒦 ⊆ W)
    (B : Section34SimplexIndex 𝒦 3 → Set M) (hB : ∀ s, IsOpen (B s))
    (hrim : ∀ s, simplexRim 𝒦 s.1 ⊆ B s)
    (O : ι → Set M) (hO : ∀ i, IsOpen (O i)) (hcover : U ⊆ ⋃ i, O i) :
    ∃ (𝒦' : LocallyFinitePLPieceIn Ea 3 M U)
      (car : Section34VertexIndex 𝒦 𝒦' → Finset Ea),
      IsSubdivision 𝒦'.complex 𝒦.complex ∧ 𝒦'.map = 𝒦.map ∧
      IsCombinatorialManifold 3 𝒦'.complex ∧
      (∀ s ∈ 𝒦'.complex.faces, ∃ i, Section34CarrierSupport 𝒦' s ⊆ O i) ∧
      (∀ w, car w ∈ 𝒦.complex.faces) ∧
      (∀ w, simplexBody 𝒦' w.1 ⊆ simplexBody 𝒦 (car w)) ∧
      (∀ w, Section34CarrierSupport 𝒦' w.1 ⊆ Section34CarrierSupport 𝒦 (car w)) ∧
      (∀ t : Finset Ea, {w | car w = t}.Finite) ∧
      (∀ w : Section34VertexIndex 𝒦 𝒦', Section34CarrierSupport 𝒦' w.1 ⊆ W) ∧
      ∀ (w : Section34VertexIndex 𝒦 𝒦') (s : Section34SimplexIndex 𝒦 3),
        Section34Incident w.1 s.1 → Section34CarrierSupport 𝒦' w.1 ⊆ B s := by
  classical
  let F : Section34SimplexIndex 𝒦 3 → Set U := fun s =>
    (Subtype.val : U → M) ⁻¹' simplexBody 𝒦 s.1
  let C : Set U := (Subtype.val : U → M) ⁻¹' graphSkeletonSpace 𝒦
  have hF : LocallyFinite F := by
    let f : Section34SimplexIndex 𝒦 3 → 𝒦.complex.faces := fun s => ⟨s.1, s.2.1⟩
    apply (locallyFinite_simplexBody_subtype 𝒦).comp_injective (g := f)
    intro s t h
    exact Subtype.ext (congrArg (fun r : 𝒦.complex.faces => r.1) h)
  have hclosed : ∀ s, IsClosed (F s) := fun s =>
    ((s.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image_of_continuousOn
      (𝒦.continuousOn.mono (𝒦.complex.convexHull_subset_space s.2.1))).isClosed.preimage
        continuous_subtype_val
  obtain ⟨V, hV, hVcover, hVB⟩ := hF.exists_isOpen_cover_with_incident_buffers hclosed
    (isClosed_graphSkeletonSpace_subtype 𝒦)
    (fun s => (hB s).preimage continuous_subtype_val)
    (fun s x hx => hrim s ((graphSkeletonSpace_inter_simplexBody_eq_simplexRim 𝒦 s).subset hx))
  let A : Option C × ι → Set M := fun j => (Subtype.val '' V j.1) ∩ O j.2
  have hA : ∀ j, IsOpen (A j) := fun j =>
    (hU.isOpenMap_subtype_val _ (hV j.1)).inter (hO j.2)
  have hAcov : U ⊆ ⋃ j, A j := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hVcover.symm ▸ mem_univ (⟨x, hx⟩ : U))
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨(j, i), ⟨⟨x, hx⟩, hj, rfl⟩, hi⟩
  obtain ⟨𝒦', car, hsub, hmap, hman, hsmall, hcar, hbody, hsupp, hfin, hW'⟩ :=
    exists_graph_subdivision_with_finite_carrier_assignment hU 𝒦 h𝒦 hW hΓW A hA hAcov
  refine ⟨𝒦', car, hsub, hmap, hman, ?_, hcar, hbody, hsupp, hfin, hW', ?_⟩
  · intro s hs
    obtain ⟨j, hj⟩ := hsmall s hs
    exact ⟨j.2, hj.trans inter_subset_right⟩
  · intro w s hws
    obtain ⟨j, hj⟩ := hsmall w.1 w.2.1
    obtain ⟨p, hp⟩ := 𝒦'.complex.nonempty_of_mem_faces w.2.1
    have hpbody : 𝒦'.map p ∈ simplexBody 𝒦' w.1 :=
      mem_image_of_mem _ (subset_convexHull ℝ _ hp)
    have hpsupp : 𝒦'.map p ∈ Section34CarrierSupport 𝒦' w.1 :=
      mem_iUnion₂.mpr ⟨p, hp, mem_iUnion₂.mpr ⟨w.1, ⟨w.2.1, hp⟩, hpbody⟩⟩
    obtain ⟨q, hqV, hq⟩ := (hj hpsupp).1
    have hqC : q ∈ C := by
      change (q : M) ∈ graphSkeletonSpace 𝒦
      rw [hq]
      exact w.2.2.2 hpbody
    have hqF : q ∈ F s := by
      change (q : M) ∈ simplexBody 𝒦 s.1
      rw [hq, hmap]
      exact ⟨p, hws hp, rfl⟩
    have hbuffer := hVB j.1 s ⟨q, ⟨hqV, hqC⟩, hqF⟩
    intro x hx
    obtain ⟨q', hq'V, rfl⟩ := (hj hx).1
    exact hbuffer hq'V

end DifferentialGeometry.Topology.PiecewiseLinear
