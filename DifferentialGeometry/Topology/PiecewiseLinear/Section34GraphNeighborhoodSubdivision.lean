/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierSupportLocallyFinite
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SubdivisionCarriers

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M}

theorem locallyFinite_simplexBody_subtype (𝒦 : LocallyFinitePLPieceIn Ea 3 M U) :
    LocallyFinite fun s : 𝒦.complex.faces =>
      (Subtype.val : U → M) ⁻¹' simplexBody 𝒦 s.1 := by
  intro x
  obtain ⟨V, hV, hfin⟩ := (locallyFinite_section34CarrierSupport 𝒦).2 x.1 x.2
  refine ⟨Subtype.val ⁻¹' V, continuous_subtype_val.continuousAt.preimage_mem_nhds hV, ?_⟩
  refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
  rintro s ⟨y, hy, hyV⟩
  obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces s.2
  exact ⟨s.2, y.1, mem_iUnion₂.mpr ⟨v, hv, mem_iUnion₂.mpr ⟨s.1, ⟨s.2, hv⟩, hy⟩⟩,
    hyV⟩

theorem isClosed_graphSkeletonSpace_subtype [T2Space M]
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M U) :
    IsClosed ((Subtype.val : U → M) ⁻¹' graphSkeletonSpace 𝒦) := by
  let I := {s : 𝒦.complex.faces // s.1.card ≤ 2}
  have hclosed : ∀ s : I,
      IsClosed ((Subtype.val : U → M) ⁻¹' simplexBody 𝒦 s.1.1) := by
    intro s
    exact ((s.1.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image_of_continuousOn
      (𝒦.continuousOn.mono (𝒦.complex.convexHull_subset_space s.1.2))).isClosed.preimage
        continuous_subtype_val
  have heq : (Subtype.val : U → M) ⁻¹' graphSkeletonSpace 𝒦 =
      ⋃ s : I, (Subtype.val : U → M) ⁻¹' simplexBody 𝒦 s.1.1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨⟨⟨s, hs.1⟩, hs.2⟩, hx⟩
    · intro hx
      obtain ⟨s, hx⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨s.1.1, ⟨s.1.2, s.2⟩, hx⟩
  rw [heq]
  exact ((locallyFinite_simplexBody_subtype 𝒦).comp_injective
    (g := fun s : I => s.1) Subtype.val_injective).isClosed_iUnion hclosed

theorem isOpen_sdiff_graphSkeletonSpace [T2Space M]
    (hU : IsOpen U) (𝒦 : LocallyFinitePLPieceIn Ea 3 M U) :
    IsOpen (U \ graphSkeletonSpace 𝒦) := by
  exact hU.inter_preimage_val_iff.mp (isClosed_graphSkeletonSpace_subtype 𝒦).isOpen_compl

theorem exists_graph_subdivision_with_finite_carrier_assignment
    [FiniteDimensional ℝ Ea] [T2Space M] {ι : Type*} {W : Set M}
    (hU : IsOpen U) (𝒦 : LocallyFinitePLPieceIn Ea 3 M U)
    (h𝒦 : IsCombinatorialManifold 3 𝒦.complex) (hW : IsOpen W)
    (hΓW : graphSkeletonSpace 𝒦 ⊆ W)
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
      ∀ w : Section34VertexIndex 𝒦 𝒦', Section34CarrierSupport 𝒦' w.1 ⊆ W := by
  classical
  let V : Bool → Set M := fun b => if b then W else U \ graphSkeletonSpace 𝒦
  have hV : ∀ b, IsOpen (V b) := by
    intro b
    cases b
    · exact isOpen_sdiff_graphSkeletonSpace hU 𝒦
    · exact hW
  have hcov : U ⊆ ⋃ p : Bool × ι, V p.1 ∩ O p.2 := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    by_cases hxΓ : x ∈ graphSkeletonSpace 𝒦
    · exact mem_iUnion.mpr ⟨(true, i), hΓW hxΓ, hi⟩
    · exact mem_iUnion.mpr ⟨(false, i), ⟨hx, hxΓ⟩, hi⟩
  obtain ⟨𝒦', car, hsub, hmap, hman, hsmall, hcar, hbody, hsupport, hfinite⟩ :=
    exists_subdivision_with_finite_carrier_assignment hU 𝒦 h𝒦
      (fun p : Bool × ι => V p.1 ∩ O p.2) (fun p => (hV p.1).inter (hO p.2)) hcov
  refine ⟨𝒦', car, hsub, hmap, hman, ?_, hcar, hbody, hsupport, hfinite, ?_⟩
  · intro s hs
    obtain ⟨p, hp⟩ := hsmall s hs
    exact ⟨p.2, hp.trans inter_subset_right⟩
  · intro w
    obtain ⟨⟨b, i⟩, hi⟩ := hsmall w.1 w.2.1
    cases b
    · obtain ⟨v, hv⟩ := 𝒦'.complex.nonempty_of_mem_faces w.2.1
      have hbody : 𝒦'.map v ∈ simplexBody 𝒦' w.1 :=
        mem_image_of_mem _ (subset_convexHull ℝ _ hv)
      have hsup : 𝒦'.map v ∈ Section34CarrierSupport 𝒦' w.1 :=
        mem_iUnion₂.mpr ⟨v, hv, mem_iUnion₂.mpr ⟨w.1, ⟨w.2.1, hv⟩, hbody⟩⟩
      exact False.elim ((hi hsup).1.2 (w.2.2.2 hbody))
    · exact hi.trans inter_subset_left

end DifferentialGeometry.Topology.PiecewiseLinear
