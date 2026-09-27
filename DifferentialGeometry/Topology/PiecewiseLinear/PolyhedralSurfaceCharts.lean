/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLSphereLocallyPlanar
import DifferentialGeometry.Topology.PiecewiseLinear.PieceParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable def subtypePreimageHomeomorph {X : Type*} [TopologicalSpace X]
    (S W : Set X) : ((Subtype.val : S → X) ⁻¹' W) ≃ₜ ↥(W ∩ S) :=
  (IsEmbedding.subtypeVal.homeomorphImage ((Subtype.val : S → X) ⁻¹' W)).trans
    (Homeomorph.setCongr (by rw [Subtype.image_preimage_coe, inter_comm]))

private theorem local_chart_of_homeomorph {X Y H : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace H] {S : Set X} {T : Set Y} (e : S ≃ₜ T)
    {y : Y} (hy : y ∈ T)
    (hlocal : ∃ W : Set X, IsOpen W ∧ (e.symm ⟨y, hy⟩ : X) ∈ W ∧
      ∃ V : Set H, IsOpen V ∧ Nonempty (↥(W ∩ S) ≃ₜ V)) :
    ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ ∃ V : Set H,
      IsOpen V ∧ Nonempty (↥(W ∩ T) ≃ₜ V) := by
  obtain ⟨W, hW, hyW, V, hV, ⟨ψ⟩⟩ := hlocal
  let D := (Subtype.val : S → X) ⁻¹' W
  have hD : IsOpen D := hW.preimage continuous_subtype_val
  obtain ⟨O, hO, hOE⟩ := isOpen_induced_iff.mp (e.isOpenMap D hD)
  have hpoint : (⟨y, hy⟩ : T) ∈ e '' D :=
    ⟨e.symm ⟨y, hy⟩, hyW, e.apply_symm_apply _⟩
  refine ⟨O, hO, ?_, V, hV, ?_⟩
  · rw [← hOE] at hpoint
    exact hpoint
  · let a : ((Subtype.val : T → Y) ⁻¹' O) ≃ₜ e '' D := Homeomorph.setCongr hOE
    exact ⟨(subtypePreimageHomeomorph T O).symm.trans
      (a.trans ((e.image D).symm.trans ((subtypePreimageHomeomorph S W).trans ψ)))⟩

private theorem local_chart_inter_open {X H : Type*} [TopologicalSpace X]
    [TopologicalSpace H] {S O : Set X} {x : X} (hO : IsOpen O) (hxO : x ∈ O)
    (hlocal : ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ V : Set H,
      IsOpen V ∧ Nonempty (↥(W ∩ S) ≃ₜ V)) :
    ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∃ V : Set H,
      IsOpen V ∧ Nonempty (↥(W ∩ (S ∩ O)) ≃ₜ V) := by
  obtain ⟨W, hW, hxW, V, hV, ⟨ψ⟩⟩ := hlocal
  let D := (Subtype.val : ↥(W ∩ S) → X) ⁻¹' O
  let V' := (Subtype.val : V → H) '' (ψ '' D)
  have hV' : IsOpen V' := hV.isOpenEmbedding_subtypeVal.isOpenMap _
    (ψ.isOpenMap D (hO.preimage continuous_subtype_val))
  have hdom : O ∩ (W ∩ S) = (W ∩ O) ∩ (S ∩ O) := by
    ext z
    simp only [mem_inter_iff]
    tauto
  let a : D ≃ₜ ↥((W ∩ O) ∩ (S ∩ O)) :=
    (subtypePreimageHomeomorph (W ∩ S) O).trans (Homeomorph.setCongr hdom)
  let b : (ψ '' D) ≃ₜ V' := IsEmbedding.subtypeVal.homeomorphImage (ψ '' D)
  exact ⟨W ∩ O, hW.inter hO, ⟨hxW, hxO⟩, V', hV',
    ⟨a.symm.trans ((ψ.image D).trans b)⟩⟩

theorem IsPolyhedralSphere.exists_isOpen_inter_homeomorph_of_two {M : Type*}
    [TopologicalSpace M] [T2Space M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {P : Set M}
    (hP : IsPolyhedralSphere (n := n) 2 P) {y : M} (hy : y ∈ P) :
    ∃ W : Set M, IsOpen W ∧ y ∈ W ∧ ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ Nonempty (↥(W ∩ P) ≃ₜ V) := by
  obtain ⟨T, hT⟩ := hP
  exact local_chart_of_homeomorph T.piece.homeomorph hy
    (hT.exists_isOpen_inter_homeomorph_of_two (T.piece.homeomorph.symm ⟨y, hy⟩).property)

theorem IsPolyhedralSphere.exists_isOpen_inter_chart_image_homeomorph_of_two {M : Type*}
    [TopologicalSpace M] [T2Space M] {n : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {P : Set M}
    (hP : IsPolyhedralSphere (n := n) 2 P)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {y : M}
    (hy : y ∈ P ∩ c.source) :
    ∃ W : Set (EuclideanSpace ℝ (Fin n)), IsOpen W ∧ c y ∈ W ∧
      ∃ V : Set (EuclideanSpace ℝ (Fin 2)), IsOpen V ∧
        Nonempty (↥(W ∩ c '' (P ∩ c.source)) ≃ₜ V) := by
  let e := c.homeomorphOfImageSubsetSource (s := P ∩ c.source) inter_subset_right rfl
  have hcy : c y ∈ c '' (P ∩ c.source) := mem_image_of_mem c hy
  have hback : (e.symm ⟨c y, hcy⟩ : M) = y := c.left_inv hy.2
  apply local_chart_of_homeomorph e hcy
  rw [hback]
  exact local_chart_inter_open c.open_source hy.2
    (hP.exists_isOpen_inter_homeomorph_of_two hy.1)

theorem IsPLCellOn.exists_isOpen_inter_boundary_homeomorph {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B : Set M} (h : IsPLCellOn 3 S B) {y : M} (hy : y ∈ B) :
    ∃ W : Set M, IsOpen W ∧ y ∈ W ∧ ∃ V : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen V ∧ Nonempty (↥(W ∩ B) ≃ₜ V) := by
  obtain ⟨P, r, u, hr, hu, -, hB⟩ := h
  have hb : IsPLBall 3 P := ⟨r, hr⟩
  have hSP : frontier P ⊆ P := hb.isPolyhedron.isClosed.frontier_subset
  rw [IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr] at hB
  let : CompactSpace (frontier P) :=
    isCompact_iff_compactSpace.mp hb.isPLSphere_frontier.isPolyhedron.isCompact
  have hemb : IsClosedEmbedding (fun x : frontier P => u x) :=
    (hu.continuousOn.mono hSP).domRestrict.isClosedEmbedding
      (fun x z hxz => Subtype.ext (hu.injOn (hSP x.property) (hSP z.property) hxz))
  have hrange : range (fun x : frontier P => u x) = B := by
    rw [hB]
    change range (u ∘ (Subtype.val : frontier P → EuclideanSpace ℝ (Fin 3))) = _
    rw [range_comp, Subtype.range_coe]
  let e := hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  exact local_chart_of_homeomorph e hy
    (hb.isPLSphere_frontier.exists_isOpen_inter_homeomorph_of_two (e.symm ⟨y, hy⟩).property)

theorem IsPLCellOn.exists_isOpen_inter_boundary_chart_image_homeomorph {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B : Set M} (h : IsPLCellOn 3 S B)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) {y : M}
    (hy : y ∈ B ∩ c.source) :
    ∃ W : Set (EuclideanSpace ℝ (Fin 3)), IsOpen W ∧ c y ∈ W ∧
      ∃ V : Set (EuclideanSpace ℝ (Fin 2)), IsOpen V ∧
        Nonempty (↥(W ∩ c '' (B ∩ c.source)) ≃ₜ V) := by
  let e := c.homeomorphOfImageSubsetSource (s := B ∩ c.source) inter_subset_right rfl
  have hcy : c y ∈ c '' (B ∩ c.source) := mem_image_of_mem c hy
  have hback : (e.symm ⟨c y, hcy⟩ : M) = y := c.left_inv hy.2
  apply local_chart_of_homeomorph e hcy
  rw [hback]
  exact local_chart_inter_open c.open_source hy.2
    (h.exists_isOpen_inter_boundary_homeomorph hy.1)

end DifferentialGeometry.Topology.PiecewiseLinear
