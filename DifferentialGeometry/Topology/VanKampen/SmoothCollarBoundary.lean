/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Manifold.EuclideanBoundaryCoordinates
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas
import DifferentialGeometry.Topology.VanKampen.SmoothSideDefiningFunction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Function Manifold Set Topology
open scoped Manifold ContDiff
noncomputable section

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev I2 := modelWithCornersSelf ℝ E2
private abbrev I3 := modelWithCornersSelf ℝ E3

variable {S M : Type} [TopologicalSpace S] [ChartedSpace E2 S]
    [IsManifold I2 ∞ S] [TopologicalSpace M] [ChartedSpace E3 M]
    {e : S → M} (h : SmoothTwoSidedCollar I2 I3 e)

def boundaryChart (x : h.neighborhood) (positive : Bool) :
    _root_.PartialDiffeomorph I3 I3 M E3 ∞ :=
  (((PartialDiffeomorph.subtypeVal (I := I3) h.neighborhood ⟨x⟩).symm.trans
    h.toDiffeomorph.symm.toPartialDiffeomorph).trans
      (PartialDiffeomorph.prod
        (PartialDiffeomorph.extendedChart (I := I2) (h.toDiffeomorph.symm x).1)
        (PartialDiffeomorph.subtypeVal (I := modelWithCornersSelf ℝ ℝ)
          (symmetricOpenInterval h.radius)
          ⟨⟨0, neg_lt_zero.mpr h.radius_pos, h.radius_pos⟩⟩))).trans
    (signedNormalFirstDiffeomorph 2 positive).toPartialDiffeomorph

omit [IsManifold I2 ∞ S] in
private theorem neighborhood_inverse (x : h.neighborhood) {y : M} (hy : y ∈ h.neighborhood) :
    (PartialDiffeomorph.subtypeVal (I := I3) h.neighborhood ⟨x⟩).symm y = ⟨y, hy⟩ := by
  apply Subtype.ext
  exact (h.neighborhood.openPartialHomeomorphSubtypeCoe ⟨x⟩).right_inv
    (by simpa using hy)

theorem boundaryChart_mem_source (x : h.neighborhood) (positive : Bool) :
    x.val ∈ (h.boundaryChart x positive).source := by
  refine ⟨⟨⟨?_, mem_univ _⟩, ?_, mem_univ _⟩, mem_univ _⟩
  · change x.val ∈ (h.neighborhood.openPartialHomeomorphSubtypeCoe ⟨x⟩).target
    simp
  · change (h.toDiffeomorph.symm
      ((PartialDiffeomorph.subtypeVal (I := I3) h.neighborhood ⟨x⟩).symm x.val)).1 ∈
      (extChartAt I2 (h.toDiffeomorph.symm x).1).source
    rw [h.neighborhood_inverse x x.property]
    exact mem_extChartAt_source _

theorem boundaryChart_source_subset (x : h.neighborhood) (positive : Bool) :
    (h.boundaryChart x positive).source ⊆ h.neighborhood := by
  intro y hy
  have htarget := hy.1.1.1
  change y ∈ (h.neighborhood.openPartialHomeomorphSubtypeCoe ⟨x⟩).target at htarget
  simpa using htarget

theorem boundaryChart_zero (x : h.neighborhood) (positive : Bool) {y : M}
    (hy : y ∈ (h.boundaryChart x positive).source) :
    h.boundaryChart x positive y 0 =
      if positive then h.finiteTime ⟨y, h.boundaryChart_source_subset x positive hy⟩
      else -h.finiteTime ⟨y, h.boundaryChart_source_subset x positive hy⟩ := by
  change signedNormalFirstEquiv 2 positive
    ((extChartAt I2 (h.toDiffeomorph.symm x).1)
      (h.toDiffeomorph.symm
        ((PartialDiffeomorph.subtypeVal (I := I3) h.neighborhood ⟨x⟩).symm y)).1,
      ((h.toDiffeomorph.symm
        ((PartialDiffeomorph.subtypeVal (I := I3) h.neighborhood ⟨x⟩).symm y)).2 : ℝ)) 0 = _
  rw [signedNormalFirstEquiv_zero, h.neighborhood_inverse x
    (h.boundaryChart_source_subset x positive hy)]
  rfl

variable [CompactSpace S] [Nonempty S] [ConnectedSpace S] [T2Space M]
    [ConnectedSpace M] [LocallyPathConnectedSpace M] [SimplyConnectedSpace M]

omit [IsManifold I2 ∞ S] in
theorem finiteTime_eq_zero_iff_mem_sphere (x : h.neighborhood) :
    h.finiteTime x = 0 ↔ x.val ∈ range e := by
  rw [← h.collarSignedValue_eq_zero_iff,
    ← h.sideDefiningFunction_of_mem_neighborhood x.property]
  exact h.sideDefiningFunction_eq_zero_iff x.val

variable [IsManifold I3 ∞ M]

theorem exists_boundaryAtlas_of_collar_side
    (positive : Bool) {K V : Set M} (hV : IsOpen V) (hK : K = V ∪ range e)
    (hdisj : Disjoint V (range e))
    (hmem : ∀ y : h.neighborhood, y.val ∈ K ↔
      0 ≤ if positive then h.finiteTime y else -h.finiteTime y) :
    ∃ C : SmoothBoundaryAtlas I3 3 K,
      ∀ x : K, C.ambientChart x x.val 0 = 0 ↔ x.val ∈ range e := by
  classical
  have hc : ∀ x : K, ∃ φ : _root_.PartialDiffeomorph I3 I3 M E3 ∞,
      x.val ∈ φ.source ∧ (∀ y ∈ φ.source, y ∈ K ↔ 0 ≤ φ y 0) ∧
      (φ x.val 0 = 0 ↔ x.val ∈ range e) := by
    intro x
    by_cases hxN : x.val ∈ h.neighborhood
    · let xN : h.neighborhood := ⟨x.val, hxN⟩
      refine ⟨h.boundaryChart xN positive, h.boundaryChart_mem_source xN positive, ?_, ?_⟩
      · intro y hy
        rw [h.boundaryChart_zero xN positive hy]
        exact hmem ⟨y, h.boundaryChart_source_subset xN positive hy⟩
      · rw [h.boundaryChart_zero xN positive (h.boundaryChart_mem_source xN positive)]
        cases positive <;> simpa using h.finiteTime_eq_zero_iff_mem_sphere xN
    · have hxV : x.val ∈ V := by
        have : x.val ∈ V ∪ range e := by simpa only [hK] using x.property
        exact this.resolve_right (fun hs ↦ hxN (h.zeroSlice_subset_neighborhood hs))
      obtain ⟨φ, hxφ, hφV, hpos⟩ := exists_positiveChart_of_mem_open (n := 3) hV hxV
      refine ⟨φ, hxφ, ?_, ?_⟩
      · intro y hy
        exact iff_of_true (by rw [hK]; exact Or.inl (hφV hy)) (hpos y hy).le
      · exact iff_of_false (ne_of_gt (hpos x.val hxφ))
          (fun hs ↦ Set.disjoint_left.mp hdisj hxV hs)
  choose φ hm hi hz using hc
  exact ⟨{ ambientChart := φ, mem_source := hm, mem_iff := hi }, hz⟩

theorem exists_boundaryAtlas_closure_negativeSide :
    ∃ C : SmoothBoundaryAtlas I3 3 (closure h.toTwoSidedCollar.negativeSide),
      ∀ x : (closure h.toTwoSidedCollar.negativeSide : Set M),
        C.ambientChart x x.val 0 = 0 ↔ x.val ∈ range e := by
  apply h.exists_boundaryAtlas_of_collar_side false h.toTwoSidedCollar.isOpen_negativeSide
    h.toTwoSidedCollar.closure_negativeSide
    h.toTwoSidedCollar.zeroSlice_disjoint_negativeSide.symm
  intro y
  rw [h.toTwoSidedCollar.closure_negativeSide, mem_union,
    ← h.finiteTime_neg_iff_mem_negativeSide, ← h.finiteTime_eq_zero_iff_mem_sphere]
  simp [le_iff_lt_or_eq]

theorem exists_boundaryAtlas_closure_positiveSide :
    ∃ C : SmoothBoundaryAtlas I3 3 (closure h.toTwoSidedCollar.positiveSide),
      ∀ x : (closure h.toTwoSidedCollar.positiveSide : Set M),
        C.ambientChart x x.val 0 = 0 ↔ x.val ∈ range e := by
  apply h.exists_boundaryAtlas_of_collar_side true h.toTwoSidedCollar.isOpen_positiveSide
    h.toTwoSidedCollar.closure_positiveSide
    h.toTwoSidedCollar.zeroSlice_disjoint_positiveSide.symm
  intro y
  rw [h.toTwoSidedCollar.closure_positiveSide, mem_union,
    ← h.finiteTime_pos_iff_mem_positiveSide, ← h.finiteTime_eq_zero_iff_mem_sphere]
  simp [le_iff_lt_or_eq, eq_comm]

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
