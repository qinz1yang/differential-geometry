/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Embedding.SubtypeRestriction
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function Manifold Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

structure SmoothBoundaryAtlas
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (n : ℕ) [NeZero n] (K : Set M) where
  ambientChart : K → PartialDiffeomorph I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
    M (EuclideanSpace ℝ (Fin n)) ∞
  mem_source : ∀ x : K, x.val ∈ (ambientChart x).source
  mem_iff : ∀ x : K, ∀ y ∈ (ambientChart x).source, y ∈ K ↔ 0 ≤ ambientChart x y 0

namespace SmoothBoundaryAtlas

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : ℕ} [NeZero n] {K : Set M} (C : SmoothBoundaryAtlas I n K)

def chart (x : K) : _root_.OpenPartialHomeomorph K (EuclideanHalfSpace n) :=
  OpenPartialHomeomorph.restrictSubtypes (C.ambientChart x).toOpenPartialHomeomorph
    K {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} x (0 : EuclideanHalfSpace n) (C.mem_iff x)

@[reducible]
def toChartedSpace : ChartedSpace (EuclideanHalfSpace n) K where
  atlas := range C.chart
  chartAt := C.chart
  mem_chart_source := C.mem_source
  chart_mem_atlas := fun x ↦ mem_range_self x

private theorem change_mem_source (x y : K) (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ (modelWithCornersEuclideanHalfSpace n).symm ⁻¹'
        ((C.chart x).symm.trans (C.chart y)).source ∩
        range (modelWithCornersEuclideanHalfSpace n)) :
    z ∈ ((C.ambientChart x).symm.trans (C.ambientChart y)).source := by
  let ih := modelWithCornersEuclideanHalfSpace n
  have hval : (ih.symm z).val = z := ih.right_inv hz.2
  have htarget : z ∈ (C.ambientChart x).target := by
    have h := hz.1.1
    change (ih.symm z).val ∈ (C.ambientChart x).target at h
    rwa [hval] at h
  have hinv : ((C.chart x).symm (ih.symm z) : M) = (C.ambientChart x).symm z := by
    rw [chart, OpenPartialHomeomorph.restrictSubtypes_symm_apply]
    · rw [hval]; rfl
    · change (ih.symm z).val ∈ (C.ambientChart x).target
      rwa [hval]
  refine ⟨htarget, ?_⟩
  have h := hz.1.2
  change ((C.chart x).symm (ih.symm z) : M) ∈ (C.ambientChart y).source at h
  rwa [hinv] at h

private theorem change_eq (x y : K) (z : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ (modelWithCornersEuclideanHalfSpace n).symm ⁻¹'
        ((C.chart x).symm.trans (C.chart y)).source ∩
        range (modelWithCornersEuclideanHalfSpace n)) :
    modelWithCornersEuclideanHalfSpace n
        (((C.chart x).symm.trans (C.chart y)) ((modelWithCornersEuclideanHalfSpace n).symm z)) =
      ((C.ambientChart x).symm.trans (C.ambientChart y)) z := by
  let ih := modelWithCornersEuclideanHalfSpace n
  have hval : (ih.symm z).val = z := ih.right_inv hz.2
  change ((C.chart y) ((C.chart x).symm (ih.symm z))).val = _
  rw [show ((C.chart y) ((C.chart x).symm (ih.symm z))).val =
      (C.ambientChart y) ((C.chart x).symm (ih.symm z)) from
    OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hz.1.2]
  have hinv := OpenPartialHomeomorph.restrictSubtypes_symm_apply
    (C.ambientChart x).toOpenPartialHomeomorph K {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} x (0 : EuclideanHalfSpace n) (C.mem_iff x) (ih.symm z) hz.1.1
  change ((C.chart x).symm (ih.symm z) : M) = (C.ambientChart x).symm (ih.symm z).val at hinv
  rw [hinv, hval]
  rfl

theorem isManifold :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin n)) _ _ (EuclideanHalfSpace n) _
      (modelWithCornersEuclideanHalfSpace n) ∞ K _ C.toChartedSpace := by
  let : ChartedSpace (EuclideanHalfSpace n) K := C.toChartedSpace
  apply isManifold_of_contDiffOn (modelWithCornersEuclideanHalfSpace n) ∞ K
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  have hc := ((C.ambientChart x).symm.trans (C.ambientChart y)).contMDiffOn_toFun.contDiffOn
  exact (hc.mono (C.change_mem_source x y)).congr (C.change_eq x y)

theorem isBoundaryPoint_iff (x : K) :
    @ModelWithCorners.IsBoundaryPoint ℝ _ (EuclideanSpace ℝ (Fin n)) _ _
      (EuclideanHalfSpace n) _ (modelWithCornersEuclideanHalfSpace n)
      K _ C.toChartedSpace x ↔ C.ambientChart x x.val 0 = 0 := by
  let : ChartedSpace (EuclideanHalfSpace n) K := C.toChartedSpace
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanHalfSpace]
  change (0 = (C.chart x x).val 0) ↔ _
  rw [chart, OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ (C.mem_source x)]
  exact eq_comm

theorem contMDiff_subtype_val :
    letI := C.toChartedSpace
    ContMDiff (modelWithCornersEuclideanHalfSpace n) I ∞ (Subtype.val : K → M) := by
  let : ChartedSpace (EuclideanHalfSpace n) K := C.toChartedSpace
  let : IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ K := C.isManifold
  intro x
  have hext : extChartAt (modelWithCornersEuclideanHalfSpace n) x x =
      C.ambientChart x x.val := by
    change (C.chart x x).val = _
    exact OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ (C.mem_source x)
  have hinv := (C.ambientChart x).contMDiffOn_invFun.contMDiffAt
    ((C.ambientChart x).open_target.mem_nhds
      ((C.ambientChart x).toPartialEquiv.map_source (C.mem_source x)))
  rw [← hext] at hinv
  have hcomp := hinv.comp x (contMDiffAt_extChartAt (I := modelWithCornersEuclideanHalfSpace n)
    (n := ∞) (x := x))
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(C.chart x).open_source.mem_nhds (C.mem_source x)] with y hy
  change y.val = (C.ambientChart x).symm (C.chart x y).val
  rw [chart, OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hy]
  exact ((C.ambientChart x).toPartialEquiv.left_inv hy).symm

end SmoothBoundaryAtlas

end DifferentialGeometry.Topology
