/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLPieceBallInterior

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem PLPieceIn.crossing_sides_of_isPLBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X]
    {W : Set X} (T : PLPieceIn E (n + 1) X W) (hdim : Module.finrank ℝ E = n + 1)
    {A B : Set E} (hA : IsPLBall (n + 1) A) (hB : IsPLBall (n + 1) B)
    (hAT : A ⊆ T.complex.space) (hBT : B ⊆ T.complex.space)
    (hin : frontier A ∩ frontier B ⊆ closure (frontier A ∩ interior B))
    (hout : frontier A ∩ frontier B ⊆ closure (frontier A \ B)) :
    (frontier (T.map '' A) ∩ frontier (T.map '' B) ⊆
      closure (frontier (T.map '' A) ∩ interior (T.map '' B))) ∧
    frontier (T.map '' A) ∩ frontier (T.map '' B) ⊆
      closure (frontier (T.map '' A) \ (T.map '' B)) := by
  have hAf := T.frontier_image_of_isPLBall hdim hA hAT
  have hBf := T.frontier_image_of_isPLBall hdim hB hBT
  have hBi := T.image_interior_of_isPLBall hdim hB hBT
  have hfrontAT : frontier A ⊆ T.complex.space :=
    hA.isPolyhedron.isClosed.frontier_subset.trans hAT
  have hfrontBT : frontier B ⊆ T.complex.space :=
    hB.isPolyhedron.isClosed.frontier_subset.trans hBT
  have hfront : frontier (T.map '' A) ∩ frontier (T.map '' B) =
      T.map '' (frontier A ∩ frontier B) :=
    (congrArg₂ (· ∩ ·) hAf hBf).trans (T.bijOn.injOn.image_inter hfrontAT hfrontBT).symm
  have htransfer {S : Set E} {V : Set X} (hST : S ⊆ T.complex.space)
      (hS : frontier A ∩ frontier B ⊆ closure S) (hSV : T.map '' S ⊆ V) :
      frontier (T.map '' A) ∩ frontier (T.map '' B) ⊆ closure V := by
    rw [hfront]
    exact (image_mono hS).trans
      ((T.continuousOn.mono (closure_minimal hST T.isPolyhedron_space.isClosed)).image_closure.trans
        (closure_mono hSV))
  constructor
  · apply htransfer (inter_subset_left.trans hfrontAT) hin
    rintro x ⟨y, hy, rfl⟩
    exact ⟨hAf.symm.subset ⟨y, hy.1, rfl⟩, hBi.subset ⟨y, hy.2, rfl⟩⟩
  · apply htransfer (sdiff_subset.trans hfrontAT) hout
    rintro x ⟨y, hy, rfl⟩
    refine ⟨hAf.symm.subset ⟨y, hy.1, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzy⟩
    exact hy.2 ((T.bijOn.injOn (hBT hz) (hfrontAT hy.1) hzy) ▸ hz)

end DifferentialGeometry.Topology.PiecewiseLinear
