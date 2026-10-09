/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.ClosedBallImage
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalConfiguration

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsTopologicalCellWithInterior.interior_eq
    {n : ℕ} {C I : Set (EuclideanSpace ℝ (Fin n))}
    (h : IsTopologicalCellWithInterior n C I) : interior C = I := by
  rcases h with ⟨φ, hφ⟩
  rw [DifferentialGeometry.Topology.interior_eq_image_of_homeomorphClosedBall φ.symm, hφ,
    image_image]
  congr 1
  ext q
  simp only [mem_preimage, mem_ball, dist_zero_right, mem_ofPred_eq]

theorem IsTopologicalCellWithInterior.interior_mono
    {n : ℕ} {X : Type*} [TopologicalSpace X] {C I D J : Set X}
    (hC : IsTopologicalCellWithInterior n C I)
    (hD : IsTopologicalCellWithInterior n D J) (hCD : C ⊆ D) : I ⊆ J := by
  rcases hC with ⟨φC, hI⟩
  rcases hD with ⟨φD, hJ⟩
  let g : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 →
      EuclideanSpace ℝ (Fin n) := fun q => φD.symm (inclusion hCD (φC q))
  have hgcont : Continuous g := continuous_subtype_val.comp
    (φD.symm.continuous.comp ((continuous_inclusion hCD).comp φC.continuous))
  have hginj : Function.Injective g :=
    Subtype.val_injective.comp
      (φD.symm.injective.comp ((inclusion_injective hCD).comp φC.injective))
  have hrange : range g ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rintro _ ⟨q, rfl⟩
    exact (φD.symm (inclusion hCD (φC q))).property
  have hmain := DifferentialGeometry.Topology.interior_range_eq_image_preimage_interior
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) g hgcont hginj
  have hgball : ∀ q : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      ‖(q : EuclideanSpace ℝ (Fin n))‖ < 1 → ‖g q‖ < 1 := by
    intro q hq
    have hqint : g q ∈ interior (range g) := by
      rw [hmain]
      refine ⟨q, ?_, rfl⟩
      simpa only [mem_preimage, interior_closedBall _ one_ne_zero, mem_ball,
        dist_zero_right] using hq
    have hqball := _root_.interior_mono hrange hqint
    simpa only [interior_closedBall _ one_ne_zero, mem_ball, dist_zero_right] using hqball
  rw [hI, hJ]
  rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
  exact ⟨inclusion hCD (φC q),
    ⟨φD.symm (inclusion hCD (φC q)), hgball q hq,
      φD.apply_symm_apply (inclusion hCD (φC q))⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
