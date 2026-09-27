/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.NormalCrossingTransport
import DifferentialGeometry.Topology.PiecewiseLinear.DoublePointFibreAgreement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def HasNormalSingularCrossingAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (D : SingularTwoCell M) (BdM : Set M) (y : M) : Prop :=
  ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
    HasPLNormalDoubleCrossingAt (e ∘ D) (D.domain ∩ D ⁻¹' e.source)
      (e '' (e.source ∩ BdM)) (e y)

theorem buffered_step_preserves_doublePoint_cover
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {G A : SingularTwoCell M} {C V : Set M}
    (hdomain : A.domain = G.domain)
    (hfibre : ∀ z ∉ V, (A : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z} =
      (G : EuclideanSpace ℝ (Fin 2) → M) ⁻¹' {z})
    (hG : doublePointSet G G.domain ⊆ C) (hV : V ⊆ C) :
    doublePointSet A A.domain ⊆ C := by
  have hsub := doublePointSet_subset_of_preimage_singleton_eq_off G.domain hfibre hG hV
  intro y hy
  apply hsub
  rw [← hdomain]
  exact hy

end DifferentialGeometry.Topology.PiecewiseLinear
