/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Schoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesFoundations

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.isSimplyEmbedded {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsPLSphere 2 S) : IsSimplyEmbedded S :=
  isSimplyEmbedded_of_isPLSphere_two schoenflies_input hS

theorem IsPLSphere.exists_isPLBall_frontier_eq {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsPLSphere 2 S) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 B ∧ frontier B = S ∧ Bornology.IsBounded B :=
  exists_isPLBall_of_isPLSphere_two schoenflies_input hS

theorem forall_isSimplyEmbedded_of_isPLSphere_two :
    ∀ S : Set (EuclideanSpace ℝ (Fin 3)), IsPLSphere 2 S → IsSimplyEmbedded S :=
  fun _ hS => hS.isSimplyEmbedded

end DifferentialGeometry.Topology.PiecewiseLinear
