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
