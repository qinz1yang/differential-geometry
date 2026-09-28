import DifferentialGeometry.Topology.EMetricSpace.CompactImage

namespace DifferentialGeometry.Analysis

theorem edist_ne_top_of_preconnected {X : Type*} [PseudoEMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ :=
  (EMetric.edist_lt_top_of_continuous_of_preconnected (f := id) continuous_id x y).ne

end DifferentialGeometry.Analysis
