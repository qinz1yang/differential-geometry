import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProduct
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceQuarterTurn

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem crossRegluedProductCell_not_nonempty_reading_quarter_turn :
    ¬ Nonempty (PLCrossSeamReading
      (fun p : (ℝ × ℝ) × ℝ => spliceEmbedding ((-p.1.2, p.1.1), p.2))
      crossRegluedProductCell) :=
  crossRegluedProductReading.not_nonempty_quarter_turn spliceEmbedding.injective.injOn

end DifferentialGeometry.Topology.PiecewiseLinear
