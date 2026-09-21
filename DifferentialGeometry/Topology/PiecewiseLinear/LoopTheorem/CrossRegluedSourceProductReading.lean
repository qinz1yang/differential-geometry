/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceProduct
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedSourceQuarterTurn

/-!
# The pairing of the bent sheets in the crossed product strip

The product strip admits the unrotated reading. A quarter turn of the target chart changes
the pairing of the four pages, and admits no reading of this same source map.
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem crossRegluedProductCell_not_nonempty_reading_quarter_turn :
    ¬ Nonempty (PLCrossSeamReading
      (fun p : (ℝ × ℝ) × ℝ => spliceEmbedding ((-p.1.2, p.1.1), p.2))
      crossRegluedProductCell) :=
  crossRegluedProductReading.not_nonempty_quarter_turn spliceEmbedding.injective.injOn

end DifferentialGeometry.Topology.PiecewiseLinear
