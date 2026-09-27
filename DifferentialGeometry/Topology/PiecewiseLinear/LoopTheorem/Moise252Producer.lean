/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ExtendedLoopTheoremOrientable
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPositionInDouble
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CoverReductionOrientableProducer
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DescentStepOrientable
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoOrientable

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem moise252 : Moise252 :=
  moise252_of_lemmaTwoOrientable
    (lemmaTwoBufferedOrientableStatement_of_generalPosition_of_descentStepOrientable
      generalPositionInDoubleBuffered descentStepOrientableStatement)

theorem moise264Orientable : Moise264Orientable :=
  moise264_orientable moise252

end DifferentialGeometry.Topology.PiecewiseLinear
