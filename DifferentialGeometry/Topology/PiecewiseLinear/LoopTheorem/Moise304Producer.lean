/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPositionInDouble
import DifferentialGeometry.Topology.PiecewiseLinear.TameNestedCells
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CoverReductionOrientableProducer
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DescentStepOrientable

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem moise304 : Moise304 :=
  moise304_of_generalPositionBuffered_of_descentStepOrientable generalPositionInDoubleBuffered
    descentStepOrientableStatement

theorem moise305Tame : Moise305Tame :=
  moise305_tame_of_moise304 moise304

end DifferentialGeometry.Topology.PiecewiseLinear
