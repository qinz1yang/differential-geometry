/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPositionInDouble
import DifferentialGeometry.Topology.PiecewiseLinear.TameNestedCells
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CoverReductionOrientableProducer
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DescentStepOrientable

/-!
# Moise 30.4 and tame 30.5 without hypotheses

The loop-theorem side is closed: the buffered general position in the double
(`generalPositionInDoubleBuffered`, 2026-09-23) and the orientable descent step
(`descentStepOrientableStatement`, 2026-09-24) are real theorems, so the endpoint
`moise304_of_generalPositionBuffered_of_descentStepOrientable` yields `Moise304`, and
`moise305_tame_of_moise304` yields `Moise305Tame`.  Consumers may replace the named inputs
`h304` and `h305` by these producers.
-/

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem moise304 : Moise304 :=
  moise304_of_generalPositionBuffered_of_descentStepOrientable generalPositionInDoubleBuffered
    descentStepOrientableStatement

theorem moise305Tame : Moise305Tame :=
  moise305_tame_of_moise304 moise304

end DifferentialGeometry.Topology.PiecewiseLinear
