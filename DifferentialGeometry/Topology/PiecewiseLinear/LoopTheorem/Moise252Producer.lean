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

/-!
# Moise 25.2 and the orientable extended loop theorem without hypotheses

The buffered general position in the double (`generalPositionInDoubleBuffered`) and the
orientable descent step (`descentStepOrientableStatement`) are theorems of the tree.  They give
the orientable buffered Lemma 2, and the orientable cover reduction turns it into the polyhedral
loop theorem `Moise252` (`moise252`).  The orientable extended loop theorem `Moise264Orientable`
follows by `moise264_orientable` (`moise264Orientable`).
-/

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem moise252 : Moise252 :=
  moise252_of_lemmaTwoOrientable
    (lemmaTwoBufferedOrientableStatement_of_generalPosition_of_descentStepOrientable
      generalPositionInDoubleBuffered descentStepOrientableStatement)

theorem moise264Orientable : Moise264Orientable :=
  moise264_orientable moise252

end DifferentialGeometry.Topology.PiecewiseLinear
