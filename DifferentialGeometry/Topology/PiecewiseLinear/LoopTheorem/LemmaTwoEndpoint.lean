/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskTower
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalShellCompression

namespace DifferentialGeometry.Topology.PiecewiseLinear

def LemmaTwoStatement : Prop :=
  ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M : ℕ} {S : NormalSystem F} {T : NormalSystem (EuclideanSpace ℝ (Fin M))},
    NormalSystem.DoubleCoverReduction S T →
    T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
      frontier T.sourceComplex.space →
    T.basepoint = T.boundaryLoop 0 →
    Nonempty (NormalSystem.EmbeddedDisk T) → Nonempty (NormalSystem.EmbeddedDisk S)

theorem moise304_of_lemmaTwo (lemmaTwo : LemmaTwoStatement) : Moise304 :=
  moise304_of_moise252 (moise252_of_lemmaTwo lemmaTwo)

end DifferentialGeometry.Topology.PiecewiseLinear
