/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDiskTower
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalShellCompression

/-!
# What Lemma 2 buys

This records the single composite statement of the chain that is currently assembled:
Moise's Lemma 2, in the shape the Stallings tower consumes, yields the spherical shell
separation endpoint `Moise304`.

The two halves are proved elsewhere.  `moise252_of_lemmaTwo` runs the tower at the level of
proper PL embedded disks and feeds the result through the bridge that builds a normal system
from a piecewise affine singular disk, giving the unchanged `Moise252` with no properness and
no orientability side condition surviving.  `moise304_of_moise252` is the previously accepted
conditional endpoint.  Composing them isolates exactly what remains to be proved.

Nothing here weakens either half, and nothing here proves Lemma 2.  Its hypothesis is a
genuine open obligation: for a double cover reduction whose upstairs system is proper and
basepoint normalized, an embedded disk upstairs must yield one downstairs.  The surgery behind
it, its branch analysis and its strict descent are not established.
-/

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-- Moise's Lemma 2, in the shape the Stallings tower consumes: a double cover reduction
carries an embedded disk from the covering normal system down to the base one, given that the
covering system's singular map is proper and its basepoint is normalized. -/
def LemmaTwoStatement : Prop :=
  ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {M : ℕ} {S : NormalSystem F} {T : NormalSystem (EuclideanSpace ℝ (Fin M))},
    NormalSystem.DoubleCoverReduction S T →
    T.sourceComplex.space ∩ T.singularMap ⁻¹' T.boundaryComplex.space =
      frontier T.sourceComplex.space →
    T.basepoint = T.boundaryLoop 0 →
    Nonempty (NormalSystem.EmbeddedDisk T) → Nonempty (NormalSystem.EmbeddedDisk S)

/-- Lemma 2 yields the spherical shell separation endpoint.  This is the whole currently
assembled chain in one statement; its hypothesis is the only open mathematical obligation
along it. -/
theorem moise304_of_lemmaTwo (lemmaTwo : LemmaTwoStatement) : Moise304 :=
  moise304_of_moise252 (moise252_of_lemmaTwo lemmaTwo)

end DifferentialGeometry.Topology.PiecewiseLinear
