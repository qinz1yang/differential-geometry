/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.Brouwer
import DifferentialGeometry.Topology.FixedPoint.NoRetraction
import DifferentialGeometry.External.ClassificationOfSurfaces.Topology.InvarianceOfDomain

namespace DifferentialGeometry.Topology.FixedPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_fixedPoint_closedBall_of_continuous
    (f : Metric.closedBall (0 : E) 1 → Metric.closedBall (0 : E) 1)
    (hf : Continuous f) :
    ∃ x, f x = x := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    exact ⟨⟨0, by simp⟩, Subsingleton.elim _ _⟩
  have hd : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hdim
  by_contra hfixed
  have hne : ∀ x, f x ≠ x := by
    intro x hx
    exact hfixed ⟨x, hx⟩
  exact not_exists_retraction_closedBall_sphere hd
    (exists_retraction_closedBall_sphere_of_continuous_of_no_fixedPoint f hf hne)

instance : BrouwerFixedPoint E where
  brouwer_fixed_point := exists_fixedPoint_closedBall_of_continuous

end DifferentialGeometry.Topology.FixedPoint
