/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Transition361

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [Nonempty M]

theorem IsPLHomeomorphInto.invFunOn {f : M → N} {P : Set M}
    (hf : IsPLHomeomorphInto n f P) :
    IsPLHomeomorphInto n (Function.invFunOn f P) (f '' P) := by
  have hi := hf.injOn.bijOn_image.invOn_invFunOn
  have hbij : BijOn (Function.invFunOn f P) (f '' P) P := hi.symm.bijOn
    hf.injOn.bijOn_image.surjOn.mapsTo_invFunOn hf.injOn.bijOn_image.mapsTo
  refine ⟨hf.isPLOn_inverse hi.1, hbij.injOn, ?_⟩
  intro y hy
  refine ⟨f, ?_, hi.2⟩
  rw [hbij.image_eq] at hy ⊢
  exact hf.isPLOn y hy

end DifferentialGeometry.Topology.PiecewiseLinear
