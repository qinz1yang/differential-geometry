/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open Set Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

theorem isOpen_setOf_isLocalDiffeomorphAt
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G) (n : WithTop ℕ∞) (f : M → N) :
    IsOpen {x | IsLocalDiffeomorphAt I J n f x} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨φ, hx, hφ⟩
  exact Filter.mem_of_superset (φ.open_source.mem_nhds hx) (fun y hy => ⟨φ, hy, hφ⟩)
