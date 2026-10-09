/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Mathlib.Topology.OpenPartialHomeomorph.Basic

open Set

namespace DifferentialGeometry.Topology

variable {E M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace E N]

include E in
theorem exists_openPartialHomeomorph_of_continuousOn_injOn [Nonempty M]
    {U : Set M} (hU : IsOpen U) {f : M → N} (hf : ContinuousOn f U) (hinj : InjOn f U) :
    ∃ F : OpenPartialHomeomorph M N, F.source = U ∧ F.target = f '' U ∧
      ∀ x, F x = f x := by
  classical
  have hopen : IsOpenMap (U.domRestrict f) := by
    intro W hW
    have hW' : IsOpen (Subtype.val '' W) := hU.isOpenMap_subtype_val W hW
    have hWU : Subtype.val '' W ⊆ U := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have himage : U.domRestrict f '' W = f '' (Subtype.val '' W) := by
      rw [← image_comp]
      rfl
    rw [himage]
    exact isOpen_image_of_continuousOn_injOn (E := E) hW' (hf.mono hWU) (hinj.mono hWU)
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f U)
    hf hopen hU, rfl, rfl, fun _ => rfl⟩

end DifferentialGeometry.Topology
