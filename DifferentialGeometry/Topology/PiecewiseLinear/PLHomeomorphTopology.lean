/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsPLHomeomorphOn.image_closure [FiniteDimensional ℝ E] {f : E → F} {P A : Set E} {Q : Set F}
    (hf : IsPLHomeomorphOn f P Q) (hP : IsCompact P) (hAP : A ⊆ P) :
    f '' closure A = closure (f '' A) := by
  have hcl : closure A ⊆ P := closure_minimal hAP hP.isClosed
  exact image_closure_of_isCompact (hP.of_isClosed_subset isClosed_closure hcl)
    (hf.isPiecewiseAffineOn.continuousOn.mono hcl)

theorem IsPLHomeomorphOn.image_interior_subset [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {P : Set E} {Q : Set F} (hf : IsPLHomeomorphOn f P Q)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : f '' interior P ⊆ interior Q := by
  apply interior_maximal (image_subset_iff.mpr (hf.bijOn.mapsTo.mono_left interior_subset))
  exact invariance_of_domain_isOpen_image_of_finrank_eq hdim isOpen_interior
    (hf.isPiecewiseAffineOn.continuousOn.mono interior_subset) (hf.bijOn.injOn.mono interior_subset)

theorem IsPLHomeomorphOn.image_interior [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {P : Set E} {Q : Set F} (hf : IsPLHomeomorphOn f P Q)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) : f '' interior P = interior Q := by
  apply Subset.antisymm (hf.image_interior_subset hdim)
  intro y hy
  exact ⟨Function.invFunOn f P y, hf.symm.image_interior_subset hdim.symm ⟨y, hy, rfl⟩,
    hf.bijOn.invOn_invFunOn.2 (interior_subset hy)⟩

theorem IsPLHomeomorphOn.image_frontier [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {P : Set E} {Q : Set F} (hf : IsPLHomeomorphOn f P Q)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hP : IsClosed P) (hQ : IsClosed Q) :
    f '' frontier P = frontier Q := by
  rw [frontier, hP.closure_eq, hf.bijOn.injOn.image_sdiff_subset interior_subset,
    hf.image_eq, hf.image_interior hdim, frontier, hQ.closure_eq]

end DifferentialGeometry.Topology.PiecewiseLinear
