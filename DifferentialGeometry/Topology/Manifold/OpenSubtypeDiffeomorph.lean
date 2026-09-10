import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def openSubtypePartialDiffeomorph (U : TopologicalSpace.Opens M) (hU : Nonempty U) :
    PartialDiffeomorph I I U M ∞ where
  toPartialEquiv := (U.openPartialHomeomorphSubtypeCoe hU).toPartialEquiv
  open_source := (U.openPartialHomeomorphSubtypeCoe hU).open_source
  open_target := (U.openPartialHomeomorphSubtypeCoe hU).open_target
  contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
  contMDiffOn_invFun := by
    intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply (ContMDiffAt.subtypeVal_comp_iff U _ x).mp
    have htarget : x ∈ U := by
      simpa only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using! hx
    apply contMDiffAt_id.congr_of_eventuallyEq
    filter_upwards [U.isOpen.mem_nhds htarget] with y hy
    exact (U.openPartialHomeomorphSubtypeCoe hU).right_inv (by
      simpa only [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target] using hy)

@[simp]
theorem openSubtypePartialDiffeomorph_apply (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) (x : U) : openSubtypePartialDiffeomorph I U hU x = x.val := rfl

@[simp]
theorem openSubtypePartialDiffeomorph_source (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) : (openSubtypePartialDiffeomorph I U hU).source = univ := rfl

@[simp]
theorem openSubtypePartialDiffeomorph_target (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) : (openSubtypePartialDiffeomorph I U hU).target = U :=
  U.openPartialHomeomorphSubtypeCoe_target hU

theorem openSubtypePartialDiffeomorph_symm_apply (U : TopologicalSpace.Opens M)
    (hU : Nonempty U) {x : M} (hx : x ∈ U) :
    (openSubtypePartialDiffeomorph I U hU).symm x = ⟨x, hx⟩ := by
  apply Subtype.ext
  exact (openSubtypePartialDiffeomorph I U hU).right_inv (by simpa using hx)

end Poincare.Manifold
