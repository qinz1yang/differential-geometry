import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem hasMFDerivAt_subtype_val (U : TopologicalSpace.Opens M) (x : U) :
    HasMFDerivAt I I (Subtype.val : U → M) x (ContinuousLinearMap.id Real E) := by
  constructor
  · exact continuous_subtype_val.continuousAt
  · let e : OpenPartialHomeomorph U H :=
      (chartAt H (x : M)).subtypeRestr (s := U) (⟨x⟩ : Nonempty U)
    apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _)
    · apply Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin (I := I) x)
      intro y hy
      have hyTarget : I.symm y ∈ e.target := by
        have hy' :
            (∃ z, I z = y) ∧ I.symm y ∈ e.target := by
          simpa [e, extChartAt, TopologicalSpace.Opens.chartAt_eq] using hy
        exact hy'.2
      have hyRange : y ∈ Set.range I := extChartAt_target_subset_range (I := I) x hy
      have hright := e.right_inv hyTarget
      simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      change I ((chartAt H (x : M)) ((e.symm (I.symm y) : U) : M)) = y
      change (chartAt H (x : M)) ((e.symm (I.symm y) : U) : M) = I.symm y at hright
      rw [hright]
      exact I.right_inv hyRange
    · simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      have hleft := (extChartAt I x).left_inv (mem_extChartAt_source x)
      rw [hleft]
      rfl

theorem mfderiv_subtype_val
    (U : TopologicalSpace.Opens M) (x : U) :
    mfderiv I I (Subtype.val : U → M) x = ContinuousLinearMap.id Real E :=
  (hasMFDerivAt_subtype_val (I := I) U x).mfderiv

theorem mfderiv_subtype_val_apply
    (U : TopologicalSpace.Opens M) (x : U) (v : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x v = v := by
  rw [mfderiv_subtype_val (I := I) U x]
  rfl

@[simp] theorem mfderiv_opens_incl {U V : TopologicalSpace.Opens M} (hVU : V ≤ U) (x : V) :
    mfderiv I I (TopologicalSpace.Opens.inclusion hVU : V → U) x =
      ContinuousLinearMap.id Real E := by
  have hinc : MDifferentiableAt I I (TopologicalSpace.Opens.inclusion hVU : V → U) x :=
    ((contMDiff_inclusion hVU).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hval : MDifferentiableAt I I (Subtype.val : U → M)
      (TopologicalSpace.Opens.inclusion hVU x) :=
    ((contMDiff_subtype_val (I := I) (U := U)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp x hval hinc
  change mfderiv I I (Subtype.val : V → M) x =
    (mfderiv I I (Subtype.val : U → M) (TopologicalSpace.Opens.inclusion hVU x)).comp
      (mfderiv I I (TopologicalSpace.Opens.inclusion hVU : V → U) x) at hcomp
  rw [mfderiv_subtype_val (I := I) V x,
    mfderiv_subtype_val (I := I) U (TopologicalSpace.Opens.inclusion hVU x)] at hcomp
  simpa using hcomp.symm

end DifferentialGeometry
