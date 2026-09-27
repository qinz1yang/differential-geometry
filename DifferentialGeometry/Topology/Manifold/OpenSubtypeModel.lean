import DifferentialGeometry.Topology.Manifold.OpenSubtype

noncomputable section

open scoped Manifold

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem extChartAt_opens_apply (U : TopologicalSpace.Opens E) (a x : U) :
    extChartAt 𝓘(ℝ, E) a x = (x : E) := rfl

theorem extChartAt_opens_source (U : TopologicalSpace.Opens E) (a : U) :
    (extChartAt 𝓘(ℝ, E) a).source = Set.univ := by
  simp only [extChartAt_source, TopologicalSpace.Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_source, chartAt_self_eq, OpenPartialHomeomorph.refl_source,
    Set.preimage_univ]

theorem extChartAt_opens_target (U : TopologicalSpace.Opens E) (a : U) :
    (extChartAt 𝓘(ℝ, E) a).target = (U : Set E) := by
  simp [extChartAt, TopologicalSpace.Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_def, chartAt_self_eq, mfld_simps]

theorem extChartAt_opens_symm_apply (U : TopologicalSpace.Opens E) (a x : U) :
    (extChartAt 𝓘(ℝ, E) a).symm (x : E) = x :=
  (extChartAt 𝓘(ℝ, E) a).left_inv (by rw [extChartAt_opens_source]; trivial)

theorem mem_interior_extChartAt_opens_target (U : TopologicalSpace.Opens E) (a x : U) :
    (x : E) ∈ interior (extChartAt 𝓘(ℝ, E) a).target := by
  rw [extChartAt_opens_target, U.isOpen.interior_eq]
  exact x.property

theorem continuousLinearMapAt_opens_model (U : TopologicalSpace.Opens E) (a x : U) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).continuousLinearMapAt ℝ x =
      ContinuousLinearMap.id ℝ E := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source,
      chartAt_self_eq]
    trivial)]
  exact mfderiv_subtype_val U x

theorem symmL_opens_model (U : TopologicalSpace.Opens E) (a x : U) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).symmL ℝ x =
      ContinuousLinearMap.id ℝ E := by
  ext v
  have hx : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source, chartAt_self_eq]
    trivial
  have h := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) a).symmL_continuousLinearMapAt (R := ℝ) hx v
  rw [continuousLinearMapAt_opens_model] at h
  exact h

end DifferentialGeometry
