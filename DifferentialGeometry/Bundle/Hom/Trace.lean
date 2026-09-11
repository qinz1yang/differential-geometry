import Mathlib.Topology.VectorBundle.Hom
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Trace

noncomputable section
open Bundle Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {M : Type*} [TopologicalSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]

theorem ContinuousWithinAt.trace_bundle
    {Z : Type*} [TopologicalSpace Z] {b : Z → M} {s : Set Z} {z₀ : Z}
    {A : ∀ z, V (b z) →L[𝕜] V (b z)}
    (hA : ContinuousWithinAt (fun z =>
      (TotalSpace.mk' (F →L[𝕜] F) (b z) (A z) :
        TotalSpace (F →L[𝕜] F) (fun x => V x →L[𝕜] V x))) s z₀) :
    ContinuousWithinAt (fun z => LinearMap.trace 𝕜 (V (b z)) (A z).toLinearMap) s z₀ := by
  have hcoord := hA
  rw [continuousWithinAt_hom_bundle] at hcoord
  let tr : (F →L[𝕜] F) →L[𝕜] 𝕜 :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.trace 𝕜 F).comp
        (LinearMap.toContinuousLinearMap :
          (F →ₗ[𝕜] F) ≃ₗ[𝕜] F →L[𝕜] F).symm.toLinearMap)
  have hcontinuous : ContinuousWithinAt
      (fun z => tr (ContinuousLinearMap.inCoordinates
        F V F V (b z₀) (b z) (b z₀) (b z) (A z))) s z₀ :=
    tr.continuous.continuousAt.comp_continuousWithinAt hcoord.2
  let e := trivializationAt F V (b z₀)
  have hb : ContinuousWithinAt b s z₀ := hcoord.1
  have hxbase : b z₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (b z₀)
  have heq (z : Z) (hz : b z ∈ e.baseSet) :
      LinearMap.trace 𝕜 (V (b z)) (A z).toLinearMap =
      tr (ContinuousLinearMap.inCoordinates F V F V (b z₀) (b z) (b z₀) (b z) (A z)) := by
    change LinearMap.trace 𝕜 (V (b z)) (A z).toLinearMap =
      LinearMap.trace 𝕜 F
        (ContinuousLinearMap.inCoordinates F V F V (b z₀) (b z) (b z₀) (b z) (A z)).toLinearMap
    rw [ContinuousLinearMap.inCoordinates_eq hz hz]
    exact (LinearMap.trace_conj' (A z).toLinearMap
      (e.continuousLinearEquivAt 𝕜 (b z) hz).toLinearEquiv).symm
  apply hcontinuous.congr_of_eventuallyEq
  · filter_upwards [hb.eventually (e.open_baseSet.mem_nhds hxbase)] with z hz
    exact heq z hz
  · exact heq z₀ hxbase

theorem ContinuousOn.trace_bundle
    {Z : Type*} [TopologicalSpace Z] {b : Z → M} {s : Set Z}
    {A : ∀ z, V (b z) →L[𝕜] V (b z)}
    (hA : ContinuousOn (fun z =>
      (TotalSpace.mk' (F →L[𝕜] F) (b z) (A z) :
        TotalSpace (F →L[𝕜] F) (fun x => V x →L[𝕜] V x))) s) :
    ContinuousOn (fun z => LinearMap.trace 𝕜 (V (b z)) (A z).toLinearMap) s :=
  fun z hz => (hA z hz).trace_bundle


end
