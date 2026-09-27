import Mathlib.Geometry.Manifold.VectorBundle.Hom
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

open Bundle Filter in
open scoped Manifold ContDiff Topology in
theorem ContMDiffAt.trace_bundle
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
    [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
    [FiberBundle F V] [VectorBundle 𝕜 F V]
    [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
    {n : ℕ∞ω} {b : P → M} {A : ∀ p : P, V (b p) →L[𝕜] V (b p)} {p : P}
    (hA : ContMDiffAt IP (I.prod 𝓘(𝕜, F →L[𝕜] F)) n
      (fun q => (⟨b q, A q⟩ : TotalSpace (F →L[𝕜] F)
        (fun y : M => V y →L[𝕜] V y))) p) :
    ContMDiffAt IP 𝓘(𝕜) n
      (fun q => LinearMap.trace 𝕜 (V (b q)) (A q).toLinearMap) p := by
  have hcoord := (contMDiffAt_hom_bundle
    (f := fun q => (⟨b q, A q⟩ : TotalSpace (F →L[𝕜] F)
      (fun y : M => V y →L[𝕜] V y)))).mp hA
  let tr : (F →L[𝕜] F) →L[𝕜] 𝕜 :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.trace 𝕜 F).comp
        (LinearMap.toContinuousLinearMap :
          (F →ₗ[𝕜] F) ≃ₗ[𝕜] F →L[𝕜] F).symm.toLinearMap)
  have hsmooth : ContMDiffAt IP 𝓘(𝕜) n
      (fun q => tr (ContinuousLinearMap.inCoordinates
        F V F V (b p) (b q) (b p) (b q) (A q))) p :=
    tr.contMDiff.contMDiffAt.comp p hcoord.2
  refine hsmooth.congr_of_eventuallyEq ?_
  have hxbase : b p ∈ (trivializationAt F V (b p)).baseSet :=
    mem_baseSet_trivializationAt F V (b p)
  filter_upwards [hcoord.1.continuousAt
    ((trivializationAt F V (b p)).open_baseSet.mem_nhds hxbase)] with q hq
  change LinearMap.trace 𝕜 (V (b q)) (A q).toLinearMap =
    LinearMap.trace 𝕜 F
      (ContinuousLinearMap.inCoordinates F V F V (b p) (b q) (b p) (b q) (A q)).toLinearMap
  rw [ContinuousLinearMap.inCoordinates_eq hq hq]
  let e := (trivializationAt F V (b p)).continuousLinearEquivAt 𝕜 (b q) hq
  exact (LinearMap.trace_conj' (A q).toLinearMap e.toLinearEquiv).symm
