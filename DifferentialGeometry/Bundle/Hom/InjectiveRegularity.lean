import DifferentialGeometry.Topology.Manifold.InjectiveRegularity
import DifferentialGeometry.Bundle.Hom.Regularity

set_option autoImplicit false

open Bundle Filter Set
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
  [FiberBundle G W] [VectorBundle 𝕜 G W]
  {n : ℕ∞ω} {A : ∀ x, V x →L[𝕜] W x} {s : ∀ x, V x} {x : M}

theorem ContMDiffAt.of_clm_bundle_apply_of_injective
    (hA : ContMDiffAt I (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun y => TotalSpace.mk' (F →L[𝕜] G) y (A y)) x)
    (hAs : ContMDiffAt I (I.prod 𝓘(𝕜, G)) n
      (fun y => TotalSpace.mk' G y (A y (s y))) x)
    (hinj : Function.Injective (A x)) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun y => TotalSpace.mk' F y (s y)) x := by
  let e := trivializationAt F V x
  let f := trivializationAt G W x
  let B := fun y => ContinuousLinearMap.inCoordinates F V G W x y x y (A y)
  let u := fun y => (e ⟨y, s y⟩).2
  have hB : ContMDiffAt I 𝓘(𝕜, F →L[𝕜] G) n B x :=
    (contMDiffAt_hom_bundle _).mp hA |>.2
  have hBu : ContMDiffAt I 𝓘(𝕜, G) n (fun y => B y (u y)) x := by
    have h := (contMDiffAt_section (F := G) (E := W) x).mp hAs
    apply h.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x),
      f.open_baseSet.mem_nhds (mem_baseSet_trivializationAt G W x)] with y he hf
    dsimp only [B, u, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e he]
    rw [e.symmL_continuousLinearMapAt he]
    exact Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 f hf _
  have hBi : Function.Injective (B x) := by
    dsimp only [B]
    rw [ContinuousLinearMap.inCoordinates_eq
      (mem_baseSet_trivializationAt F V x) (mem_baseSet_trivializationAt G W x)]
    exact (f.continuousLinearEquivAt 𝕜 x (mem_baseSet_trivializationAt G W x)).injective.comp
      (hinj.comp (e.continuousLinearEquivAt 𝕜 x
        (mem_baseSet_trivializationAt F V x)).symm.injective)
  rw [contMDiffAt_section]
  exact hB.of_clm_apply_of_injective hBu hBi

theorem ContMDiff.of_clm_bundle_apply_of_injective
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun y => TotalSpace.mk' (F →L[𝕜] G) y (A y)))
    (hAs : ContMDiff I (I.prod 𝓘(𝕜, G)) n
      (fun y => TotalSpace.mk' G y (A y (s y))))
    (hinj : ∀ y, Function.Injective (A y)) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun y => TotalSpace.mk' F y (s y)) :=
  fun y => (hA y).of_clm_bundle_apply_of_injective (hAs y) (hinj y)
