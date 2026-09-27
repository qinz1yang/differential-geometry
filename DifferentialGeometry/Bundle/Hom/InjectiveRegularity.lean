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

section Map

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {J : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {b : P → M} {A : ∀ p, V (b p) →L[𝕜] W (b p)}
  {s : ∀ p, V (b p)} {p : P}

theorem ContMDiffWithinAt.of_clm_bundle_apply_of_injective
    {u : Set P}
    (hA : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun q => TotalSpace.mk' (F →L[𝕜] G) (E := fun x => V x →L[𝕜] W x) (b q) (A q)) u p)
    (hAs : ContMDiffWithinAt J (I.prod 𝓘(𝕜, G)) n
      (fun q => TotalSpace.mk' G (E := W) (b q) (A q (s q))) u p)
    (hinj : Function.Injective (A p)) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F)) n (fun q => TotalSpace.mk' F (E := V) (b q) (s q)) u p := by
  let e := trivializationAt F V (b p)
  let f := trivializationAt G W (b p)
  let B := fun q => ContinuousLinearMap.inCoordinates F V G W (b p) (b q) (b p) (b q) (A q)
  let vcoord := fun q => (e ⟨b q, s q⟩).2
  have hAB := (contMDiffWithinAt_hom_bundle _).mp hA
  have hB : ContMDiffWithinAt J 𝓘(𝕜, F →L[𝕜] G) n B u p := hAB.2
  have hBu : ContMDiffWithinAt J 𝓘(𝕜, G) n (fun q => B q (vcoord q)) u p := by
    have h := (contMDiffWithinAt_totalSpace.mp hAs).2
    apply h.congr_of_eventuallyEq
    · filter_upwards [hAB.1.continuousWithinAt (e.open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt F V (b p))),
        hAB.1.continuousWithinAt (f.open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt G W (b p)))] with q he hf
      dsimp only [B, vcoord, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
      rw [← Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e he]
      rw [e.symmL_continuousLinearMapAt he]
      exact Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 f hf _
    · dsimp only [B, vcoord, ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
      rw [← Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 e
        (mem_baseSet_trivializationAt F V (b p))]
      rw [e.symmL_continuousLinearMapAt (mem_baseSet_trivializationAt F V (b p))]
      exact Trivialization.continuousLinearMapAt_apply_of_mem 𝕜 f
        (mem_baseSet_trivializationAt G W (b p)) _
  have hBi : Function.Injective (B p) := by
    dsimp only [B]
    rw [ContinuousLinearMap.inCoordinates_eq
      (mem_baseSet_trivializationAt F V (b p)) (mem_baseSet_trivializationAt G W (b p))]
    exact (f.continuousLinearEquivAt 𝕜 (b p) (mem_baseSet_trivializationAt G W (b p))).injective.comp
      (hinj.comp (e.continuousLinearEquivAt 𝕜 (b p)
        (mem_baseSet_trivializationAt F V (b p))).symm.injective)
  rw [contMDiffWithinAt_totalSpace]
  exact ⟨hAB.1, hB.of_clm_apply_of_injective hBu hBi⟩

theorem ContMDiffOn.of_clm_bundle_apply_of_injective
    {u : Set P}
    (hA : ContMDiffOn J (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun q => TotalSpace.mk' (F →L[𝕜] G)
        (E := fun x => V x →L[𝕜] W x) (b q) (A q)) u)
    (hAs : ContMDiffOn J (I.prod 𝓘(𝕜, G)) n
      (fun q => TotalSpace.mk' G (E := W) (b q) (A q (s q))) u)
    (hinj : ∀ q ∈ u, Function.Injective (A q)) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F)) n (fun q => TotalSpace.mk' F (E := V) (b q) (s q)) u :=
  fun q hq => (hA q hq).of_clm_bundle_apply_of_injective (hAs q hq) (hinj q hq)

end Map

theorem ContMDiffAt.of_clm_bundle_apply_of_injective
    (hA : ContMDiffAt I (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun y => TotalSpace.mk' (F →L[𝕜] G) y (A y)) x)
    (hAs : ContMDiffAt I (I.prod 𝓘(𝕜, G)) n
      (fun y => TotalSpace.mk' G y (A y (s y))) x)
    (hinj : Function.Injective (A x)) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun y => TotalSpace.mk' F y (s y)) x := by
  exact contMDiffWithinAt_univ.mp
    (hA.contMDiffWithinAt.of_clm_bundle_apply_of_injective
      hAs.contMDiffWithinAt hinj)

theorem ContMDiff.of_clm_bundle_apply_of_injective
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] G)) n
      (fun y => TotalSpace.mk' (F →L[𝕜] G) y (A y)))
    (hAs : ContMDiff I (I.prod 𝓘(𝕜, G)) n
      (fun y => TotalSpace.mk' G y (A y (s y))))
    (hinj : ∀ y, Function.Injective (A y)) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun y => TotalSpace.mk' F y (s y)) :=
  fun y => (hA y).of_clm_bundle_apply_of_injective (hAs y) (hinj y)
