import DifferentialGeometry.Tensor.Multilinear.Fiber
import Mathlib.Geometry.Manifold.VectorBundle.Hom

open Bundle Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {J : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : WithTop ℕ∞} {k : ℕ} {b : P → M}
  {T : ∀ p, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => V (b p)) 𝕜}
  {s : Set P} {p₀ : P}

private theorem curryLeftEquiv_inCoordinates
    (x₀ x : M) (hx : x ∈ (trivializationAt F V x₀).baseSet)
    (T : Bundle.continuousMultilinearMap 𝕜 (k + 1) F V x) :
    ContinuousLinearMap.inCoordinates F V
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 k F V) x₀ x x₀ x
      (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k x T) =
    continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => F) 𝕜
      ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V) x₀ ⟨x, T⟩).2) := by
  ext v w
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem]
  · change (T.curryLeft ((trivializationAt F V x₀).symmL 𝕜 x v)).compContinuousLinearMap
      (fun _ => (trivializationAt F V x₀).symmL 𝕜 x) w =
      (T.compContinuousLinearMap (fun _ => (trivializationAt F V x₀).symmL 𝕜 x)).curryLeft v w
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.curryLeft_apply]
    congr 1
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  · exact hx


theorem ContMDiffWithinAt.multilinear_bundle_curry_left
    (hT : ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s p₀) :
    ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s p₀ := by
  rw [contMDiffWithinAt_totalSpace] at hT
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨hT.1, ?_⟩
  let L : (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) →L[𝕜]
      (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) :=
    (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => F) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ContMDiff
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
      𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) n L :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜)
      (E := ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
      (F := F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) L
  have h := hL.contMDiffAt.comp_contMDiffWithinAt p₀ hT.2
  let e := trivializationAt F V (b p₀)
  have hx : b p₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (b p₀)
  apply h.congr_of_eventuallyEq
  · have hbase : ∀ᶠ p in 𝓝[s] p₀, b p ∈ e.baseSet :=
      hT.1.continuousWithinAt (e.open_baseSet.mem_nhds hx)
    filter_upwards [hbase] with p hp
    exact curryLeftEquiv_inCoordinates (b p₀) (b p) hp (T p)
  · exact curryLeftEquiv_inCoordinates (b p₀) (b p₀) hx (T p₀)

theorem ContMDiffAt.multilinear_bundle_curry_left
    (hT : ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) p₀) :
    ContMDiffAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) p₀ :=
  ContMDiffWithinAt.multilinear_bundle_curry_left hT

theorem ContMDiffOn.multilinear_bundle_curry_left
    (hT : ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s) :
    ContMDiffOn J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s :=
  fun p hp => (hT p hp).multilinear_bundle_curry_left

theorem ContMDiff.multilinear_bundle_curry_left
    (hT : ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V)))) :
    ContMDiff J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) :=
  fun p => (hT p).multilinear_bundle_curry_left

theorem ContMDiffWithinAt.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s p₀) :
    ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s p₀ := by
  rw [contMDiffWithinAt_hom_bundle] at hA
  rw [contMDiffWithinAt_totalSpace]
  refine ⟨hA.1, ?_⟩
  let L := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => F) 𝕜).toContinuousLinearEquiv
  have hL : ContMDiff
      𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) n L.symm :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜)
      (E := F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
      (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) L.symm.toContinuousLinearMap
  have h := hL.contMDiffAt.comp_contMDiffWithinAt p₀ hA.2
  let e := trivializationAt F V (b p₀)
  have hx : b p₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V (b p₀)
  have hinv (S : ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) :
      L.symm (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => F) 𝕜 S) = S :=
    L.symm_apply_apply S
  have heq (p : P) (hp : b p ∈ e.baseSet) :=
    congrArg L.symm (curryLeftEquiv_inCoordinates (b p₀) (b p) hp
      ((Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)))
  apply h.congr_of_eventuallyEq
  · have hbase : ∀ᶠ p in 𝓝[s] p₀, b p ∈ e.baseSet :=
      hA.1.continuousWithinAt (e.open_baseSet.mem_nhds hx)
    filter_upwards [hbase] with p hp
    simpa only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
      hinv, Function.comp_apply] using (heq p hp).symm
  · simpa only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply,
      hinv, Function.comp_apply] using (heq p₀ hx).symm

theorem ContMDiffAt.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : ContMDiffAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) p₀) :
    ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) p₀ :=
  ContMDiffWithinAt.multilinear_bundle_uncurry_left hA

theorem ContMDiffOn.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : ContMDiffOn J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s) :
    ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s :=
  fun p hp => (hA p hp).multilinear_bundle_uncurry_left

theorem ContMDiff.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : ContMDiff J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x)))) :
    ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) n
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) :=
  fun p => (hA p).multilinear_bundle_uncurry_left

theorem MDifferentiableWithinAt.multilinear_bundle_curry_left
    (hT : MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s p₀) :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s p₀ := by
  have hmap : ContMDiff (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) 1
      (fun q : TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V) =>
        (⟨q.1, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k q.1 q.2⟩ : TotalSpace (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) :=
    ContMDiff.multilinear_bundle_curry_left contMDiff_id
  exact (hmap.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ hT

theorem MDifferentiableAt.multilinear_bundle_curry_left
    (hT : MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) p₀) :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) p₀ :=
  MDifferentiableWithinAt.multilinear_bundle_curry_left hT

theorem MDifferentiableOn.multilinear_bundle_curry_left
    (hT : MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s) :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s :=
  fun p hp => (hT p hp).multilinear_bundle_curry_left

theorem MDifferentiable.multilinear_bundle_curry_left
    (hT : MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V)))) :
    MDifferentiable J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p) (T p)⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) :=
  fun p => (hT p).multilinear_bundle_curry_left

theorem MDifferentiableWithinAt.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, A p⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s p₀) :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s p₀ := by
  have hmap : ContMDiff (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)) 1
      (fun q : TotalSpace (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x) =>
        (⟨q.1, (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k q.1).symm q.2⟩ : TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜) (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) :=
    ContMDiff.multilinear_bundle_uncurry_left contMDiff_id
  exact (hmap.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ hA

theorem MDifferentiableAt.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : MDifferentiableAt J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, A p⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) p₀) :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) p₀ :=
  MDifferentiableWithinAt.multilinear_bundle_uncurry_left hA

theorem MDifferentiableOn.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : MDifferentiableOn J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, A p⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x))) s) :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) s :=
  fun p hp => (hA p hp).multilinear_bundle_uncurry_left

theorem MDifferentiable.multilinear_bundle_uncurry_left
    {A : ∀ p, V (b p) →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
    (hA : MDifferentiable J
      (I.prod 𝓘(𝕜, F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, A p⟩ : TotalSpace
        (F →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (fun x => V x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 k F V x)))) :
    MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜))
      (fun p => (⟨b p,
        (Bundle.continuousMultilinearMap.curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := V) k (b p)).symm (A p)⟩ :
        TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin (k + 1) => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 (k + 1) F V))) :=
  fun p => (hA p).multilinear_bundle_uncurry_left

theorem contMDiffWithinAt_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) s p₀ ↔
      ContMDiffWithinAt J I n b s p₀ ∧
        ContMDiffWithinAt J 𝓘(𝕜, 𝕜) n (fun p => T p Fin.elim0) s p₀ := by
  rw [contMDiffWithinAt_totalSpace]
  let L := (continuousMultilinearCurryFin0 𝕜 F 𝕜).toContinuousLinearEquiv
  have hL : ContMDiff 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      𝓘(𝕜, 𝕜) n L :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜)
      (E := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      (F := 𝕜) L.toContinuousLinearMap
  have hLinv : ContMDiff 𝓘(𝕜, 𝕜)
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) n L.symm :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜) (E := 𝕜)
      (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) L.symm.toContinuousLinearMap
  have heq (p : P) :
      L ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V) (b p₀) ⟨b p, T p⟩).2) =
        T p Fin.elim0 :=
    Bundle.continuousMultilinearMap.triv_zero_apply_eq (b p₀) (b p) (T p) 0
  constructor
  · rintro ⟨hb, hT⟩
    refine ⟨hb, ?_⟩
    exact (hL.contMDiffAt.comp_contMDiffWithinAt p₀ hT).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => (heq p).symm) (heq p₀).symm
  · rintro ⟨hb, hT⟩
    refine ⟨hb, ?_⟩
    have heq' (p : P) := congrArg L.symm (heq p)
    exact (hLinv.contMDiffAt.comp_contMDiffWithinAt p₀ hT).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => by simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply]
        using (heq' p)) (by simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply] using (heq' p₀))

theorem contMDiffAt_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) p₀ ↔
      ContMDiffAt J I n b p₀ ∧
        ContMDiffAt J 𝓘(𝕜, 𝕜) n (fun p => T p Fin.elim0) p₀ := contMDiffWithinAt_multilinear_bundle_zero

theorem contMDiffOn_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) s ↔
      ContMDiffOn J I n b s ∧
        ContMDiffOn J 𝓘(𝕜, 𝕜) n (fun p => T p Fin.elim0) s := by
  constructor
  · intro h
    exact ⟨fun p hp => (contMDiffWithinAt_multilinear_bundle_zero.mp (h p hp)).1,
      fun p hp => (contMDiffWithinAt_multilinear_bundle_zero.mp (h p hp)).2⟩
  · rintro ⟨hb, hT⟩ p hp
    exact contMDiffWithinAt_multilinear_bundle_zero.mpr ⟨hb p hp, hT p hp⟩

theorem contMDiff_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) ↔
      ContMDiff J I n b ∧
        ContMDiff J 𝓘(𝕜, 𝕜) n (fun p => T p Fin.elim0) := by
  constructor
  · intro h
    exact ⟨fun p => (contMDiffAt_multilinear_bundle_zero.mp (h p)).1,
      fun p => (contMDiffAt_multilinear_bundle_zero.mp (h p)).2⟩
  · rintro ⟨hb, hT⟩ p
    exact contMDiffAt_multilinear_bundle_zero.mpr ⟨hb p, hT p⟩

theorem mdifferentiableWithinAt_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) s p₀ ↔
      MDifferentiableWithinAt J I b s p₀ ∧
        MDifferentiableWithinAt J 𝓘(𝕜, 𝕜) (fun p => T p Fin.elim0) s p₀ := by
  rw [mdifferentiableWithinAt_totalSpace]
  let L := (continuousMultilinearCurryFin0 𝕜 F 𝕜).toContinuousLinearEquiv
  have hL : ContMDiff 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      𝓘(𝕜, 𝕜) 1 L :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜)
      (E := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
      (F := 𝕜) L.toContinuousLinearMap
  have hLinv : ContMDiff 𝓘(𝕜, 𝕜)
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) 1 L.symm :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜) (E := 𝕜)
      (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜) L.symm.toContinuousLinearMap
  have heq (p : P) :
      L ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V) (b p₀) ⟨b p, T p⟩).2) =
        T p Fin.elim0 :=
    Bundle.continuousMultilinearMap.triv_zero_apply_eq (b p₀) (b p) (T p) 0
  constructor
  · rintro ⟨hb, hT⟩
    refine ⟨hb, ?_⟩
    exact ((hL.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ hT).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => (heq p).symm) (heq p₀).symm
  · rintro ⟨hb, hT⟩
    refine ⟨hb, ?_⟩
    have heq' (p : P) := congrArg L.symm (heq p)
    exact ((hLinv.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ hT).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => by simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply]
        using (heq' p)) (by simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply] using (heq' p₀))

theorem mdifferentiableAt_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) p₀ ↔
      MDifferentiableAt J I b p₀ ∧
        MDifferentiableAt J 𝓘(𝕜, 𝕜) (fun p => T p Fin.elim0) p₀ := mdifferentiableWithinAt_multilinear_bundle_zero

theorem mdifferentiableOn_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) s ↔
      MDifferentiableOn J I b s ∧
        MDifferentiableOn J 𝓘(𝕜, 𝕜) (fun p => T p Fin.elim0) s := by
  constructor
  · intro h
    exact ⟨fun p hp => (mdifferentiableWithinAt_multilinear_bundle_zero.mp (h p hp)).1,
      fun p hp => (mdifferentiableWithinAt_multilinear_bundle_zero.mp (h p hp)).2⟩
  · rintro ⟨hb, hT⟩ p hp
    exact mdifferentiableWithinAt_multilinear_bundle_zero.mpr ⟨hb p hp, hT p hp⟩

theorem mdifferentiable_multilinear_bundle_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)} :
    MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V))) ↔
      MDifferentiable J I b ∧
        MDifferentiable J 𝓘(𝕜, 𝕜) (fun p => T p Fin.elim0) := by
  constructor
  · intro h
    exact ⟨fun p => (mdifferentiableAt_multilinear_bundle_zero.mp (h p)).1,
      fun p => (mdifferentiableAt_multilinear_bundle_zero.mp (h p)).2⟩
  · rintro ⟨hb, hT⟩ p
    exact mdifferentiableAt_multilinear_bundle_zero.mpr ⟨hb p, hT p⟩

theorem ContMDiff.multilinear_bundle_curry_zero
    {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 0 F V (b p)}
    (hT : ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 0 F V)))) :
    ContMDiff J (I.prod 𝓘(𝕜, 𝕜)) n
      (fun p => (⟨b p, Bundle.continuousMultilinearMap.curryFin0Equiv
        (𝕜 := 𝕜) (F := F) (E := V) (b p) (T p)⟩ : TotalSpace 𝕜 (Bundle.Trivial M 𝕜))) := by
  obtain ⟨hb, hs⟩ := contMDiff_multilinear_bundle_zero.mp hT
  intro p
  rw [contMDiffAt_totalSpace]
  refine ⟨hb p, ?_⟩
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.trivialization_apply, Bundle.continuousMultilinearMap.curryFin0Equiv_apply]
    using hs p

theorem ContMDiff.multilinear_bundle_uncurry_zero
    {A : P → 𝕜}
    (hA : ContMDiff J (I.prod 𝓘(𝕜, 𝕜)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace 𝕜 (Bundle.Trivial M 𝕜)))) :
    ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)) n
      (fun p => (⟨b p, (Bundle.continuousMultilinearMap.curryFin0Equiv
        (𝕜 := 𝕜) (F := F) (E := V) (b p)).symm (A p)⟩ : TotalSpace
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 0 F V))) := by
  rw [contMDiff_multilinear_bundle_zero]
  constructor
  · intro p
    exact (contMDiffAt_totalSpace.mp (hA p)).1
  · intro p
    have h := (contMDiffAt_totalSpace.mp (hA p)).2
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.trivialization_apply,
      Bundle.continuousMultilinearMap.curryFin0Equiv_symm_apply] using h
