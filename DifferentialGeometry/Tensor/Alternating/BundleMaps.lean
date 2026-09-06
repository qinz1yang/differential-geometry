import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Multilinear.Fiber

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
  {a : ∀ p, V (b p) [⋀^Fin k]→L[𝕜] 𝕜}
  {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 k F V (b p)}
  {s : Set P} {p₀ : P}

private theorem alternating_trivialization_apply (x₀ x : M)
    (a : V x [⋀^Fin k]→L[𝕜] 𝕜) :
    (trivializationAt (F [⋀^Fin k]→L[𝕜] 𝕜)
      (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜))
      x₀ ⟨x, a⟩).2 = a.compContinuousLinearMap ((trivializationAt F V x₀).symmL 𝕜 x) := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  ext v
  simp [ContinuousAlternatingMap.inCoordinates]

theorem ContMDiffWithinAt.alternating_bundle_toMultilinear
    (ha : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, a p⟩ : TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s p₀) :
    ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s p₀ := by
  rw [contMDiffWithinAt_totalSpace] at ha ⊢
  refine ⟨ha.1, ?_⟩
  let L : (F [⋀^Fin k]→L[𝕜] 𝕜) →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜 :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM
    (E := F) (F := 𝕜) (ι := Fin k) 𝕜
  have hL : ContMDiff 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)
      𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) n L :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜) (E := F [⋀^Fin k]→L[𝕜] 𝕜)
      (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜) L
  have h := hL.contMDiffAt.comp_contMDiffWithinAt p₀ ha.2
  have heq (p : P) :
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V) (b p₀) ⟨b p, (a p).toContinuousMultilinearMap⟩).2 =
      L ((trivializationAt (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜))
        (b p₀) ⟨b p, a p⟩).2) := by
    rw [alternating_trivialization_apply]
    rfl
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall heq) (heq p₀)

theorem ContMDiffWithinAt.multilinear_bundle_alternatization
    (hT : ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s p₀ := by
  rw [contMDiffWithinAt_totalSpace] at hT ⊢
  refine ⟨hT.1, ?_⟩
  let L : ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜 →L[𝕜]
      F [⋀^Fin k]→L[𝕜] 𝕜 := ContinuousMultilinearMap.alternatizationCLM
  have hL : ContMDiff 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
      𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜) n L :=
    ContinuousLinearMap.contMDiff (𝕜 := 𝕜)
      (E := ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
      (F := F [⋀^Fin k]→L[𝕜] 𝕜) L
  have h := hL.contMDiffAt.comp_contMDiffWithinAt p₀ hT.2
  have heq (p : P) :
      (trivializationAt (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜))
        (b p₀) ⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩).2 =
      L ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V) (b p₀) ⟨b p, T p⟩).2) := by
    rw [alternating_trivialization_apply]
    exact (ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap
      (T p) ((trivializationAt F V (b p₀)).symmL 𝕜 (b p))).symm
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall heq) (heq p₀)

theorem ContMDiffAt.alternating_bundle_toMultilinear
    (ha : ContMDiffAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, a p⟩ : TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) p₀) :
    ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) p₀ :=
  ContMDiffWithinAt.alternating_bundle_toMultilinear ha

theorem ContMDiffOn.alternating_bundle_toMultilinear
    (ha : ContMDiffOn J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, a p⟩ : TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s) :
    ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s :=
  fun p hp => (ha p hp).alternating_bundle_toMultilinear

theorem ContMDiff.alternating_bundle_toMultilinear
    (ha : ContMDiff J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, a p⟩ : TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜))))) :
    ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) :=
  fun p => (ha p).alternating_bundle_toMultilinear

theorem ContMDiffAt.multilinear_bundle_alternatization
    (hT : ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) p₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) p₀ :=
  ContMDiffWithinAt.multilinear_bundle_alternatization hT

theorem ContMDiffOn.multilinear_bundle_alternatization
    (hT : ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s :=
  fun p hp => (hT p hp).multilinear_bundle_alternatization

theorem ContMDiff.multilinear_bundle_alternatization
    (hT : ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V)))) :
    ContMDiff J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) :=
  fun p => (hT p).multilinear_bundle_alternatization

theorem MDifferentiableWithinAt.alternating_bundle_toMultilinear
    (ha : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, a p⟩ : TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s p₀) :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s p₀ := by
  have hmap : ContMDiff (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)) 1
      (fun q : TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)) =>
        (⟨q.1, q.2.toContinuousMultilinearMap⟩ : TotalSpace
          (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
          (Bundle.continuousMultilinearMap 𝕜 k F V))) :=
    ContMDiff.alternating_bundle_toMultilinear contMDiff_id
  exact (hmap.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ ha

theorem MDifferentiableAt.alternating_bundle_toMultilinear
    (ha : MDifferentiableAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, a p⟩ : TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) p₀) :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) p₀ :=
  MDifferentiableWithinAt.alternating_bundle_toMultilinear ha

theorem MDifferentiableOn.alternating_bundle_toMultilinear
    (ha : MDifferentiableOn J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, a p⟩ : TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s) :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s :=
  fun p hp => (ha p hp).alternating_bundle_toMultilinear

theorem MDifferentiable.alternating_bundle_toMultilinear
    (ha : MDifferentiable J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, a p⟩ : TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜))))) :
    MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, (a p).toContinuousMultilinearMap⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) :=
  fun p => (ha p).alternating_bundle_toMultilinear

theorem MDifferentiableWithinAt.multilinear_bundle_alternatization
    (hT : MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s p₀) :
    MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s p₀ := by
  have hmap : ContMDiff
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)) 1
      (fun q : TotalSpace (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V) =>
        (⟨q.1, ContinuousMultilinearMap.alternatizationCLM q.2⟩ : TotalSpace
          (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) :=
    ContMDiff.multilinear_bundle_alternatization contMDiff_id
  exact (hmap.mdifferentiableAt (by norm_num)).comp_mdifferentiableWithinAt p₀ hT

theorem MDifferentiableAt.multilinear_bundle_alternatization
    (hT : MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) p₀) :
    MDifferentiableAt J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) p₀ :=
  MDifferentiableWithinAt.multilinear_bundle_alternatization hT

theorem MDifferentiableOn.multilinear_bundle_alternatization
    (hT : MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V))) s) :
    MDifferentiableOn J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) s :=
  fun p hp => (hT p hp).multilinear_bundle_alternatization

theorem MDifferentiable.multilinear_bundle_alternatization
    (hT : MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F V)))) :
    MDifferentiable J (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, ContinuousMultilinearMap.alternatizationCLM (T p)⟩ :
        TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) :=
  fun p => (hT p).multilinear_bundle_alternatization
