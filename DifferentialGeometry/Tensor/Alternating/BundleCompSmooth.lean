import DifferentialGeometry.Tensor.Alternating.BundleMaps
import DifferentialGeometry.Tensor.Multilinear.BundleComp
import DifferentialGeometry.Tensor.Alternating.Coordinates.Basis
import DifferentialGeometry.Bundle.Hom.Regularity

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {J : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace 𝕜 (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace 𝕜 (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {n : ℕ∞ω} {k : ℕ} {b : P → M}
  {T : ∀ p, V₂ (b p) [⋀^Fin k]→L[𝕜] 𝕜}
  {A : ∀ p, V₁ (b p) →L[𝕜] V₂ (b p)} {s : Set P} {p₀ : P}

theorem ContMDiffWithinAt.alternating_bundle_comp
    (hT : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))) s p₀)
    (hA : ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s p₀) :
    ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ :
        TotalSpace (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) s p₀ := by
  have h := (hT.alternating_bundle_toMultilinear.multilinear_bundle_comp
    (fun _ => hA)).multilinear_bundle_alternatization
  simpa only [ContinuousMultilinearMap.alternatizationCLM_compContinuousLinearMap,
    ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap] using h

theorem ContMDiffAt.alternating_bundle_comp
    (hT : ContMDiffAt J (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))) p₀)
    (hA : ContMDiffAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) p₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ :
        TotalSpace (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) p₀ :=
  ContMDiffWithinAt.alternating_bundle_comp hT hA

theorem ContMDiffOn.alternating_bundle_comp
    (hT : ContMDiffOn J (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))) s)
    (hA : ContMDiffOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s) :
    ContMDiffOn J (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ :
        TotalSpace (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) s :=
  fun p hp => (hT p hp).alternating_bundle_comp (hA p hp)

theorem ContMDiff.alternating_bundle_comp
    (hT : ContMDiff J (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))))
    (hA : ContMDiff J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) :
    ContMDiff J (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ :
        TotalSpace (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) :=
  fun p => (hT p).alternating_bundle_comp (hA p)

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁]

theorem ContMDiff.alternating_bundle_congrLeft
    (φ : ∀ x, V₁ x ≃L[𝕜] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) (k : ℕ) :
    ContMDiff I
      (I.prod 𝓘(𝕜, (F₁ [⋀^Fin k]→L[𝕜] 𝕜) →L[𝕜] F₂ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun x => (⟨x, ((φ x).continuousAlternatingMapCongrLeft (ι := Fin k)
        (F := 𝕜)).toContinuousLinearMap⟩ : TotalSpace
          ((F₁ [⋀^Fin k]→L[𝕜] 𝕜) →L[𝕜] F₂ [⋀^Fin k]→L[𝕜] 𝕜)
          (fun x => (V₁ x [⋀^Fin k]→L[𝕜] 𝕜) →L[𝕜] V₂ x [⋀^Fin k]→L[𝕜] 𝕜))) := by
  let _ : CompleteSpace F₁ := FiniteDimensional.complete 𝕜 F₁
  let _ : FiniteDimensional 𝕜 (F₁ [⋀^Fin k]→L[𝕜] 𝕜) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := k)
      (Module.finBasis 𝕜 F₁)).finiteDimensional_of_finite
  have hφinv : ContMDiff I (I.prod 𝓘(𝕜, F₂ →L[𝕜] F₁)) n
      (fun x => (⟨x, (φ x).symm.toContinuousLinearMap⟩ : TotalSpace (F₂ →L[𝕜] F₁)
        (fun x => V₂ x →L[𝕜] V₁ x))) := by
    simpa only [ContinuousLinearMap.inverse_equiv] using
      hφ.clm_bundle_inverse (fun _ => ContinuousLinearMap.isInvertible_equiv)
  apply ContMDiff.clm_bundle_of_map
  exact (contMDiff_id : ContMDiff
      (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜))
      (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)) n
      (fun p : TotalSpace (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)) => p))
    |>.alternating_bundle_comp (hφinv.comp (contMDiff_proj _))
