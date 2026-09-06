import DifferentialGeometry.Tensor.Alternating.Bundle
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

open Bundle Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
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
  {k : ℕ} {b : P → M}
  {T : ∀ p, V₂ (b p) [⋀^Fin k]→L[𝕜] 𝕜}
  {A : ∀ p, V₁ (b p) →L[𝕜] V₂ (b p)} {s : Set P} {p₀ : P}

private theorem alternating_comp_inCoordinates
    (x₀ x : M) (hx : x ∈ (trivializationAt F₂ V₂ x₀).baseSet)
    (T : V₂ x [⋀^Fin k]→L[𝕜] 𝕜) (A : V₁ x →L[𝕜] V₂ x) :
    (trivializationAt (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
      (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)) x₀
      ⟨x, T.compContinuousLinearMap A⟩).2 =
      ((trivializationAt (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)) x₀
        ⟨x, T⟩).2).compContinuousLinearMap
          (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ x x₀ x A) := by
  simp only [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  ext v
  suffices T (fun i => A ((trivializationAt F₁ V₁ x₀).symmL 𝕜 x (v i))) =
    T (fun i => (trivializationAt F₂ V₂ x₀).symmL 𝕜 x
      (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ x x₀ x A (v i))) by
    simpa [ContinuousAlternatingMap.inCoordinates, Function.comp_def] using this
  congr 1
  funext i
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_continuousLinearMapAt _ hx]

theorem MDifferentiableWithinAt.alternating_bundle_comp
    (hT : MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))) s p₀)
    (hA : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s p₀) :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ : TotalSpace
        (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) s p₀ := by
  rw [mdifferentiableWithinAt_totalSpace] at hT ⊢
  refine ⟨hT.1, ?_⟩
  have hAc := ((mdifferentiableWithinAt_hom_bundle _).mp hA).2
  have hcomp : MDifferentiable
      𝓘(𝕜, (F₂ [⋀^Fin k]→L[𝕜] 𝕜) × (F₁ →L[𝕜] F₂))
      𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜)
      (fun z : (F₂ [⋀^Fin k]→L[𝕜] 𝕜) × (F₁ →L[𝕜] F₂) =>
        z.1.compContinuousLinearMap z.2) := by
    apply mdifferentiable_iff_differentiable.mpr
    intro z
    exact differentiableAt_fst.continuousAlternatingMapCompContinuousLinearMap
      differentiableAt_snd
  have h := (hcomp _).comp_mdifferentiableWithinAt p₀ (hT.2.prodMk_space hAc)
  let e := trivializationAt F₂ V₂ (b p₀)
  have hx : b p₀ ∈ e.baseSet := mem_baseSet_trivializationAt F₂ V₂ (b p₀)
  apply h.congr_of_eventuallyEq
  · filter_upwards [hT.1.continuousWithinAt (e.open_baseSet.mem_nhds hx)] with p hp
    exact alternating_comp_inCoordinates (b p₀) (b p) hp (T p) (A p)
  · exact alternating_comp_inCoordinates (b p₀) (b p₀) hx (T p₀) (A p₀)

theorem MDifferentiableAt.alternating_bundle_comp
    (hT : MDifferentiableAt J
      (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))) p₀)
    (hA : MDifferentiableAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) p₀) :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ : TotalSpace
        (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) p₀ :=
  MDifferentiableWithinAt.alternating_bundle_comp hT hA

theorem MDifferentiableOn.alternating_bundle_comp
    (hT : MDifferentiableOn J
      (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))) s)
    (hA : MDifferentiableOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s) :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ : TotalSpace
        (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) s :=
  fun p hp => (hT p hp).alternating_bundle_comp (hA p hp)

theorem MDifferentiable.alternating_bundle_comp
    (hT : MDifferentiable J
      (I.prod 𝓘(𝕜, F₂ [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (F₂ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₂ V₂ 𝕜 (Bundle.Trivial M 𝕜)))))
    (hA : MDifferentiable J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) :
    MDifferentiable J
      (I.prod 𝓘(𝕜, F₁ [⋀^Fin k]→L[𝕜] 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (A p)⟩ : TotalSpace
        (F₁ [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F₁ V₁ 𝕜 (Bundle.Trivial M 𝕜)))) :=
  fun p => (hT p).alternating_bundle_comp (hA p)
