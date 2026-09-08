import DifferentialGeometry.Tensor.Alternating.Bundle
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations

open Bundle Filter Set
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

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners 𝕜 EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {F₀ F : Type*} [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem mdifferentiableWithinAt_clm_of_pointwise
    [FiniteDimensional 𝕜 F₀]
    {A : P → (F₀ →L[𝕜] F)} {J : Set P} {p : P}
    (h : ∀ v, MDifferentiableWithinAt IP 𝓘(𝕜, F) (fun q => A q v) J p) :
    MDifferentiableWithinAt IP 𝓘(𝕜, F₀ →L[𝕜] F) A J p := by
  let d := Module.finrank 𝕜 F₀
  have hd : d = Module.finrank 𝕜 (Fin d → 𝕜) := (Module.finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  have hEA : MDifferentiableWithinAt IP 𝓘(𝕜, Fin d → F) (e₂ ∘ A) J p := by
    have hpi : ∀ i : Fin d, MDifferentiableWithinAt IP 𝓘(𝕜, F)
        (fun q => (e₂ ∘ A) q i) J p := fun i => h _
    simpa only [mdifferentiableWithinAt_iff, continuousWithinAt_pi,
      differentiableWithinAt_pi, forall_and, extChartAt_model_space_eq_id,
      Function.comp_def, PartialEquiv.refl_coe, id] using hpi
  have hA : A = e₂.symm ∘ e₂ ∘ A := by
    funext q
    exact (e₂.symm_apply_apply (A q)).symm
  rw [hA]
  exact e₂.symm.differentiable.mdifferentiable.mdifferentiableAt.comp_mdifferentiableWithinAt p hEA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

theorem mdifferentiableWithinAt_alternating_congrLeft_of_pointwise
    (k : ℕ) (γ : P → M) (T : ∀ p, F₀ ≃L[𝕜] V (γ p))
    (a : F₀ [⋀^Fin k]→L[𝕜] 𝕜) {J : Set P} {p : P}
    (hT : ∀ v, MDifferentiableWithinAt IP (I.prod 𝓘(𝕜, F))
      (fun q => (⟨γ q, T q v⟩ : TotalSpace F V)) J p) :
    MDifferentiableWithinAt IP (I.prod 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜))
      (fun q => (⟨γ q, (T q).continuousAlternatingMapCongrLeft a⟩ :
        TotalSpace (F [⋀^Fin k]→L[𝕜] 𝕜)
          (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)))) J p := by
  let e := trivializationAt F V (γ p)
  have he : γ p ∈ e.baseSet := mem_baseSet_trivializationAt F V (γ p)
  let C := (T p).trans (e.continuousLinearEquivAt 𝕜 (γ p) he)
  let : FiniteDimensional 𝕜 F₀ :=
    FiniteDimensional.of_injective C.toLinearMap C.injective
  have : CompleteSpace F₀ := FiniteDimensional.complete 𝕜 F₀
  let A := fun q => (e.continuousLinearMapAt 𝕜 (γ q)).comp (T q).toContinuousLinearMap
  have hγ := ((mdifferentiableWithinAt_totalSpace I _).mp (hT 0)).1
  have hpre : ∀ᶠ q in 𝓝[J] p, γ q ∈ e.baseSet :=
    hγ.continuousWithinAt (e.open_baseSet.mem_nhds he)
  have hA : MDifferentiableWithinAt IP 𝓘(𝕜, F₀ →L[𝕜] F) A J p := by
    apply mdifferentiableWithinAt_clm_of_pointwise
    intro v
    have hh := ((mdifferentiableWithinAt_totalSpace I _).mp (hT v)).2
    apply hh.congr_of_eventuallyEq
    · filter_upwards [hpre] with q hq
      exact e.continuousLinearMapAt_apply_of_mem 𝕜 hq (T q v)
    · exact e.continuousLinearMapAt_apply_of_mem 𝕜 he (T p v)
  have hAp : A p = C.toContinuousLinearMap := by
    exact (congrArg (fun L : V (γ p) →L[𝕜] F => L.comp (T p).toContinuousLinearMap)
      (e.coe_continuousLinearEquivAt_eq' (R := 𝕜) he)).symm
  have hinv : MDifferentiableAt 𝓘(𝕜, F₀ →L[𝕜] F) 𝓘(𝕜, F →L[𝕜] F₀)
      ContinuousLinearMap.inverse (A p) := by
    rw [hAp]
    exact ((contDiffAt_map_inverse (n := 1) C).differentiableAt one_ne_zero).mdifferentiableAt
  have hAi := hinv.comp_mdifferentiableWithinAt p hA
  have hcomp : MDifferentiable 𝓘(𝕜, F →L[𝕜] F₀) 𝓘(𝕜, F [⋀^Fin k]→L[𝕜] 𝕜)
      (fun B : F →L[𝕜] F₀ => a.compContinuousLinearMap B) := by
    apply mdifferentiable_iff_differentiable.mpr
    intro B
    exact DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap
      (differentiableAt_const (c := a)) differentiableAt_id
  have ha := (hcomp _).comp_mdifferentiableWithinAt p hAi
  have hcoord (q : P) (hq : γ q ∈ e.baseSet) :
      (trivializationAt (F [⋀^Fin k]→L[𝕜] 𝕜)
        (Bundle.continuousAlternatingMap 𝕜 (Fin k) F V 𝕜 (Bundle.Trivial M 𝕜)) (γ p)
        ⟨γ q, (T q).continuousAlternatingMapCongrLeft a⟩).2 =
      a.compContinuousLinearMap (A q).inverse := by
    let Cq := (T q).trans (e.continuousLinearEquivAt 𝕜 (γ q) hq)
    have hAq : A q = Cq.toContinuousLinearMap := by
      exact (congrArg (fun L : V (γ q) →L[𝕜] F => L.comp (T q).toContinuousLinearMap)
        (e.coe_continuousLinearEquivAt_eq' (R := 𝕜) hq)).symm
    rw [hAq, ContinuousLinearMap.inverse_equiv Cq]
    simp only [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
    ext v
    simp [ContinuousAlternatingMap.inCoordinates,
      ContinuousLinearEquiv.continuousAlternatingMapCongrLeft_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
      Cq, Trivialization.symmL_apply, hq, e]
  rw [mdifferentiableWithinAt_totalSpace]
  refine ⟨hγ, ?_⟩
  apply ha.congr_of_eventuallyEq
  · filter_upwards [hpre] with q hq
    exact hcoord q hq
  · exact hcoord p he

end
