import DifferentialGeometry.Tensor.Multilinear.Fiber
import Mathlib.Geometry.Manifold.VectorBundle.Hom

noncomputable section

open Bundle Filter
open scoped Manifold ContDiff Topology

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ : B → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace 𝕜 (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  {V₂ : B → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace 𝕜 (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  {k : ℕ}

def compContinuousLinearMapL (x : B) (A : Fin k → V₁ x →L[𝕜] V₂ x) :
    Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ x →L[𝕜]
      Bundle.continuousMultilinearMap 𝕜 k F₁ V₁ x :=
  (fiberContinuousLinearEquiv (F := F₁) k x).symm.toContinuousLinearMap.comp
    ((ContinuousMultilinearMap.compContinuousLinearMapL A).comp
      (fiberContinuousLinearEquiv (F := F₂) k x).toContinuousLinearMap)

@[simp] theorem compContinuousLinearMapL_apply (x : B)
    (A : Fin k → V₁ x →L[𝕜] V₂ x)
    (T : Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ x) (v : Fin k → V₁ x) :
    compContinuousLinearMapL (F₁ := F₁) (F₂ := F₂) x A T v =
      T (fun i => A i (v i)) := rfl

def congrLeft (x : B) (φ : Fin k → V₁ x ≃L[𝕜] V₂ x) :
    Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ x ≃L[𝕜]
      Bundle.continuousMultilinearMap 𝕜 k F₁ V₁ x :=
  (fiberContinuousLinearEquiv (F := F₂) k x).trans
    ((ContinuousLinearEquiv.continuousMultilinearMapCongrLeft 𝕜 φ).trans
      (fiberContinuousLinearEquiv (F := F₁) k x).symm)

@[simp] theorem congrLeft_apply (x : B) (φ : Fin k → V₁ x ≃L[𝕜] V₂ x)
    (T : Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ x) (v : Fin k → V₁ x) :
    congrLeft (F₁ := F₁) (F₂ := F₂) x φ T v = T (fun i => φ i (v i)) := rfl

@[simp] theorem congrLeft_symm (x : B) (φ : Fin k → V₁ x ≃L[𝕜] V₂ x) :
    (congrLeft (F₁ := F₁) (F₂ := F₂) x φ).symm =
      congrLeft (F₁ := F₂) (F₂ := F₁) x (fun i => (φ i).symm) := rfl

end Bundle.continuousMultilinearMap

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
  {n : WithTop ℕ∞} {k : ℕ} {b : P → M}
  {T : ∀ p, Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ (b p)}
  {A : Fin k → ∀ p, V₁ (b p) →L[𝕜] V₂ (b p)} {s : Set P} {p₀ : P}

private theorem multilinear_comp_inCoordinates
    (x₀ x : M) (hx : x ∈ (trivializationAt F₂ V₂ x₀).baseSet)
    (T : Bundle.continuousMultilinearMap 𝕜 k F₂ V₂ x)
    (A : Fin k → V₁ x →L[𝕜] V₂ x) :
    (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁) x₀
        ⟨x, T.compContinuousLinearMap A⟩).2 =
      ((trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂) x₀ ⟨x, T⟩).2).compContinuousLinearMap
        (fun i => ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ x x₀ x (A i)) := by
  ext v
  change T (fun i => A i ((trivializationAt F₁ V₁ x₀).symmL 𝕜 x (v i))) =
    T (fun i => (trivializationAt F₂ V₂ x₀).symmL 𝕜 x
      (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ x x₀ x (A i) (v i)))
  congr 1
  funext i
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_continuousLinearMapAt _ hx]

theorem ContMDiffWithinAt.multilinear_bundle_comp
    (hT : ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) s p₀)
    (hA : ∀ i, ContMDiffWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A i p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s p₀) :
    ContMDiffWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) s p₀ := by
  rw [contMDiffWithinAt_totalSpace] at hT ⊢
  refine ⟨hT.1, ?_⟩
  have hAc := fun i => ((contMDiffWithinAt_hom_bundle _).mp (hA i)).2
  let L := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : Fin k => F₁) (fun _ : Fin k => F₂) 𝕜
  have h := ((L.contDiff (n := n)).contMDiff.contMDiffAt.comp_contMDiffWithinAt p₀
    (contMDiffWithinAt_pi_space.mpr hAc)).clm_apply hT.2
  let e := trivializationAt F₂ V₂ (b p₀)
  have hx : b p₀ ∈ e.baseSet := mem_baseSet_trivializationAt F₂ V₂ (b p₀)
  apply h.congr_of_eventuallyEq
  · filter_upwards [hT.1.continuousWithinAt (e.open_baseSet.mem_nhds hx)] with p hp
    exact multilinear_comp_inCoordinates (b p₀) (b p) hp (T p) (fun i => A i p)
  · exact multilinear_comp_inCoordinates (b p₀) (b p₀) hx (T p₀) (fun i => A i p₀)

theorem ContMDiffAt.multilinear_bundle_comp
    (hT : ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) p₀)
    (hA : ∀ i, ContMDiffAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A i p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) p₀) :
    ContMDiffAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) p₀ :=
  ContMDiffWithinAt.multilinear_bundle_comp hT hA

theorem ContMDiffOn.multilinear_bundle_comp
    (hT : ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) s)
    (hA : ∀ i, ContMDiffOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A i p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s) :
    ContMDiffOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) s :=
  fun p hp => (hT p hp).multilinear_bundle_comp (fun i => hA i p hp)

theorem ContMDiff.multilinear_bundle_comp
    (hT : ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)) n
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))))
    (hA : ∀ i, ContMDiff J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun p => (⟨b p, A i p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) :
    ContMDiff J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)) n
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) :=
  fun p => (hT p).multilinear_bundle_comp (fun i => hA i p)

theorem MDifferentiableWithinAt.multilinear_bundle_comp
    (hT : MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) s p₀)
    (hA : ∀ i, MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A i p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s p₀) :
    MDifferentiableWithinAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) s p₀ := by
  rw [mdifferentiableWithinAt_totalSpace] at hT ⊢
  refine ⟨hT.1, ?_⟩
  have hAc := fun i => ((mdifferentiableWithinAt_hom_bundle _).mp (hA i)).2
  let L := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : Fin k => F₁) (fun _ : Fin k => F₂) 𝕜
  have hpi : MDifferentiableWithinAt J 𝓘(𝕜, Fin k → F₁ →L[𝕜] F₂)
      (fun p i => ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂
        (b p₀) (b p) (b p₀) (b p) (A i p)) s p₀ := by
    simpa only [mdifferentiableWithinAt_iff, continuousWithinAt_pi,
      differentiableWithinAt_pi, forall_and, extChartAt_model_space_eq_id,
      Function.comp_def, PartialEquiv.refl_coe, id] using hAc
  have hL : MDifferentiable 𝓘(𝕜, Fin k → F₁ →L[𝕜] F₂)
      𝓘(𝕜, (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜) →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜) L :=
    mdifferentiable_iff_differentiable.mpr
      ((show ContDiff 𝕜 1 (fun a : Fin k → F₁ →L[𝕜] F₂ => L a) from
        ContinuousMultilinearMap.contDiff (𝕜 := 𝕜) (E := fun _ : Fin k => F₁ →L[𝕜] F₂)
          (F := (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜) →L[𝕜]
            ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜) L).differentiable
        (by norm_num))
  have h := ((hL _).comp_mdifferentiableWithinAt p₀ hpi).clm_apply hT.2
  let e := trivializationAt F₂ V₂ (b p₀)
  have hx : b p₀ ∈ e.baseSet := mem_baseSet_trivializationAt F₂ V₂ (b p₀)
  apply h.congr_of_eventuallyEq
  · filter_upwards [hT.1.continuousWithinAt (e.open_baseSet.mem_nhds hx)] with p hp
    exact multilinear_comp_inCoordinates (b p₀) (b p) hp (T p) (fun i => A i p)
  · exact multilinear_comp_inCoordinates (b p₀) (b p₀) hx (T p₀) (fun i => A i p₀)

theorem MDifferentiableAt.multilinear_bundle_comp
    (hT : MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) p₀)
    (hA : ∀ i, MDifferentiableAt J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A i p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) p₀) :
    MDifferentiableAt J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) p₀ :=
  MDifferentiableWithinAt.multilinear_bundle_comp hT hA

theorem MDifferentiableOn.multilinear_bundle_comp
    (hT : MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))) s)
    (hA : ∀ i, MDifferentiableOn J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A i p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x))) s) :
    MDifferentiableOn J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) s :=
  fun p hp => (hT p hp).multilinear_bundle_comp (fun i => hA i p hp)

theorem MDifferentiable.multilinear_bundle_comp
    (hT : MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜))
      (fun p => (⟨b p, T p⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₂) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₂ V₂))))
    (hA : ∀ i, MDifferentiable J (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun p => (⟨b p, A i p⟩ : TotalSpace (F₁ →L[𝕜] F₂)
        (fun x => V₁ x →L[𝕜] V₂ x)))) :
    MDifferentiable J
      (I.prod 𝓘(𝕜, ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜))
      (fun p => (⟨b p, (T p).compContinuousLinearMap (fun i => A i p)⟩ : TotalSpace
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin k => F₁) 𝕜)
        (Bundle.continuousMultilinearMap 𝕜 k F₁ V₁))) :=
  fun p => (hT p).multilinear_bundle_comp (fun i => hA i p)
