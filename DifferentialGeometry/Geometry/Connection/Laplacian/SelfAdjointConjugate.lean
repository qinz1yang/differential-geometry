import DifferentialGeometry.Geometry.Connection.SelfAdjointConjugate
import DifferentialGeometry.Geometry.Connection.Laplacian.SelfAdjointRestriction

noncomputable section

open Bundle
open DifferentialGeometry.HomConnectionGen
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [FiniteDimensional ℝ F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [FiniteDimensional ℝ F₂]
variable {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, InnerProductSpace ℝ (V₁ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [ContMDiffVectorBundle ∞ F₁ V₁ I] [IsContMDiffRiemannianBundle I ∞ F₁ V₁]
variable {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, InnerProductSpace ℝ (V₂ x)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle ∞ F₂ V₂ I] [IsContMDiffRiemannianBundle I ∞ F₂ V₂]

namespace CovariantDerivative

theorem map_selfAdjoint_hessian_conjugate
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (D : CovariantDerivative I F₁ V₁) (hD : D.IsMetricCompatible)
    (C : CovariantDerivative I F₂ V₂) (hC : C.IsMetricCompatible)
    [ContMDiffCovariantDerivative D ∞] [ContMDiffCovariantDerivative C ∞]
    (hparallel : homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂ D C
      (fun x => (φ x).toContinuousLinearEquiv.toContinuousLinearMap) = 0)
    (base : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
    let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
    letI := S₁.totalSpaceTopology
    letI := S₁.fiberBundle
    letI := S₁.vector_bundle
    letI := S₂.totalSpaceTopology
    letI := S₂.fiberBundle
    letI := S₂.vector_bundle
    ∀ (A : Cₛ^∞⟮I; Fin S₂.rank → ℝ, fun x => S₂.fiber x⟯)
      (x : M) (X Y : TangentSpace I x),
      (φ x).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((D.selfAdjoint hD).hessian base (ContMDiffSection.selfAdjointConjugate φ hφ A) x X Y :
          V₁ x →L[ℝ] V₁ x) =
      ((C.selfAdjoint hC).hessian base A x X Y : V₂ x →L[ℝ] V₂ x).comp
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap := by
  let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
  let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
  let _ := S₁.totalSpaceTopology
  let _ := S₁.fiberBundle
  let _ := S₁.vector_bundle
  let _ := S₁.contMDiffVectorBundle
  let _ := S₂.totalSpaceTopology
  let _ := S₂.fiberBundle
  let _ := S₂.vector_bundle
  let _ := S₂.contMDiffVectorBundle
  dsimp only
  intro A x X Y
  let B := ContMDiffSection.selfAdjointConjugate φ hφ A
  let DS := D.selfAdjoint hD
  let CS := C.selfAdjoint hC
  have hDS := D.contMDiff_selfAdjoint hD
  have hCS := C.contMDiff_selfAdjoint hC
  have hDB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (Fin S₁.rank → ℝ))) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] (Fin S₁.rank → ℝ)) y (DS B y)) :=
    contMDiffOn_univ.mp (hDS.contMDiff.contMDiff (by simpa using B.contMDiff.contMDiffOn))
  have hCA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (Fin S₂.rank → ℝ))) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] (Fin S₂.rank → ℝ)) y (CS A y)) :=
    contMDiffOn_univ.mp (hCS.contMDiff.contMDiff (by simpa using A.contMDiff.contMDiffOn))
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  let η : Cₛ^∞⟮I; Fin S₁.rank → ℝ, fun y => S₁.fiber y⟯ :=
    ⟨fun y => DS B y (Z y), hDB.clm_bundle_apply Z.contMDiff⟩
  let τ : Cₛ^∞⟮I; Fin S₂.rank → ℝ, fun y => S₂.fiber y⟯ :=
    ⟨fun y => CS A y (Z y), hCA.clm_bundle_apply Z.contMDiff⟩
  have hη : η = ContMDiffSection.selfAdjointConjugate φ hφ τ := by
    apply ContMDiffSection.ext
    intro y
    apply Subtype.ext
    exact (ContinuousLinearEquiv.eq_toContinuousLinearMap_symm_comp _ _).mpr
      (map_selfAdjoint_conjugate φ hφ D hD C hC hparallel A y (Z y))
  change (φ x).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (DS.hessian base B x X Y : V₁ x →L[ℝ] V₁ x) =
    (CS.hessian base A x X Y : V₂ x →L[ℝ] V₂ x).comp
      (φ x).toContinuousLinearEquiv.toContinuousLinearMap
  rw [← hZ, DS.hessian_apply base (hDB.mdifferentiableAt (by simp)) Z.mdifferentiableAt,
    CS.hessian_apply base (hCA.mdifferentiableAt (by simp)) Z.mdifferentiableAt,
    Submodule.coe_sub, Submodule.coe_sub,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  change (φ x).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (DS η x X : V₁ x →L[ℝ] V₁ x) -
      (φ x).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (DS B x (base Z x X) : V₁ x →L[ℝ] V₁ x) = _
  rw [hη]
  exact congrArg₂ (· - ·)
    (map_selfAdjoint_conjugate φ hφ D hD C hC hparallel τ x X)
    (map_selfAdjoint_conjugate φ hφ D hD C hC hparallel A x (base Z x X))

end CovariantDerivative

namespace DifferentialGeometry.Geometry.Connection

open CovariantDerivative

theorem map_rawBundleConnLap_selfAdjoint_conjugate
    (φ : ∀ x, V₁ x ≃ₗᵢ[ℝ] V₂ x)
    (hφ : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap))
    (D : CovariantDerivative I F₁ V₁) (hD : D.IsMetricCompatible)
    (C : CovariantDerivative I F₂ V₂) (hC : C.IsMetricCompatible)
    [ContMDiffCovariantDerivative D ∞] [ContMDiffCovariantDerivative C ∞]
    (hparallel : homBundleCovariantDerivativeGen I M F₁ V₁ F₂ V₂ D C
      (fun x => (φ x).toContinuousLinearEquiv.toContinuousLinearMap) = 0)
    (g : SmoothRiemannianMetric I M) :
    let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
    let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
    letI := S₁.totalSpaceTopology
    letI := S₁.fiberBundle
    letI := S₂.totalSpaceTopology
    letI := S₂.fiberBundle
    ∀ (A : Cₛ^∞⟮I; Fin S₂.rank → ℝ, fun x => S₂.fiber x⟯) (x : M),
      (φ x).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (rawBundleConnLap g (D.selfAdjoint hD)
          (ContMDiffSection.selfAdjointConjugate φ hφ A) x : V₁ x →L[ℝ] V₁ x) =
      (rawBundleConnLap g (C.selfAdjoint hC) A x : V₂ x →L[ℝ] V₂ x).comp
        (φ x).toContinuousLinearEquiv.toContinuousLinearMap := by
  let S₁ := selfAdjointSubbundle (I := I) (F := F₁) (V := V₁) (n := ∞)
  let S₂ := selfAdjointSubbundle (I := I) (F := F₂) (V := V₂) (n := ∞)
  let _ := S₁.totalSpaceTopology
  let _ := S₁.fiberBundle
  let _ := S₁.vector_bundle
  let _ := S₁.contMDiffVectorBundle
  let _ := S₂.totalSpaceTopology
  let _ := S₂.fiberBundle
  let _ := S₂.vector_bundle
  let _ := S₂.contMDiffVectorBundle
  dsimp only
  intro A x
  let B := ContMDiffSection.selfAdjointConjugate φ hφ A
  have hDS := D.contMDiff_selfAdjoint hD
  have hCS := C.contMDiff_selfAdjoint hC
  rw [rawBundleConnLap_eq_sum_hessian_of_contMDiffAt g (D.selfAdjoint hD) hDS
      ((B.contMDiff x).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))),
    rawBundleConnLap_eq_sum_hessian_of_contMDiffAt g (C.selfAdjoint hC) hCS
      ((A.contMDiff x).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))),
    Submodule.coe_sum, Submodule.coe_sum]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun L : V₁ x →L[ℝ] V₂ x => L v)
    (map_selfAdjoint_hessian_conjugate φ hφ D hD C hC hparallel (LeviCivita g) A x
      (smoothOrthoFrame g x i x) (smoothOrthoFrame g x i x))

end DifferentialGeometry.Geometry.Connection
