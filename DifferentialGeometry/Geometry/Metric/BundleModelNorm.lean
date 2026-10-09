import DifferentialGeometry.Geometry.Metric.MetricFiberData.Topology
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

noncomputable section

open DifferentialGeometry.Tensor0SBundle (MetricFiberData)
open scoped Manifold ContDiff

namespace Bundle

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  {HA : Type*} [TopologicalSpace HA] {IA : ModelWithCorners ℝ EA HA}
  {A : Type*} [TopologicalSpace A] [ChartedSpace HA A]
  {F : Type*} [oldNorm : NormedAddCommGroup F] [oldSpace : NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

section VectorBundle

variable {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [oldVector : VectorBundle ℝ F V]

theorem vector_bundle_model_metric (D : MetricFiberData F) :
    letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology
    letI : InnerProductSpace ℝ F :=
      @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
        _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                let : NormedSpace ℝ F := oldSpace
                infer_instance) _ _ D
    VectorBundle ℝ F V := by
  let newNorm : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology
  let : SeminormedAddCommGroup F := newNorm.toSeminormedAddCommGroup
  let : InnerProductSpace ℝ F :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  refine ⟨?_, ?_⟩
  · exact oldVector.trivialization_linear'
  · exact oldVector.continuousOn_coordChange'

theorem contMDiffVectorBundle_model_metric {n : ℕ∞ω}
    [oldSmooth : ContMDiffVectorBundle n F V IB] (D : MetricFiberData F) :
    letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology
    letI : InnerProductSpace ℝ F :=
      @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
        _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                let : NormedSpace ℝ F := oldSpace
                infer_instance) _ _ D
    letI : VectorBundle ℝ F V :=
      @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D
    ContMDiffVectorBundle n F V IB := by
  let endNorm₀ : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
  let endSpace₀ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
  let newNorm : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology
  let : SeminormedAddCommGroup F := newNorm.toSeminormedAddCommGroup
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  let : VectorBundle ℝ F V :=
    @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D
  let endNorm₁ : NormedAddCommGroup (F →L[ℝ] F) :=
    @ContinuousLinearMap.toNormedAddCommGroup ℝ ℝ F F
      newNorm newNorm _ _ newInner.toNormedSpace newInner.toNormedSpace _ _
  let : SeminormedAddCommGroup (F →L[ℝ] F) := endNorm₁.toSeminormedAddCommGroup
  let endSpace₁ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
  refine ⟨?_⟩
  intro e e' _ _
  have hend := @ContinuousLinearMap.contMDiff ℝ _
    (F →L[ℝ] F) endNorm₀ endSpace₀ (F →L[ℝ] F) endNorm₁ endSpace₁ n
    (ContinuousLinearMap.id ℝ (F →L[ℝ] F))
  exact @ContMDiff.comp_contMDiffOn ℝ _ EB _ _ HB _ IB B _
    (F →L[ℝ] F) endNorm₀ endSpace₀ (F →L[ℝ] F) _ _ (F →L[ℝ] F) _
    (F →L[ℝ] F) endNorm₁ endSpace₁ (F →L[ℝ] F) _ _ (F →L[ℝ] F) _
    _ _ _ n _ _ _ hend (oldSmooth.contMDiffOn_coordChangeL e e')

end VectorBundle

theorem contMDiffWithinAt_model_metric_iff (D : MetricFiberData F)
    {n : ℕ∞ω} {f : B → F} {s : Set B} {x : B} :
    (letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology;
      letI : InnerProductSpace ℝ F :=
        @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
          _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                  let : NormedSpace ℝ F := oldSpace
                  infer_instance) _ _ D;
      ContMDiffWithinAt IB 𝓘(ℝ, F) n f s x) ↔
    ContMDiffWithinAt IB 𝓘(ℝ, F) n f s x := by
  let newNorm := D.toNormedAddCommGroupOfTopology
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  have hfwd := @ContinuousLinearMap.contMDiff ℝ _ F oldNorm oldSpace F newNorm
    newInner.toNormedSpace n (ContinuousLinearMap.id ℝ F)
  have hbwd := @ContinuousLinearMap.contMDiff ℝ _ F newNorm newInner.toNormedSpace F oldNorm
    oldSpace n (ContinuousLinearMap.id ℝ F)
  constructor
  · intro hf
    exact @ContMDiffAt.comp_contMDiffWithinAt ℝ _ EB _ _ HB _ IB B _
      F newNorm newInner.toNormedSpace F _ _ F _ F oldNorm oldSpace F _ _ F _
      _ _ _ f s n _ x (hbwd (f x)) hf
  · intro hf
    exact @ContMDiffAt.comp_contMDiffWithinAt ℝ _ EB _ _ HB _ IB B _
      F oldNorm oldSpace F _ _ F _ F newNorm newInner.toNormedSpace F _ _ F _
      _ _ _ f s n _ x (hfwd (f x)) hf

theorem mdifferentiableAt_model_metric_iff (D : MetricFiberData F)
    {f : B → F} {x : B} :
    (letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology;
      letI : InnerProductSpace ℝ F :=
        @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
          _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                  let : NormedSpace ℝ F := oldSpace
                  infer_instance) _ _ D;
      MDifferentiableAt IB 𝓘(ℝ, F) f x) ↔
    MDifferentiableAt IB 𝓘(ℝ, F) f x := by
  let newNorm := D.toNormedAddCommGroupOfTopology
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  have hfwd := @ContinuousLinearMap.mdifferentiableAt ℝ _ F oldNorm oldSpace F newNorm
    newInner.toNormedSpace (ContinuousLinearMap.id ℝ F) (f x)
  have hbwd := @ContinuousLinearMap.mdifferentiableAt ℝ _ F newNorm newInner.toNormedSpace F oldNorm
    oldSpace (ContinuousLinearMap.id ℝ F) (f x)
  constructor
  · intro hf
    exact @MDifferentiableAt.comp ℝ _ EB _ _ HB _ IB B _ _
      F newNorm newInner.toNormedSpace F _ _ F _ _ F oldNorm oldSpace F _ _ F _ _
      f x _ hbwd hf
  · intro hf
    exact @MDifferentiableAt.comp ℝ _ EB _ _ HB _ IB B _ _
      F oldNorm oldSpace F _ _ F _ _ F newNorm newInner.toNormedSpace F _ _ F _ _
      f x _ hfwd hf

section TotalSpace

variable {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

theorem contMDiffWithinAt_totalSpace_model_metric_iff (D : MetricFiberData F)
    {n : ℕ∞ω} {f : A → TotalSpace F V} {s : Set A} {x : A} :
    (letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology;
      letI : InnerProductSpace ℝ F :=
        @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
          _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                  let : NormedSpace ℝ F := oldSpace
                  infer_instance) _ _ D;
      ContMDiffWithinAt IA (IB.prod 𝓘(ℝ, F)) n f s x) ↔
    ContMDiffWithinAt IA (IB.prod 𝓘(ℝ, F)) n f s x := by
  let newNorm := D.toNormedAddCommGroupOfTopology
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  rw [@contMDiffWithinAt_totalSpace n ℝ B F A V _ newNorm newInner.toNormedSpace
      _ _ EB _ _ HB _ IB EA _ _ HA _ IA _ _ _ _ _ f s x,
    @contMDiffWithinAt_totalSpace n ℝ B F A V _ oldNorm oldSpace
      _ _ EB _ _ HB _ IB EA _ _ HA _ IA _ _ _ _ _ f s x]
  exact and_congr_right fun _ => @contMDiffWithinAt_model_metric_iff EA _ _ HA _ IA A _ _
    F oldNorm oldSpace _ D n _ s x

theorem mdifferentiableAt_totalSpace_model_metric_iff (D : MetricFiberData F)
    {f : A → TotalSpace F V} {x : A} :
    (letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology;
      letI : InnerProductSpace ℝ F :=
        @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
          _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                  let : NormedSpace ℝ F := oldSpace
                  infer_instance) _ _ D;
      MDifferentiableAt IA (IB.prod 𝓘(ℝ, F)) f x) ↔
    MDifferentiableAt IA (IB.prod 𝓘(ℝ, F)) f x := by
  let newNorm := D.toNormedAddCommGroupOfTopology
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  rw [@mdifferentiableAt_totalSpace ℝ B F A V _ newNorm newInner.toNormedSpace
      _ _ EB _ _ HB _ IB EA _ _ HA _ IA _ _ _ _ _ f x,
    @mdifferentiableAt_totalSpace ℝ B F A V _ oldNorm oldSpace
      _ _ EB _ _ HB _ IB EA _ _ HA _ IA _ _ _ _ _ f x]
  exact and_congr_right fun _ => @mdifferentiableAt_model_metric_iff EA _ _ HA _ IA A _ _
    F oldNorm oldSpace _ D _ x

end TotalSpace

variable {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [oldVector : VectorBundle ℝ F V]

theorem isContMDiffRiemannianBundle_model_metric (D : MetricFiberData F)
    {n : ℕ∞ω} [hc : IsContMDiffRiemannianBundle IB n F V] :
    letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology
    letI : InnerProductSpace ℝ F :=
      @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
        _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                let : NormedSpace ℝ F := oldSpace
                infer_instance) _ _ D
    letI : VectorBundle ℝ F V :=
      @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D
    IsContMDiffRiemannianBundle IB n F V := by
  obtain ⟨g, hg, hinner⟩ := hc.exists_contMDiff
  let norm₀ : Unit → NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := fun _ => inferInstance
  let space₀ : Unit → @NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) _ (norm₀ ()).toSeminormedAddCommGroup :=
    fun _ => inferInstance
  have hOld := fun x => (@contMDiffWithinAt_totalSpace n ℝ B (F →L[ℝ] F →L[ℝ] ℝ) B
    (fun x => V x →L[ℝ] V x →L[ℝ] ℝ) _ (norm₀ ()) (space₀ ()) _ _
    EB _ _ HB _ IB EB _ _ HB _ IB _ _ _ _ _ _ Set.univ x).mp
    ((hg x).contMDiffWithinAt (s := Set.univ))
  let newNorm := D.toNormedAddCommGroupOfTopology
  let : SeminormedAddCommGroup F := newNorm.toSeminormedAddCommGroup
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  let : VectorBundle ℝ F V :=
    @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D
  let norm₁ : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
  let space₁ : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
  refine ⟨g, ?_, hinner⟩
  intro x
  rw [← contMDiffWithinAt_univ]
  apply (@contMDiffWithinAt_totalSpace n ℝ B (F →L[ℝ] F →L[ℝ] ℝ) B
    (fun x => V x →L[ℝ] V x →L[ℝ] ℝ) _ norm₁ space₁ _ _
    EB _ _ HB _ IB EB _ _ HB _ IB _ _ _ _ _ _ Set.univ x).mpr
  refine ⟨(hOld x).1, ?_⟩
  have hid := @ContinuousLinearMap.contMDiff ℝ _ (F →L[ℝ] F →L[ℝ] ℝ) (norm₀ ()) (space₀ ())
    (F →L[ℝ] F →L[ℝ] ℝ) norm₁ space₁ n (ContinuousLinearMap.id ℝ (F →L[ℝ] F →L[ℝ] ℝ))
  exact @ContMDiffAt.comp_contMDiffWithinAt ℝ _ EB _ _ HB _ IB B _
    (F →L[ℝ] F →L[ℝ] ℝ) (norm₀ ()) (space₀ ()) (F →L[ℝ] F →L[ℝ] ℝ) _ _ (F →L[ℝ] F →L[ℝ] ℝ) _
    (F →L[ℝ] F →L[ℝ] ℝ) norm₁ space₁ (F →L[ℝ] F →L[ℝ] ℝ) _ _ (F →L[ℝ] F →L[ℝ] ℝ) _
    _ _ _ _ Set.univ n _ x (hid _) (hOld x).2

end Bundle
