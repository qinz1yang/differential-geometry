import DifferentialGeometry.Geometry.Metric.BundleModelNorm
import Mathlib.Geometry.Manifold.VectorBundle.Hom

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
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [oldVector : VectorBundle ℝ F V]
  {G : Type*} [gNorm : NormedAddCommGroup G] [gSpace : NormedSpace ℝ G]
  {W : B → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle G W] [gVector : VectorBundle ℝ G W]

theorem contMDiffWithinAt_hom_totalSpace_model_metric_iff (D : MetricFiberData F)
    {n : ℕ∞ω} {f : A → TotalSpace (G →L[ℝ] F) (fun x => W x →L[ℝ] V x)}
    {s : Set A} {x : A} :
    (letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology;
      letI : InnerProductSpace ℝ F :=
        @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
          _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                  let : NormedSpace ℝ F := oldSpace
                  infer_instance) _ _ D;
      letI : VectorBundle ℝ F V :=
        @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D;
      ContMDiffWithinAt IA (IB.prod 𝓘(ℝ, G →L[ℝ] F)) n f s x) ↔
    ContMDiffWithinAt IA (IB.prod 𝓘(ℝ, G →L[ℝ] F)) n f s x := by
  let homNorm₀ : NormedAddCommGroup (G →L[ℝ] F) := inferInstance
  let homSpace₀ : NormedSpace ℝ (G →L[ℝ] F) := inferInstance
  have hOld := @contMDiffWithinAt_totalSpace n ℝ B (G →L[ℝ] F) A
    (fun x => W x →L[ℝ] V x) _ homNorm₀ homSpace₀ _ _ EB _ _ HB _ IB EA _ _ HA _ IA
    _ _ _ _ _ f s x
  let newNorm := D.toNormedAddCommGroupOfTopology
  let : SeminormedAddCommGroup F := newNorm.toSeminormedAddCommGroup
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  let : VectorBundle ℝ F V :=
    @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D
  let homNorm₁ : NormedAddCommGroup (G →L[ℝ] F) :=
    @ContinuousLinearMap.toNormedAddCommGroup ℝ ℝ G F _ newNorm _ _ _ newInner.toNormedSpace _ _
  let : SeminormedAddCommGroup (G →L[ℝ] F) := homNorm₁.toSeminormedAddCommGroup
  let homSpace₁ : NormedSpace ℝ (G →L[ℝ] F) := inferInstance
  rw [@contMDiffWithinAt_totalSpace n ℝ B (G →L[ℝ] F) A (fun x => W x →L[ℝ] V x)
      _ homNorm₁ homSpace₁ _ _ EB _ _ HB _ IB EA _ _ HA _ IA _ _ _ _ _ f s x,
    hOld]
  apply and_congr_right
  intro _
  have hfwd := @ContinuousLinearMap.contMDiff ℝ _ (G →L[ℝ] F) homNorm₀ homSpace₀
    (G →L[ℝ] F) homNorm₁ homSpace₁ n (ContinuousLinearMap.id ℝ (G →L[ℝ] F))
  have hbwd := @ContinuousLinearMap.contMDiff ℝ _ (G →L[ℝ] F) homNorm₁ homSpace₁
    (G →L[ℝ] F) homNorm₀ homSpace₀ n (ContinuousLinearMap.id ℝ (G →L[ℝ] F))
  constructor
  · intro hf
    exact @ContMDiffAt.comp_contMDiffWithinAt ℝ _ EA _ _ HA _ IA A _
      (G →L[ℝ] F) homNorm₁ homSpace₁ (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      (G →L[ℝ] F) homNorm₀ homSpace₀ (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      _ _ _ _ s n _ x (hbwd _) hf
  · intro hf
    exact @ContMDiffAt.comp_contMDiffWithinAt ℝ _ EA _ _ HA _ IA A _
      (G →L[ℝ] F) homNorm₀ homSpace₀ (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      (G →L[ℝ] F) homNorm₁ homSpace₁ (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      _ _ _ _ s n _ x (hfwd _) hf

theorem contMDiffWithinAt_hom_totalSpace_model_metric_both_iff [FiniteDimensional ℝ G]
    (D : MetricFiberData F) (Dg : MetricFiberData G)
    {n : ℕ∞ω} {f : A → TotalSpace (G →L[ℝ] F) (fun x => W x →L[ℝ] V x)}
    {s : Set A} {x : A} :
    (letI : NormedAddCommGroup F := D.toNormedAddCommGroupOfTopology;
      letI : InnerProductSpace ℝ F :=
        @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
          _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
                  let : NormedSpace ℝ F := oldSpace
                  infer_instance) _ _ D;
      letI : VectorBundle ℝ F V :=
        @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D;
      letI : NormedAddCommGroup G := Dg.toNormedAddCommGroupOfTopology;
      letI : InnerProductSpace ℝ G :=
        @MetricFiberData.toInnerProductSpaceOfTopology G gNorm.toAddCommGroup gSpace.toModule
          _ _ (by let : SeminormedAddCommGroup G := gNorm.toSeminormedAddCommGroup
                  let : NormedSpace ℝ G := gSpace
                  infer_instance) _ _ Dg;
      letI : VectorBundle ℝ G W :=
        @vector_bundle_model_metric B _ G gNorm gSpace _ W _ _ _ _ gVector Dg;
      ContMDiffWithinAt IA (IB.prod 𝓘(ℝ, G →L[ℝ] F)) n f s x) ↔
    ContMDiffWithinAt IA (IB.prod 𝓘(ℝ, G →L[ℝ] F)) n f s x := by
  let norm₀ : Unit → NormedAddCommGroup (G →L[ℝ] F) := fun _ => inferInstance
  let space₀ : Unit → @NormedSpace ℝ (G →L[ℝ] F) _ (norm₀ ()).toSeminormedAddCommGroup :=
    fun _ => inferInstance
  have hOld := @contMDiffWithinAt_totalSpace n ℝ B (G →L[ℝ] F) A
    (fun x => W x →L[ℝ] V x) _ (norm₀ ()) (space₀ ()) _ _ EB _ _ HB _ IB EA _ _ HA _ IA
    _ _ _ _ _ f s x
  let newNorm := D.toNormedAddCommGroupOfTopology
  let : SeminormedAddCommGroup F := newNorm.toSeminormedAddCommGroup
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ D
  let : VectorBundle ℝ F V :=
    @vector_bundle_model_metric B _ F oldNorm oldSpace _ V _ _ _ _ oldVector D
  let newGNorm := Dg.toNormedAddCommGroupOfTopology
  let : SeminormedAddCommGroup G := newGNorm.toSeminormedAddCommGroup
  let newGInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology G gNorm.toAddCommGroup gSpace.toModule
      _ _ (by let : SeminormedAddCommGroup G := gNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ G := gSpace
              infer_instance) _ _ Dg
  let : VectorBundle ℝ G W :=
    @vector_bundle_model_metric B _ G gNorm gSpace _ W _ _ _ _ gVector Dg
  let norm₁ : NormedAddCommGroup (G →L[ℝ] F) := inferInstance
  let space₁ : NormedSpace ℝ (G →L[ℝ] F) := inferInstance
  rw [@contMDiffWithinAt_totalSpace n ℝ B (G →L[ℝ] F) A (fun x => W x →L[ℝ] V x)
      _ norm₁ space₁ _ _ EB _ _ HB _ IB EA _ _ HA _ IA _ _ _ _ _ f s x, hOld]
  apply and_congr_right
  intro _
  have hfwd := @ContinuousLinearMap.contMDiff ℝ _ (G →L[ℝ] F) (norm₀ ()) (space₀ ())
    (G →L[ℝ] F) norm₁ space₁ n (ContinuousLinearMap.id ℝ (G →L[ℝ] F))
  have hbwd := @ContinuousLinearMap.contMDiff ℝ _ (G →L[ℝ] F) norm₁ space₁
    (G →L[ℝ] F) (norm₀ ()) (space₀ ()) n (ContinuousLinearMap.id ℝ (G →L[ℝ] F))
  constructor
  · intro hf
    exact @ContMDiffAt.comp_contMDiffWithinAt ℝ _ EA _ _ HA _ IA A _
      (G →L[ℝ] F) norm₁ space₁ (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      (G →L[ℝ] F) (norm₀ ()) (space₀ ()) (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      _ _ _ _ s n _ x (hbwd _) hf
  · intro hf
    exact @ContMDiffAt.comp_contMDiffWithinAt ℝ _ EA _ _ HA _ IA A _
      (G →L[ℝ] F) (norm₀ ()) (space₀ ()) (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      (G →L[ℝ] F) norm₁ space₁ (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      _ _ _ _ s n _ x (hfwd _) hf

omit [FiniteDimensional ℝ F] in
theorem contMDiffWithinAt_hom_totalSpace_domain_model_metric_iff [FiniteDimensional ℝ G]
    (D : MetricFiberData G)
    {n : ℕ∞ω} {f : A → TotalSpace (G →L[ℝ] F) (fun x => W x →L[ℝ] V x)}
    {s : Set A} {x : A} :
    (letI : NormedAddCommGroup G := D.toNormedAddCommGroupOfTopology;
      letI : InnerProductSpace ℝ G :=
        @MetricFiberData.toInnerProductSpaceOfTopology G gNorm.toAddCommGroup gSpace.toModule
          _ _ (by let : SeminormedAddCommGroup G := gNorm.toSeminormedAddCommGroup
                  let : NormedSpace ℝ G := gSpace
                  infer_instance) _ _ D;
      letI : VectorBundle ℝ G W :=
        @vector_bundle_model_metric B _ G gNorm gSpace _ W _ _ _ _ gVector D;
      ContMDiffWithinAt IA (IB.prod 𝓘(ℝ, G →L[ℝ] F)) n f s x) ↔
    ContMDiffWithinAt IA (IB.prod 𝓘(ℝ, G →L[ℝ] F)) n f s x := by
  let homNorm₀ : NormedAddCommGroup (G →L[ℝ] F) := inferInstance
  let homSpace₀ : NormedSpace ℝ (G →L[ℝ] F) := inferInstance
  have hOld := @contMDiffWithinAt_totalSpace n ℝ B (G →L[ℝ] F) A
    (fun x => W x →L[ℝ] V x) _ homNorm₀ homSpace₀ _ _ EB _ _ HB _ IB EA _ _ HA _ IA
    _ _ _ _ _ f s x
  let newNorm := D.toNormedAddCommGroupOfTopology
  let : SeminormedAddCommGroup G := newNorm.toSeminormedAddCommGroup
  let newInner :=
    @MetricFiberData.toInnerProductSpaceOfTopology G gNorm.toAddCommGroup gSpace.toModule
      _ _ (by let : SeminormedAddCommGroup G := gNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ G := gSpace
              infer_instance) _ _ D
  let : VectorBundle ℝ G W :=
    @vector_bundle_model_metric B _ G gNorm gSpace _ W _ _ _ _ gVector D
  let homNorm₁ : NormedAddCommGroup (G →L[ℝ] F) :=
    @ContinuousLinearMap.toNormedAddCommGroup ℝ ℝ G F newNorm _ _ _ newInner.toNormedSpace _ _ _
  let : SeminormedAddCommGroup (G →L[ℝ] F) := homNorm₁.toSeminormedAddCommGroup
  let homSpace₁ : NormedSpace ℝ (G →L[ℝ] F) := inferInstance
  rw [@contMDiffWithinAt_totalSpace n ℝ B (G →L[ℝ] F) A (fun x => W x →L[ℝ] V x)
      _ homNorm₁ homSpace₁ _ _ EB _ _ HB _ IB EA _ _ HA _ IA _ _ _ _ _ f s x,
    hOld]
  apply and_congr_right
  intro _
  have hfwd := @ContinuousLinearMap.contMDiff ℝ _ (G →L[ℝ] F) homNorm₀ homSpace₀
    (G →L[ℝ] F) homNorm₁ homSpace₁ n (ContinuousLinearMap.id ℝ (G →L[ℝ] F))
  have hbwd := @ContinuousLinearMap.contMDiff ℝ _ (G →L[ℝ] F) homNorm₁ homSpace₁
    (G →L[ℝ] F) homNorm₀ homSpace₀ n (ContinuousLinearMap.id ℝ (G →L[ℝ] F))
  constructor
  · intro hf
    exact @ContMDiffAt.comp_contMDiffWithinAt ℝ _ EA _ _ HA _ IA A _
      (G →L[ℝ] F) homNorm₁ homSpace₁ (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      (G →L[ℝ] F) homNorm₀ homSpace₀ (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      _ _ _ _ s n _ x (hbwd _) hf
  · intro hf
    exact @ContMDiffAt.comp_contMDiffWithinAt ℝ _ EA _ _ HA _ IA A _
      (G →L[ℝ] F) homNorm₀ homSpace₀ (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      (G →L[ℝ] F) homNorm₁ homSpace₁ (G →L[ℝ] F) _ _ (G →L[ℝ] F) _
      _ _ _ _ s n _ x (hfwd _) hf

end Bundle
