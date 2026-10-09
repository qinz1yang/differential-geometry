import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CoreInclusionRestriction
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem not_boundaryless_euclideanHalfSpace (n : ℕ) [NeZero n] : ¬ (𝓡∂ n).Boundaryless := by
  intro h
  have hmem : EuclideanSpace.single (0 : Fin n) (-1 : ℝ) ∈ Set.range (𝓡∂ n) := by
    rw [ModelWithCorners.range_eq_univ]
    exact Set.mem_univ _
  rw [range_modelWithCornersEuclideanHalfSpace, Set.mem_ofPred_eq] at hmem
  rw [PiLp.single_apply] at hmem
  norm_num at hmem

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
    [TopologicalSpace D] [TopologicalSpace N]

theorem retainedCore_isOpen (E : CutCapTopology M Q D N) : IsOpen E.retainedCore := by
  have hset : E.retainedCore =
      E.capping.coreInclusion ⁻¹' (E.presentation ⁻¹' Set.range (Sum.inl : Q → Q ⊕ D)) := by
    ext x
    simp only [CutCapTopology.retainedCore, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_range]
    constructor <;> rintro ⟨q, hq⟩ <;> exact ⟨q, hq.symm⟩
  rw [hset]
  exact (isOpen_range_inl.preimage E.presentation.continuous).preimage
    E.capping.coreInclusion.continuous

end CutCapTopology

def IsOpenCoreSubmanifold {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (old : Type u) [oldTop : TopologicalSpace old]
    [oldCharts : ChartedSpace (EuclideanHalfSpace 3) old]
    (ι : old → X.trace.tubes.core) : Prop :=
  letI : TopologicalSpace old := oldTop
  letI : ChartedSpace (EuclideanHalfSpace 3) old := oldCharts
  letI : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
  ∃ U : TopologicalSpace.Opens X.trace.tubes.core,
    ∃ Ψ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) old U ∞,
      ∀ x : old, (Ψ x : X.trace.tubes.core) = ι x

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

abbrev coreOpensCharts (X : SmoothCutCapTransition P Q D N)
    (U : TopologicalSpace.Opens X.trace.tubes.core) :
    ChartedSpace (EuclideanHalfSpace 3) ↥U :=
  @TopologicalSpace.Opens.instChartedSpace (EuclideanHalfSpace 3)
    (↥X.trace.tubes.core) _ _ X.coreCharts U

theorem coreInclusion_isSmoothEmbedding_of_isOpenCoreSubmanifold
    (X : SmoothCutCapTransition P Q D N) {old : Type u} [oldTop : TopologicalSpace old]
    [oldCharts : ChartedSpace (EuclideanHalfSpace 3) old]
    [oldSmooth : IsManifold (𝓡∂ 3) ∞ old]
    (ι : old → X.trace.tubes.core) (h : IsOpenCoreSubmanifold X old ι) :
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (fun x : old => X.trace.capping.coreInclusion (ι x)) := by
  obtain ⟨U, Ψ, hΨ⟩ := h
  exact X.coreInclusion_isSmoothEmbedding_of_diffeomorph (old := old) ι U Ψ hΨ

theorem isOpenCoreSubmanifold_of_opens (X : SmoothCutCapTransition P Q D N)
    (U : TopologicalSpace.Opens X.trace.tubes.core) :
    IsOpenCoreSubmanifold (X := X) (old := ↥U) (oldTop := inferInstance)
      (oldCharts := X.coreOpensCharts U) (Subtype.val) := by
  let coreCharts : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
  exact ⟨U, Diffeomorph.refl (𝓡∂ 3) ↥U ∞, fun _ => rfl⟩

theorem isOpenCoreSubmanifold_retainedCore (X : SmoothCutCapTransition P Q D N) :
    IsOpenCoreSubmanifold (X := X)
      (old := ↥(⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩ :
        TopologicalSpace.Opens X.trace.tubes.core))
      (oldTop := inferInstance)
      (oldCharts := X.coreOpensCharts
        ⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩) (Subtype.val) :=
  X.isOpenCoreSubmanifold_of_opens ⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩

theorem coreInclusion_isSmoothEmbedding_retainedCore (X : SmoothCutCapTransition P Q D N) :
    letI : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (fun x : (↥(⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩ :
          TopologicalSpace.Opens X.trace.tubes.core)) =>
        X.trace.capping.coreInclusion x.1) := by
  let coreCharts : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
  let coreSmooth : IsManifold (𝓡∂ 3) ∞ X.trace.tubes.core := X.coreSmooth
  exact X.coreInclusion_isSmoothEmbedding_of_isOpenCoreSubmanifold
    (old := ↥(⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩ :
      TopologicalSpace.Opens X.trace.tubes.core))
    (oldCharts := X.coreOpensCharts ⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩)
    Subtype.val X.isOpenCoreSubmanifold_retainedCore

end SmoothCutCapTransition

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

def coreCompatibility (E : MetricCutCapEvent P Q a s) : Prop :=
  IsOpenCoreSubmanifold (X := E.transition) (old := E.old) (oldTop := inferInstance)
    (oldCharts := E.oldCharts) (fun x : E.old => x.1)

variable (E : MetricCutCapEvent P Q a s)

theorem isEmbedding_coreInclusion_old :
    Topology.IsEmbedding
      (fun x : E.old => E.transition.trace.capping.coreInclusion x.1) :=
  E.transition.trace.capping.coreEmbedding.comp Topology.IsEmbedding.subtypeVal

theorem coreInclusion_isSmoothEmbedding_of_coreCompatibility (h : E.coreCompatibility) :
    letI : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (fun x : E.old => E.transition.trace.capping.coreInclusion x.1) := by
  let oldCharts : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let oldSmooth : IsManifold (𝓡∂ 3) ∞ E.old := E.oldSmooth
  exact E.transition.coreInclusion_isSmoothEmbedding_of_isOpenCoreSubmanifold
    (old := E.old) (oldCharts := E.oldCharts) (oldSmooth := E.oldSmooth)
    (fun x : E.old => x.1) h

theorem isOpen_old_of_coreCompatibility (h : E.coreCompatibility) :
    IsOpen (E.old : Set E.transition.trace.tubes.core) := by
  let oldCharts : ChartedSpace (EuclideanHalfSpace 3) E.old := E.oldCharts
  let coreCharts : ChartedSpace (EuclideanHalfSpace 3)
    E.transition.trace.tubes.core := E.transition.coreCharts
  obtain ⟨U, Ψ, hΨ⟩ := h
  have hrange : Set.range (fun x : E.old => (x.1 : E.transition.trace.tubes.core)) =
      (U : Set E.transition.trace.tubes.core) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact hΨ x ▸ (Ψ x).2
    · intro hy
      obtain ⟨x, hx⟩ := Ψ.surjective ⟨y, hy⟩
      refine ⟨x, ?_⟩
      have h1 : ((Ψ x : ↥U) : E.transition.trace.tubes.core) = y := congrArg Subtype.val hx
      rwa [hΨ x] at h1
  have hold : (E.old : Set E.transition.trace.tubes.core) =
      Set.range (fun x : E.old => (x.1 : E.transition.trace.tubes.core)) := by
    rw [Subtype.range_val]
  rw [hold, hrange]
  exact U.2

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
