import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowDom
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FamilyIsotopyCores

/-!
# CP1-D7 (2): basic facts used to build the smooth window

* `backwardSurvivorDomain` is `σ`-compact and `backwardSurvivorMap` is an open embedding;
* derivative injectivity transfers along carrier casts and open subsets;
* `restrictDom_CPD6` and `domMap` are smooth.
-/

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

instance secondCountable_carrier_CPD7 (S : OrientedThreeStage.{u}) :
    SecondCountableTopology S.Carrier :=
  ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) S.Carrier

instance sigmaCompact_survivorDomain_CPD7 (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) :
    SigmaCompactSpace (H.backwardSurvivorDomain first last hle) := by
  have : LocallyCompactSpace (H.backwardSurvivorDomain first last hle) :=
    (H.backwardSurvivorDomain first last hle).isOpen.locallyCompactSpace
  infer_instance

theorem isOpenEmbedding_survivorMap_CPD7 (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (j : Fin (H.eventCount + 1))
    (hj : first ≤ j) (hl : j ≤ last) :
    Topology.IsOpenEmbedding (H.backwardSurvivorMap first last hle j hj hl) := by
  have h := H.backwardSurvivorMap_isLocalDiffeomorph first last hle j hj hl
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap h.contMDiff.continuous
    (H.backwardSurvivorMap_injective first last hle j hj hl) h.isOpenMap

theorem contMDiff_survivorMap_CPD7 (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (j : Fin (H.eventCount + 1))
    (hj : first ≤ j) (hl : j ≤ last) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (H.backwardSurvivorMap first last hle j hj hl) :=
  (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j hj hl).contMDiff

/-- the survivor map has injective differential -/
theorem mfderiv_survivorMap_injective_CPD7 (H : ObservedHistory.{u})
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) (j : Fin (H.eventCount + 1))
    (hj : first ≤ j) (hl : j ≤ last) (x : H.backwardSurvivorDomain first last hle) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (H.backwardSurvivorMap first last hle j hj hl) x) :=
  (H.backwardSurvivorMap_isSmoothEmbedding first last hle j hj hl).isImmersion.mfderiv_injective
    (by decide) x


theorem mfderiv_injective_of_subtype_CPD7 {M N : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (D : TopologicalSpace.Opens M) (f : M → N) (y : D)
    (hf : MDifferentiableAt (𝓡 3) (𝓡 3) f y.1)
    (h : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun x : D => f x.1) y)) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y.1) := by
  have hv := (DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := 𝓡 3) D) y
  let e := hv.mfderivToContinuousLinearEquiv (by decide)
  have hcomp : mfderiv (𝓡 3) (𝓡 3) (fun x : D => f x.1) y =
      (mfderiv (𝓡 3) (𝓡 3) f y.1).comp (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : D → M) y) :=
    mfderiv_comp y hf (hv.mdifferentiableAt (by decide))
  intro v1 v2 hv12
  have h1 : (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : D → M) y) (e.symm v1) = v1 := e.apply_symm_apply v1
  have h2 : (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : D → M) y) (e.symm v2) = v2 := e.apply_symm_apply v2
  have := h (a₁ := e.symm v1) (a₂ := e.symm v2) (by
    rw [hcomp]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [h1, h2]; exact hv12)
  rw [← h1, ← h2, this]

theorem mfderiv_injective_carrierHomeo_CPD7 {A B : OrientedThreeStage.{u}} (h : A = B)
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ X] (f : X → A.Carrier) (x : X) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun y => carrierHomeo_CPD2 h (f y)) x) ↔
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) f x) := by
  subst h
  exact Iff.rfl

end GC.LongTime.CuspP1
