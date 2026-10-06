import DifferentialGeometry.Geometry.Collapse.CutMetricTransport
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Collapse
open GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

theorem inj_of_isInvertible_S25 {E₁ E₂ : Type*} [TopologicalSpace E₁] [AddCommMonoid E₁] [Module ℝ E₁]
    [TopologicalSpace E₂] [AddCommMonoid E₂] [Module ℝ E₂] {f : E₁ →L[ℝ] E₂} (h : f.IsInvertible) :
    Function.Injective f := by
  obtain ⟨A, rfl⟩ := h
  exact A.injective

/-- `cutPieceMap` is an immersion at every point (boundary points included). -/
theorem mfderiv_injective_cutPieceMap_aux_S25 {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (x : D.components.piece i) :
    Function.Injective (mfderiv D.carrier.model (𝓡 3)
      (fun y : D.components.piece i => D.reconstruction.val (D.boundary.quotientMap y.val)) x) := by
  let := D.reconstructionAtlas.charts
  let := D.reconstructionAtlas.smooth
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hval : IsLocalDiffeomorph D.carrier.model D.carrier.model ∞
      (Subtype.val : D.components.piece i → D.carrier.Carrier) :=
    isLocalDiffeomorph_subtype_val (I := D.carrier.model) (D.components.piece i)
  have hvalx : Function.Injective (mfderiv D.carrier.model D.carrier.model
      (Subtype.val : D.components.piece i → D.carrier.Carrier) x) :=
    inj_of_isInvertible_S25 ((hval x).isInvertible_mfderiv hn)
  have hq : MDifferentiableAt D.carrier.model (𝓡 3) D.boundary.quotientMap x.val :=
    (D.reconstructionAtlas.quotient_smooth x.val).mdifferentiableAt hn
  have hv : MDifferentiableAt D.carrier.model D.carrier.model
      (Subtype.val : D.components.piece i → D.carrier.Carrier) x :=
    (contMDiff_subtype_val x).mdifferentiableAt hn
  have hr : MDifferentiableAt (𝓡 3) (𝓡 3) (D.reconstruction.val : D.boundary.Assembled → M.Carrier)
      (D.boundary.quotientMap x.val) :=
    (D.reconstruction.val.contMDiff _).mdifferentiableAt hn
  have hqv : MDifferentiableAt D.carrier.model (𝓡 3)
      (D.boundary.quotientMap ∘ (Subtype.val : D.components.piece i → D.carrier.Carrier)) x :=
    MDifferentiableAt.comp x hq hv
  have hcomp : ∀ v, mfderiv D.carrier.model (𝓡 3)
      (fun y : D.components.piece i => D.reconstruction.val (D.boundary.quotientMap y.val)) x v =
      mfderiv (𝓡 3) (𝓡 3) (D.reconstruction.val : D.boundary.Assembled → M.Carrier)
        (D.boundary.quotientMap x.val)
      (mfderiv D.carrier.model (𝓡 3) D.boundary.quotientMap x.val
        (mfderiv D.carrier.model D.carrier.model
          (Subtype.val : D.components.piece i → D.carrier.Carrier) x v)) := by
    intro v
    have h1 := mfderiv_comp (I := D.carrier.model) (I' := 𝓡 3) (I'' := 𝓡 3) x hr hqv
    have h2 := mfderiv_comp (I := D.carrier.model) (I' := D.carrier.model) (I'' := 𝓡 3) x hq hv
    have h1' := congrArg (fun L => L v) h1
    have h2' := congrArg (fun L => L v) h2
    simp only [ContinuousLinearMap.comp_apply] at h1' h2'
    refine h1'.trans ?_
    rw [h2']
    rfl
  intro a b hab
  obtain ⟨A, hA⟩ := (D.reconstruction.val.isLocalDiffeomorph
    (D.boundary.quotientMap x.val)).isInvertible_mfderiv hn
  have hQ : Function.Injective (mfderiv D.carrier.model (𝓡 3) D.boundary.quotientMap x.val) := by
    obtain ⟨L, hL, -⟩ := D.reconstructionAtlas.quotient_oriented x.val
    intro u v huv
    exact L.injective (by rw [hL, hL]; exact huv)
  rw [hcomp, hcomp] at hab
  have hAe : ∀ w, A w = mfderiv (𝓡 3) (𝓡 3)
      (D.reconstruction.val : D.boundary.Assembled → M.Carrier) (D.boundary.quotientMap x.val) w :=
    fun w => by rw [← hA]; rfl
  apply hvalx
  apply hQ
  exact EquivLike.injective A ((hAe _).trans (hab.trans (hAe _).symm))

theorem mfderiv_injective_cutPieceMap_S25 {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (x : (D.component i).Carrier) :
    Function.Injective (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) x) :=
  mfderiv_injective_cutPieceMap_aux_S25 D i x

/-- The induced piece metric: pullback of `g` along the actual cut map `cutPieceMap D i`. -/
def cutMetric_S25 {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count) :
    SmoothRiemannianMetric (D.component i).model (D.component i).Carrier :=
  g.pullback (cutPieceMap D i) (contMDiff_cutPieceMap D i) (mfderiv_injective_cutPieceMap_S25 D i)

theorem isInducedCutMetric_cutMetric_S25 {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count) :
    isInducedCutMetric g D i (cutMetric_S25 g D i) :=
  fun _ _ _ => rfl

end GC.LongTime.Ch12
