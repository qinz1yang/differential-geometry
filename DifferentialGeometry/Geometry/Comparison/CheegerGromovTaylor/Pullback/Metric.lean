import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Geometry.Curvature.Bounds.Pullback
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

open Exponential NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def intrinsicPullBall (R : Real) : Opens E :=
  ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩

noncomputable def intrinsicExpOn
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (R : Real) :
    intrinsicPullBall (E := E) R → M :=
  fun z => intrinsicFramedExp (I := I) g hEnorm p z

theorem intrinsicExpOn_local
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    IsLocalDiffeomorph 𝓘(Real, E) I ∞
      (intrinsicExpOn (I := I) g hEnorm p R) := by
  exact isLocalDiffeomorph_restrict_open (intrinsicPullBall (E := E) R) hloc

theorem intrinsicExpOn_mfderiv
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (R : Real) (z : intrinsicPullBall (E := E) R) (v : E) :
    mfderiv 𝓘(Real, E) I
        (intrinsicExpOn (I := I) g hEnorm p R) z
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm v) =
      mfderiv 𝓘(Real, E) I
        (intrinsicFramedExp (I := I) g hEnorm p) (z : E)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) (z : E)).symm v) := by
  change mfderiv 𝓘(Real, E) I
      (fun y : intrinsicPullBall (E := E) R => intrinsicFramedExp (I := I) g hEnorm p y)
      z _ = _
  rw [mfderiv_restrict_open]
  with_unfolding_all rfl

noncomputable def intrinsicPullMetric
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    SmoothRiemannianMetric 𝓘(Real, E) (intrinsicPullBall (E := E) R) := by
  let _ : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
  exact localPullMetric (I := 𝓘(Real, E)) (J := I) g
    (intrinsicExpOn (I := I) g hEnorm p R)
    (intrinsicExpOn_local (I := I) g hEnorm p hloc)

theorem intrinsicPullMetric_inner
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (z : intrinsicPullBall (E := E) R) (v w : E) :
    (intrinsicPullMetric (I := I) g hEnorm p hloc).inner z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) z).symm v)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) z).symm w) =
      intrinsicFrameMetric (I := I) g hEnorm p z v w := by
  let _ : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
  rw [intrinsicPullMetric, localPullMetric_inner, intrinsicFrameMetric_apply,
    intrinsicExpOn_mfderiv, intrinsicExpOn_mfderiv]
  rfl

theorem intrinsicPull_pathLen
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {γ : Real → intrinsicPullBall (E := E) R} {a b : Real}
    (hγ : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc a b)) :
    letI : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
    letI : RiemannianBundle
        (fun y : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) y) :=
      ⟨(intrinsicPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
    Manifold.pathELength I
        (intrinsicExpOn (I := I) g hEnorm p R ∘ γ) a b =
      Manifold.pathELength 𝓘(Real, E) γ a b := by
  let _ : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
  rw [intrinsicPullMetric]
  exact localPull_pathLen (I := 𝓘(Real, E)) (J := I) g hEnorm
    (intrinsicExpOn (I := I) g hEnorm p R)
    (intrinsicExpOn_local (I := I) g hEnorm p hloc) hγ

theorem intrinsicPull_rm04
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (z : intrinsicPullBall (E := E) R) (X Y Z W : E) :
    letI : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
    Geometry.Curvature.metricRm04StandardAt
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
        (intrinsicPullMetric (I := I) g hEnorm p hloc) z
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm X)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm Y)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm Z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm W) =
      Geometry.Curvature.metricRm04StandardAt (I := I) (M := M) g
        (intrinsicFramedExp (I := I) g hEnorm p (z : E))
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (z : E)
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) (z : E)).symm X))
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (z : E)
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) (z : E)).symm Y))
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (z : E)
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) (z : E)).symm Z))
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (z : E)
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) (z : E)).symm W)) := by
  let _ : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
  rw [intrinsicPullMetric, Geometry.Curvature.metricRm04StandardAt_localPullMetric,
    intrinsicExpOn_mfderiv, intrinsicExpOn_mfderiv, intrinsicExpOn_mfderiv,
    intrinsicExpOn_mfderiv]
  rfl

theorem intrinsicPull_quad_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (z : intrinsicPullBall (E := E) R) {K : Real}
    (hRm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (intrinsicFramedExp (I := I) g hEnorm p (z : E)) 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g
          (intrinsicFramedExp (I := I) g hEnorm p (z : E)))) ≤ K)
    (J V : E) :
    letI : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    let Jz := (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E)) z).symm J
    let Vz := (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E)) z).symm V
    gPull.inner z
        (Geometry.Curvature.riemannOp
          (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
          z Jz Vz Vz)
        Jz ≤
      K * gPull.inner z Jz Jz * gPull.inner z Vz Vz := by
  simpa only [intrinsicPullMetric] using!
    Geometry.Curvature.inner_riemannOp_localPullMetric_le (I := 𝓘(Real, E)) (J := I)
      g (intrinsicExpOn g hEnorm p R) (intrinsicExpOn_local g hEnorm p hloc) z hRm
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm J)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm V)

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry
