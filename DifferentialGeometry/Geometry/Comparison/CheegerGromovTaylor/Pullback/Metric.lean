import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator
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
  let _ : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
  have hF :
      MDifferentiableAt 𝓘(Real, E) I
        (intrinsicFramedExp (I := I) g hEnorm p) (z : E) :=
    (intrinsicFrame_smooth (I := I) g hEnorm p).mdifferentiableAt (by decide)
  have hval :
      MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E)
        (Subtype.val : intrinsicPullBall (E := E) R → E) z :=
    ((contMDiff_subtype_val (I := 𝓘(Real, E))).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  change mfderiv 𝓘(Real, E) I
      ((intrinsicFramedExp (I := I) g hEnorm p) ∘
        (Subtype.val : intrinsicPullBall (E := E) R → E)) z
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm v) = _
  rw [mfderiv_comp_apply z hF hval, mfderiv_subtype_val_apply]
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
  rw [intrinsicPullMetric, Integral.Connection.rm04_localPull,
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
  let _ : SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let Jz : TangentSpace 𝓘(Real, E) z :=
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm J
  let Vz : TangentSpace 𝓘(Real, E) z :=
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z).symm V
  let F : E → M := intrinsicFramedExp (I := I) g hEnorm p
  let q : M := F (z : E)
  let dJ : TangentSpace I q :=
    mfderiv 𝓘(Real, E) I F (z : E)
      ((tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) (z : E)).symm J)
  let dV : TangentSpace I q :=
    mfderiv 𝓘(Real, E) I F (z : E)
      ((tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) (z : E)).symm V)
  have hRm' :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g q)) ≤ K := by
    simpa only [F, q] using hRm
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g q
  have hquad :=
    DifferentialGeometry.Geometry.Curvature.riemann_quad_le (I := I) g basis hON
      hRm' dJ dV
  have hJJ : gPull.inner z Jz Jz = g.inner q dJ dJ := by
    simp only [gPull, Jz, F, q, dJ]
    rw [intrinsicPullMetric_inner, intrinsicFrameMetric_apply]
    with_unfolding_all rfl
  have hVV : gPull.inner z Vz Vz = g.inner q dV dV := by
    simp only [gPull, Vz, F, q, dV]
    rw [intrinsicPullMetric_inner, intrinsicFrameMetric_apply]
    with_unfolding_all rfl
  calc
    gPull.inner z
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
            z Jz Vz Vz)
          Jz =
        gPull.inner z Jz
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
            z Jz Vz Vz) := gPull.symm _ _ _
    _ = Geometry.Curvature.metricRm04StandardAt
          (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
          gPull z Jz Vz Vz Jz := by
      rw [DifferentialGeometry.Geometry.Curvature.rm04_eq_inner]
    _ = Geometry.Curvature.metricRm04StandardAt
          (I := I) (M := M) g q dJ dV dV dJ := by
      simpa only [gPull, Jz, Vz, F, q, dJ, dV] using
        intrinsicPull_rm04 (I := I) g hEnorm p hloc z J V V J
    _ = g.inner q dJ
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := I) g)
            q dJ dV dV) := by
      rw [DifferentialGeometry.Geometry.Curvature.rm04_eq_inner]
    _ = g.inner q
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := I) g)
            q dJ dV dV)
          dJ := g.symm _ _ _
    _ ≤ K * g.inner q dJ dJ * g.inner q dV dV :=
      hquad
    _ = K * gPull.inner z Jz Jz * gPull.inner z Vz Vz := by
      rw [hJJ, hVV]

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry
