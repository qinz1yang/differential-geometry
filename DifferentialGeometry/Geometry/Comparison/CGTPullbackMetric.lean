import DifferentialGeometry.Geometry.Exponential.IntrinsicFramedCoordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphOpen
import DifferentialGeometry.Geometry.Curvature.Rm04OperatorBound
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityLocalCross
import DifferentialGeometry.Geometry.Metric.LocalPullback
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

open Bundle Manifold Metric Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CGT

open Exponential NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def intrPullBall (R : Real) : Opens E :=
  ⟨Metric.ball (0 : E) R, Metric.isOpen_ball⟩

noncomputable def intrExpOn
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (R : Real) :
    intrPullBall (E := E) R → M :=
  fun z => intrinsicFramedExp (I := I) g hEnorm p z

theorem intrExpOn_local
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    IsLocalDiffeomorph 𝓘(Real, E) I ∞
      (intrExpOn (I := I) g hEnorm p R) := by
  exact isLocalDiffeomorph_restrict_open (intrPullBall (E := E) R) hloc

theorem intrExpOn_mfderiv
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (R : Real) (z : intrPullBall (E := E) R) (v : E) :
    mfderiv 𝓘(Real, E) I
        (intrExpOn (I := I) g hEnorm p R) z v =
      mfderiv 𝓘(Real, E) I
        (intrinsicFramedExp (I := I) g hEnorm p) (z : E) v := by
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  have hF :
      MDifferentiableAt 𝓘(Real, E) I
        (intrinsicFramedExp (I := I) g hEnorm p) (z : E) :=
    (intrFrame_smooth (I := I) g hEnorm p).mdifferentiableAt (by decide)
  have hval :
      MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E)
        (Subtype.val : intrPullBall (E := E) R → E) z :=
    ((contMDiff_subtype_val (I := 𝓘(Real, E))).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  change mfderiv 𝓘(Real, E) I
      ((intrinsicFramedExp (I := I) g hEnorm p) ∘
        (Subtype.val : intrPullBall (E := E) R → E)) z v = _
  rw [mfderiv_comp_apply z hF hval v, mfderiv_subtype_val_apply]

noncomputable def intrPullMetric
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R)) :
    SmoothRiemannianMetric 𝓘(Real, E) (intrPullBall (E := E) R) := by
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  exact localPullMetric (I := 𝓘(Real, E)) (J := I) g
    (intrExpOn (I := I) g hEnorm p R)
    (intrExpOn_local (I := I) g hEnorm p hloc)

theorem intrPullMetric_inner
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (z : intrPullBall (E := E) R) (v w : E) :
    (intrPullMetric (I := I) g hEnorm p hloc).inner z v w =
      intrFrameMetric (I := I) g hEnorm p z v w := by
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  rw [intrPullMetric, localPullMetric_inner, intrFrameMetric_apply,
    intrExpOn_mfderiv, intrExpOn_mfderiv]
  rfl

theorem intrPull_pathLen
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    {γ : Real → intrPullBall (E := E) R} {a b : Real}
    (hγ : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc a b)) :
    letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
    letI : RiemannianBundle
        (fun y : intrPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) y) :=
      ⟨(intrPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
    Manifold.pathELength I
        (intrExpOn (I := I) g hEnorm p R ∘ γ) a b =
      Manifold.pathELength 𝓘(Real, E) γ a b := by
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  rw [intrPullMetric]
  exact localPull_pathLen (I := 𝓘(Real, E)) (J := I) g hEnorm
    (intrExpOn (I := I) g hEnorm p R)
    (intrExpOn_local (I := I) g hEnorm p hloc) hγ

theorem intrPull_rm04
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (z : intrPullBall (E := E) R) (X Y Z W : E) :
    letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
    Geometry.Curvature.metricRm04StdAt
        (I := 𝓘(Real, E)) (M := intrPullBall (E := E) R)
        (intrPullMetric (I := I) g hEnorm p hloc) z X Y Z W =
      Geometry.Curvature.metricRm04StdAt (I := I) (M := M) g
        (intrinsicFramedExp (I := I) g hEnorm p (z : E))
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (z : E) X)
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (z : E) Y)
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (z : E) Z)
        (mfderiv 𝓘(Real, E) I
          (intrinsicFramedExp (I := I) g hEnorm p) (z : E) W) := by
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  rw [intrPullMetric, Integral.Connection.rm04_localPull,
    intrExpOn_mfderiv, intrExpOn_mfderiv, intrExpOn_mfderiv,
    intrExpOn_mfderiv]
  rfl

theorem intrPull_quad_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : Real}
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (z : intrPullBall (E := E) R) {K : Real}
    (hRm :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
        (intrinsicFramedExp (I := I) g hEnorm p (z : E)) 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g
          (intrinsicFramedExp (I := I) g hEnorm p (z : E)))) ≤ K)
    (J V : E) :
    letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
      isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen
          𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
    let gPull := intrPullMetric (I := I) g hEnorm p hloc
    gPull.inner z
        (Geometry.Curvature.riemannOp
          (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
          z J V V)
        J ≤
      K * gPull.inner z J J * gPull.inner z V V := by
  letI : SigmaCompactSpace (intrPullBall (E := E) R) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen
        𝓘(Real, E) (intrPullBall (E := E) R).isOpen)
  let gPull := intrPullMetric (I := I) g hEnorm p hloc
  let F : E → M := intrinsicFramedExp (I := I) g hEnorm p
  let q : M := F (z : E)
  let dJ : TangentSpace I q :=
    mfderiv 𝓘(Real, E) I F (z : E) J
  let dV : TangentSpace I q :=
    mfderiv 𝓘(Real, E) I F (z : E) V
  have hRm' :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) g q 4
        (Geometry.Curvature.metricRm04At
          (I := I) (M := M) g q)) ≤ K := by
    simpa only [F, q] using hRm
  obtain ⟨basis, hON⟩ :=
    Geometry.Curvature.exists_gOrthonormalBasis (I := I) g q
  have hquad :=
    Integral.Connection.riemann_quad_le (I := I) g basis hON
      hRm' dJ dV
  have hJJ : gPull.inner z J J = g.inner q dJ dJ := by
    simp only [gPull, F, q, dJ]
    rw [intrPullMetric_inner, intrFrameMetric_apply]
  have hVV : gPull.inner z V V = g.inner q dV dV := by
    simp only [gPull, F, q, dV]
    rw [intrPullMetric_inner, intrFrameMetric_apply]
  calc
    gPull.inner z
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
            z J V V)
          J =
        gPull.inner z J
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := 𝓘(Real, E)) gPull)
            z J V V) := gPull.symm _ _ _
    _ = Geometry.Curvature.metricRm04StdAt
          (I := 𝓘(Real, E)) (M := intrPullBall (E := E) R)
          gPull z J V V J := by
      rw [Integral.Connection.rm04_eq_inner]
    _ = Geometry.Curvature.metricRm04StdAt
          (I := I) (M := M) g q dJ dV dV dJ := by
      simpa only [gPull, F, q, dJ, dV] using
        intrPull_rm04 (I := I) g hEnorm p hloc z J V V J
    _ = g.inner q dJ
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := I) g)
            q dJ dV dV) := by
      rw [Integral.Connection.rm04_eq_inner]
    _ = g.inner q
          (Geometry.Curvature.riemannOp
            (Geometry.Connection.LeviCivita (I := I) g)
            q dJ dV dV)
          dJ := g.symm _ _ _
    _ ≤ K * g.inner q dJ dJ * g.inner q dV dV :=
      hquad
    _ = K * gPull.inner z J J * gPull.inner z V V := by
      rw [hJJ, hVV]

end CGT
end Riemannian
end Geometry
end DifferentialGeometry
