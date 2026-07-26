import DifferentialGeometry.Geometry.Metric.Sphere.KillingHopf
import DifferentialGeometry.Geometry.Metric.Sphere.RoundInputs
import DifferentialGeometry.Geometry.Topology.FiberBundleT2
import DifferentialGeometry.Geometry.Topology.SemilocallySimplyConnected
import DifferentialGeometry.Geometry.Topology.UniversalCover.CompletenessPullback
import DifferentialGeometry.Geometry.Topology.UniversalCover.CurvaturePullback

set_option autoImplicit false

/-!
# Positive-curvature universal covers

This module applies the positive Killing--Hopf theorem to the normalized
lifted metric on a universal cover.  It packages the metric-instance and
completeness setup while retaining the differential isometry equation needed
for the deck-action quotient.
-/

noncomputable section

open Bundle Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry
namespace Geometry

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A]
variable {n : ℕ} [Fact (Module.finrank ℝ A = n + 1)] [NeZero n]

universe u

variable {Q : Type u} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
  [IsManifold (𝓡 n) ∞ Q]
  [T2Space Q] [SigmaCompactSpace Q]
  [CompactSpace Q] [ConnectedSpace Q] [Inhabited Q]
  [LocPathConnectedSpace Q]
  [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace Q]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The normalized universal cover of a compact connected positive
constant-curvature manifold is globally isometric to the round sphere. -/
theorem sphereCover_one
    (hn : 1 < n)
    (g : SmoothRiemannianMetric (𝓡 n) Q)
    (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : Q, ∀ X Y : TangentSpace (𝓡 n) x,
      DifferentialGeometry.Integral.Connection.metricRm04StdAt
          (I := 𝓡 n) (M := Q) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y))
    (p q : sphere (0 : A) 1) (hpq : p ≠ q) (hqneg : q ≠ -p) :
    ∃ d : Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : A) 1)
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) ∞,
      ∀ (x : sphere (0 : A) 1)
        (Y Z : TangentSpace (𝓡 n) x),
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
            (I := 𝓡 n)
            (DifferentialGeometry.scaleMetric
              (I := 𝓡 n) c hc g)).inner (d x)
            (mfderiv (𝓡 n) (𝓡 n)
              (d : sphere (0 : A) 1 →
                DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
              x Y)
            (mfderiv (𝓡 n) (𝓡 n)
              (d : sphere (0 : A) 1 →
                DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
              x Z) =
          (roundMetric (E := A) (n := n)).inner x Y Z := by
  classical
  let g₁ : SmoothRiemannianMetric (𝓡 n) Q :=
    DifferentialGeometry.scaleMetric
      (I := 𝓡 n) c hc g
  haveI : LocallyCompactSpace Q :=
    Manifold.locallyCompact_of_finiteDimensional (M := Q) (𝓡 n)
  letI : RiemannianBundle
      (fun x : Q => TangentSpace (𝓡 n) x) :=
    ⟨g₁.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : Q => TangentSpace (𝓡 n) x) :=
    ⟨g₁.inner, g₁.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI : PseudoEMetricSpace Q :=
    PseudoEMetricSpace.ofRiemannianMetric (𝓡 n) Q
  letI : IsRiemannianManifold (𝓡 n) Q :=
    ⟨fun _ _ => rfl⟩
  letI : CompleteSpace Q := inferInstance
  let gUC :
      SmoothRiemannianMetric (𝓡 n)
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.liftedMetric
      (I := 𝓡 n) g₁
  haveI :
      RegularSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_regularSpace
      (𝓡 n)
  letI : RiemannianBundle
      (fun x :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q =>
        TangentSpace (𝓡 n) x) :=
    ⟨gUC.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q =>
        TangentSpace (𝓡 n) x) :=
    ⟨gUC.inner, gUC.contMDiff.continuous, fun _ _ _ => rfl⟩
  letI :
      PseudoEMetricSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.uc_pseudoEMetricSpace
      (I := 𝓡 n) (M := Q) gUC
  letI :
      IsRiemannianManifold (𝓡 n)
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.isRiemannianManifold
      (I := 𝓡 n) (M := Q) gUC
  have hEnormBase :
      ∀ (x : Q) (v : TangentSpace (𝓡 n) x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g₁.inner x v v)) := by
    intro x v
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    rfl
  have hEnormCover :
      ∀ (x :
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
        (v : TangentSpace (𝓡 n) x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gUC.inner x v v)) := by
    intro x v
    rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
    rfl
  letI :
      CompleteSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.completeSpace_of_complete
      (I := 𝓡 n) (M := Q) g₁ hEnormBase hEnormCover
  letI :
      LocPathConnectedSpace
        (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q) :=
    ChartedSpace.locPathConnectedSpace
      (EuclideanSpace ℝ (Fin n))
      (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
  letI : RiemannianBundle
      (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x) :=
    roundBundle (A := A) (n := n)
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x) :=
    ⟨(roundMetric (E := A) (n := n)).inner,
      (roundMetric (E := A) (n := n)).contMDiff.continuous,
      fun _ _ _ => rfl⟩
  letI spherePseudo : PseudoEMetricSpace (sphere (0 : A) 1) :=
    PseudoEMetricSpace.ofRiemannianMetric (𝓡 n) (sphere (0 : A) 1)
  letI : IsRiemannianManifold (𝓡 n) (sphere (0 : A) 1) :=
    ⟨fun _ _ => rfl⟩
  letI : @CompleteSpace (sphere (0 : A) 1)
      (@PseudoEMetricSpace.toUniformSpace _ spherePseudo) :=
    @complete_of_compact (sphere (0 : A) 1)
      (@PseudoEMetricSpace.toUniformSpace _ spherePseudo) (by
        infer_instance)
  have hRound :
      ∀ (x : sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
        ‖w‖ₑ = ENNReal.ofReal
          (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)) := by
    simpa only using (round_enorm (A := A) (n := n))
  refine sphere_diffeo_one
    (A := A) (n := n) (J := 𝓡 n)
    (N := DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover Q)
    hn hRound gUC hEnormCover ?_ p q hpq hqneg
    (DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.basePoint
      (X := Q))
  simpa only [gUC, g₁] using
    DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.riemannOp_lift_one
      (I := 𝓡 n) (M := Q) g c hc hsec

end Geometry
end DifferentialGeometry
