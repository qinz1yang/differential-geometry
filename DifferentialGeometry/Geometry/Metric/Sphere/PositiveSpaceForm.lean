import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross
import DifferentialGeometry.Geometry.Metric.Sphere.CoverQuotient
import DifferentialGeometry.Geometry.Metric.Sphere.PositiveCover
import DifferentialGeometry.Geometry.Topology.SemilocallySimplyConnected
import DifferentialGeometry.Geometry.Topology.StandardModel

set_option autoImplicit false

/-!
# Positive constant curvature gives a spherical space form

This module standardizes the model space of a closed constant-positive-
curvature manifold, identifies its universal cover with the round sphere, and
packages the deck action as finite round quotient data.
-/

noncomputable section

open Bundle Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry
namespace Geometry

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private instance sphere4_fact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

/-- Construct finite round-quotient data and the identifying diffeomorphism
from a closed connected three-manifold with a positive constant-curvature
metric. -/
noncomputable def constPosQuotient
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      DifferentialGeometry.Integral.Connection.metricRm04StdAt
          (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    Σ data : RoundQuotientData.{0, u, u}
        (EuclideanSpace ℝ (Fin 4)) 3,
      M ≃ₘ⟮I, 𝓡 3⟯ data.Q := by
  classical
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconn
  letI : I.Boundaryless := hbdry
  letI : NeZero (Module.finrank ℝ E) :=
    ⟨by rw [hdim]; decide⟩
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := by
    exact ContinuousLinearEquiv.ofFinrankEq (by
      rw [hdim, finrank_euclideanSpace_fin])
  let S := Topology.stdModelCopy (I := I) (M := M) e
  letI : CompactSpace S.Q := S.equiv.toHomeomorph.compactSpace
  letI : ConnectedSpace S.Q :=
    S.equiv.surjective.connectedSpace S.equiv.continuous
  letI : Inhabited S.Q :=
    Classical.inhabited_of_nonempty inferInstance
  letI : LocPathConnectedSpace S.Q :=
    ChartedSpace.locPathConnectedSpace
      (EuclideanSpace ℝ (Fin 3)) S.Q
  letI :
      Riemannian.Topology.SemilocallySimplyConnectedSpace S.Q :=
    Riemannian.Topology.manifold_semilocallySimplyConnectedSpace
      (I := 𝓡 3) (M := S.Q)
  letI : NeZero
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := by
    rw [finrank_euclideanSpace_fin]
    infer_instance
  let gQ : SmoothRiemannianMetric (𝓡 3) S.Q :=
    Diffeomorph.pullbackMetricCross
      (I := 𝓡 3) (J := I) g S.equiv.symm
  have hsecQ :
      ∀ x : S.Q, ∀ X Y : TangentSpace (𝓡 3) x,
        DifferentialGeometry.Integral.Connection.metricRm04StdAt
            (I := 𝓡 3) (M := S.Q) gQ x X Y Y X =
          c * (gQ.inner x X X * gQ.inner x Y Y -
            gQ.inner x X Y * gQ.inner x X Y) := by
    intro x X Y
    rw [DifferentialGeometry.Integral.Connection.metricRm04Std_pullbackCross
          g S.equiv.symm x X Y Y X,
      hsec,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X X,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x Y Y,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X Y]
  let p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
    sphereBasisPt 0
  let q : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
    sphereBasisPt 1
  have hpq : p ≠ q := by
    simpa only [p, q] using (sphereBasisPt_ne (by decide) :
      sphereBasisPt (0 : Fin 4) ≠ sphereBasisPt (1 : Fin 4))
  have hqneg : q ≠ -p := by
    simpa only [p, q] using (sphereBasisPt_ne_neg (by decide) :
      sphereBasisPt (1 : Fin 4) ≠ -sphereBasisPt (0 : Fin 4))
  have hcover :=
    sphereCover_one
      (A := EuclideanSpace ℝ (Fin 4)) (n := 3) (Q := S.Q)
      (by norm_num) gQ c hc hsecQ p q hpq hqneg
  let d := Classical.choose hcover
  have hd := Classical.choose_spec hcover
  let g₁ : SmoothRiemannianMetric (𝓡 3) S.Q :=
    DifferentialGeometry.scaleMetric (I := 𝓡 3) c hc gQ
  let data : RoundQuotientData.{0, u, u}
      (EuclideanSpace ℝ (Fin 4)) 3 :=
    roundQuotientUC g₁ d (by simpa only [g₁] using hd)
  refine ⟨data, ?_⟩
  simpa only [data] using S.equiv

end Geometry
end DifferentialGeometry
