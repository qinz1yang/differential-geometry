import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.Topology.Homotopy.Equiv

set_option autoImplicit false
noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

def hasConstantSectionalCurvature (g : SmoothRiemannianMetric (𝓡 3) M) (K : ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace (𝓡 3) p),
    LinearIndependent ℝ ![v, w] → Geometry.Riemannian.sectionalCurvature g p v w = K

theorem mostow_prasad
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (h : SmoothRiemannianMetric (𝓡 3) N)
    (K : ℝ) (hK : K < 0)
    (hgcurvature : hasConstantSectionalCurvature g K)
    (hhcurvature : hasConstantSectionalCurvature h K)
    (hgcomplete : RiemannianMetricComplete g)
    (hhcomplete : RiemannianMetricComplete h)
    (hgvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (hhvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < ⊤)
    (u : ContinuousMap.HomotopyEquiv M N) :
    ∃! f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N,
      (∀ (p : M) (v w : TangentSpace (𝓡 3) p),
        h.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p v)
          (mfderiv (𝓡 3) (𝓡 3) f p w) = g.inner p v w) ∧
      (⟨f, f.continuous⟩ : C(M, N)).Homotopic u.toFun := by
  sorry

end DifferentialGeometry.Geometry.Hyperbolic
