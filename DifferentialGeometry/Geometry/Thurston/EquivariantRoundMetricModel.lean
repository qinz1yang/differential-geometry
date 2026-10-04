import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Compact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Isometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Topology.Manifold.ModelWithCorners
import DifferentialGeometry.Topology.Morse.NormalForm.Local

/-!
# Surface Ricci flows on the model `MorseModel 2`

Chapter 7, packet P8, surface lemma U1, route (a), model bridge. The surface `N` of U1 is modeled
on `MorseModel 2 = Fin 2 → ℝ`, whose sup norm is not an inner product norm.

* `exists_isometryInvariant_surfaceFlow`: for a smooth metric `h` on a compact surface modeled on
  `MorseModel 2` there is a Ricci flow on `[0, T)` starting at `h`, a `SolutionOn` with
  `IsSolutionOn`, jointly smooth on `[0, T) × N` as a section and satisfying `∂ₜ g = -2 Ric` with
  right derivatives at `0`, and every isometry of `h` is an isometry of every time slice.
  Short-time existence is `exists_completeBoundedCurvatureSolutionOn_of_compact` (which already
  passes through a Euclidean copy of the model) and the isometry step is
  `ricci_flow_pullback_eq_of_initial_isometry`.
* `surfaceModel`, `toSurfaceModel`: the same manifold with the Euclidean model
  `𝓘(ℝ, MorseModel 2).transContinuousLinearEquiv surfaceModelEquiv`, whose model vector space is
  `EuclideanSpace ℝ (Fin 2)` (needed by the inner-product-space parts of the surface theory:
  entropy, Poisson, the normalization of `EquivariantRoundMetricNormalization`).
  `isSolutionOn_toSurfaceModel` moves a flow there, and `toSurfaceModel_metric`,
  `toSurfaceModel_scalar`, `pullback_toSurfaceModel_metric` record that the metrics, their scalar
  curvatures and the round trip are unchanged.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

namespace GC.Geometry

local notation "MM2" => DifferentialGeometry.Topology.Morse.MorseModel 2
local notation "E2" => EuclideanSpace ℝ (Fin 2)

def surfaceModelEquiv : MM2 ≃L[ℝ] E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm

abbrev surfaceModel : ModelWithCorners ℝ E2 MM2 :=
  𝓘(ℝ, MM2).transContinuousLinearEquiv surfaceModelEquiv

variable {N : Type*} [TopologicalSpace N] [ChartedSpace MM2 N] [IsManifold 𝓘(ℝ, MM2) ∞ N]
  [T2Space N]

variable (N) in
def toSurfaceModel : N ≃ₘ⟮𝓘(ℝ, MM2), surfaceModel⟯ N :=
  ContinuousLinearEquiv.toTransContinuousLinearEquiv 𝓘(ℝ, MM2) N surfaceModelEquiv

theorem exists_isometryInvariant_surfaceFlow [CompactSpace N]
    (h : SmoothRiemannianMetric 𝓘(ℝ, MM2) N) :
    ∃ (T : ℝ) (hT : 0 < T)
      (S : SolutionOn (I := 𝓘(ℝ, MM2)) (M := N) (RealTimeInterval.closedOpen 0 T hT)),
      IsSolutionOn S ∧ S.family.metric 0 = h ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, MM2)) (𝓘(ℝ, MM2).prod 𝓘(ℝ, MM2 →L[ℝ] MM2 →L[ℝ] ℝ)) ∞
        (fun p : ℝ × N => (⟨p.2, (S.family.metric p.1).inner p.2⟩ :
          Bundle.TotalSpace (MM2 →L[ℝ] MM2 →L[ℝ] ℝ)
            (fun x => TangentSpace 𝓘(ℝ, MM2) x →L[ℝ] TangentSpace 𝓘(ℝ, MM2) x →L[ℝ] ℝ)))
        (Set.Ico 0 T ×ˢ (Set.univ : Set N)) ∧
      (∀ t ∈ Set.Ico 0 T, ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, MM2) x),
        HasDerivWithinAt (fun s => (S.family.metric s).inner x v w)
          (-2 * ricciTensor (S.family.metric t) x v w) (Set.Ici 0) t) ∧
      ∀ φ : N ≃ₘ⟮𝓘(ℝ, MM2), 𝓘(ℝ, MM2)⟯ N, Diffeomorph.pullbackMetric h φ = h →
        ∀ t ∈ Set.Ico 0 T,
          Diffeomorph.pullbackMetric (S.family.metric t) φ = S.family.metric t := by
  obtain ⟨T, hT, Q, h0, -, hjoint, hpde⟩ :=
    exists_completeBoundedCurvatureSolutionOn_of_compact (I := 𝓘(ℝ, MM2)) (M := N) h
  refine ⟨T, hT, Q.solution, Q.isSolution, h0, hjoint, hpde, fun φ hφ => ?_⟩
  exact ricci_flow_pullback_eq_of_initial_isometry Q.solution.base.metric hT hjoint hpde φ
    (h0 ▸ hφ)

theorem toSurfaceModel_metric (g : SmoothRiemannianMetric 𝓘(ℝ, MM2) N) :
    Diffeomorph.pullbackMetricCross g (toSurfaceModel N).symm =
      g.transContinuousLinearEquiv surfaceModelEquiv :=
  rfl

theorem pullback_toSurfaceModel_metric (g : SmoothRiemannianMetric 𝓘(ℝ, MM2) N) :
    Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross g (toSurfaceModel N).symm)
      (toSurfaceModel N) = g :=
  SmoothRiemannianMetric.pullback_transContinuousLinearEquiv g surfaceModelEquiv

theorem toSurfaceModel_scalar (g : SmoothRiemannianMetric 𝓘(ℝ, MM2) N) (x : N) :
    metricScalarAt (Diffeomorph.pullbackMetricCross g (toSurfaceModel N).symm) x =
      metricScalarAt g x :=
  DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross g (toSurfaceModel N).symm x

theorem isSolutionOn_toSurfaceModel {D : RealTimeInterval}
    (S : SolutionOn (I := 𝓘(ℝ, MM2)) (M := N) D) (hS : IsSolutionOn S) :
    IsSolutionOn (S.pullback (toSurfaceModel N).symm) :=
  IsSolutionOn.pullback S hS (toSurfaceModel N).symm

end GC.Geometry
