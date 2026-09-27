import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalCoverSplitNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalProductScalar
import DifferentialGeometry.Geometry.Curvature.PositiveSectional


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped _root_.Manifold ContDiff

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [LocallyPathConnectedSpace N] [SemilocallySimplyConnectedSpace N] [Inhabited N]


structure TerminalSurfaceProduct (g : SmoothRiemannianMetric I N) where

  S : Type u
  [topology : TopologicalSpace S]
  [charted : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [smooth : IsManifold (𝓡 2) ∞ S]
  [t2 : T2Space S]
  [sigmaCompact : SigmaCompactSpace S]
  [connected : ConnectedSpace S]
  h : SmoothRiemannianMetric (𝓡 2) S

  Phi : (S × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover N

  product : ∀ (y : S) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
    (UniversalCover.liftedMetric (I := I) g).inner (Phi (y, s))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
      h.inner y v w + a * c

  complete : RiemannianMetricComplete (I := 𝓡 2) h

  positive : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := 𝓡 2) h

attribute [instance] TerminalSurfaceProduct.topology TerminalSurfaceProduct.charted
  TerminalSurfaceProduct.smooth TerminalSurfaceProduct.t2
  TerminalSurfaceProduct.sigmaCompact TerminalSurfaceProduct.connected

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
