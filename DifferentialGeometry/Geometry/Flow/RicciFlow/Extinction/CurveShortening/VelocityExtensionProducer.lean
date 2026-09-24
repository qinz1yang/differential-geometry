import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.BoundaryIsotopyFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.VelocityExtensionManifoldFrontier

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]
  {a b : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem hasBoundaryIsotopyVelocityExtension_iff_loopFamilyVelocityExtensionProducer :
    HasBoundaryIsotopyVelocityExtension (I := I) (M := M) a b ↔
      LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b :=
  ⟨fun h => h, fun h => h⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] hBoundary hT2 hCompact hNonempty
  [SigmaCompactSpace M] in
theorem loopFamilyVelocityExtensionProducer_iff_allWindows :
    (∀ a b : ℝ, LoopFamilyVelocityExtensionProducer (I := I) (M := M) a b) ↔
      ∀ (a' b' : ℝ) (γ : ℝ → ContinuousFreeLoop M),
        (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a' b') →
        (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a' b') →
        (∀ t ∈ Icc a' b', Topology.IsEmbedding (γ t)) →
        LoopFamilyVelocityExtension (I := I) a' b' γ :=
  ⟨fun h a' b' => h a' b', fun h a b => h a b⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
