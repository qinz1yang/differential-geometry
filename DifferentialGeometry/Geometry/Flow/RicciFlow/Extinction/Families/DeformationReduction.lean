import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.UniformRampFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyContinuity



noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

def rampAreaData (B : RicciBackground (I := I) (M := Q) D a b) : Prop :=
  curveShorteningLeastAreaSlope (I := I) (M := Q) B ∧
    curveShorteningTotalCurvatureBound (I := I) (M := Q) B

def rampUniformBoundsData (B : RicciBackground (I := I) (M := Q) D a b) : Prop :=
  RampLengthEvolution (I := I) (Q := Q) (D := D) (a := a) (b := b) B ∧
    rampAreaData (I := I) (Q := Q) (D := D) (a := a) (b := b) B

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
