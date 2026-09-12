import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedTraceHarnack

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology Interval

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance normalizedHarnackTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance normalizedHarnackCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance normalizedHarnackSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance normalizedHarnackC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance normalizedHarnackT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

theorem exists_normalized_klim_canonical_harnack_limit
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = CanonicalNeighborhood.ancientTimeInterval) (hdim : Module.finrank ℝ E = 3)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (hbase : ∀ i, CanonicalNeighborhood.PointedFlowScalarAtBase (I := I) (X.term i) 1) :
    ∃ (L : PointedFlowData.{u, uE, uH} (I := I) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi,
        KLim (I := I) kappa L ∧
        CanonicalNeighborhood.PointedFlowScalarAtBase (I := I) L 1 ∧
        ∀ t ∈ X.D.carrier,
          ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
            ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I) (Phi.atTime (L := L) t) k := by
  obtain ⟨L, phi, hphi, Phi, hconn, hcomplete, hbaseL, hflat, hRm, hNC, hconv⟩ :=
    exists_normalized_klim_canonical_slice_limit X hD hdim hsource hbase
  refine ⟨L, phi, hphi, Phi, ?_, hbaseL, hconv⟩
  exact
    { dimension_ge_two := by omega
      kappa_pos := (hsource 0).kappa_pos
      carrier_eq := (hsource 0).carrier_eq
      regular_eq := (hsource 0).regular_eq
      connected := hconn
      complete := hcomplete
      nonnegativeCurvatureOperator := hRm
      noncollapsed := hNC
      notFlat := hflat
      traceHarnack := fun t ht x V =>
        pointed_limit_traceHarnack Phi hsource hconv ht (hcomplete t ht) x V }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
