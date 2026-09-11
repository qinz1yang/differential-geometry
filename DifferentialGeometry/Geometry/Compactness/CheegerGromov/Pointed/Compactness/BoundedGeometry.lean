import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.InjectivityRadiusDecay.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.VolumeOverlap
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.NormalCharts
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Restriction
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.ConnectedComponent

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

def metricCompactSeedOfBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hinj : BaseInjBound (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactSeed (I := I) X := by
  let hd := injectivityRadiusDecayOfBoundedGeometry (I := I) X hcomplete hconn hgeom hinj
  let hreal : hd.RealizesDistance :=
    injectivity_radius_decay_realizes_distance (I := I) X hcomplete hconn hgeom hinj
  let out :=
    volInputOfBg (I := I) X hgeom hd hreal hcomplete hconn 1
      (by norm_num : (0 : Real) < 1)
  exact
    { decay := hd
      packAll := fun D hD =>
        packInputOfBg (I := I) X hgeom hd hreal hcomplete hconn D hD
      volume := out.1
      dist_eq := out.2
      realizes := hreal }

def metricCompactnessOfBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hinj : BaseInjBound (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactLimit (I := I) X := by
  let b := metricCompactSeedOfBoundedGeometry (I := I) X hcomplete hgeom hinj hconn
  have hd : Nonempty (BoundedGeometryNormalChartData (I := I) X b.decay) :=
    nonempty_bounded_geometry_normal_chart_data (I := I) X hcomplete hconn hgeom b.decay b.realizes
  exact b.higherRegularityMetricCompactness (Classical.choice hd) hcomplete hconn

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private def metricCompactnessByComponents (S : PointedRiemannianSeq I)
    (hcomplete : SeqMetricComplete S) (hgeom : SeqBoundedGeometry S) (hinj : BaseInjBound S) :
    MetricCompactLimit S := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let R := S.connectedComponent
  let B := metricCompactnessOfBoundedGeometry R hcomplete.connectedComponent
    hgeom.connectedComponent (hinj.connectedComponent hcomplete)
    (fun k => (S.obj k).connectedComponent_connected)
  letI (i : ℕ) : TopologicalSpace (S.obj i).M := (S.obj i).topology
  letI (i : ℕ) : ChartedSpace H (S.obj i).M := (S.obj i).charted
  let U := fun i => connectedComponentOpen (I := I) (S.obj i).basepoint
  exact
    { subseq := B.subseq
      strictMono := B.strictMono
      limit := B.limit
      limit_complete := B.limit_complete
      maps := PointedRiemannianConvergenceMaps.liftTargetOpen
        (S := S) (L := B.limit) (subseq := B.subseq) U (fun _ => mem_connectedComponent) B.maps
      convergence := PointedRiemannianConverges.liftTargetOpen
        (S := S) (L := B.limit) (subseq := B.subseq) U (fun _ => mem_connectedComponent)
        (Φ := B.maps) B.convergence }

def metricCompactness (S : PointedRiemannianSeq I)
    (hcomplete : SeqMetricComplete S) (hgeom : SeqBoundedGeometry S) (hinj : BaseInjBound S) :
    MetricCompactLimit S := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact if hconn : ∀ k : ℕ,
      letI : TopologicalSpace (S.obj k).M := (S.obj k).topology
      ConnectedSpace (S.obj k).M then
    metricCompactnessOfBoundedGeometry S hcomplete hgeom hinj hconn
  else metricCompactnessByComponents S hcomplete hgeom hinj

theorem metricCompactness_eq_of_connected [CompleteSpace E] (S : PointedRiemannianSeq I)
    (hcomplete : SeqMetricComplete S) (hgeom : SeqBoundedGeometry S) (hinj : BaseInjBound S)
    (hconn : ∀ k : ℕ,
      letI : TopologicalSpace (S.obj k).M := (S.obj k).topology
      ConnectedSpace (S.obj k).M) :
    metricCompactness S hcomplete hgeom hinj =
      metricCompactnessOfBoundedGeometry S hcomplete hgeom hinj hconn := by
  classical
  simp only [metricCompactness, dif_pos hconn]

end

end CheegerGromovCompactness
end DifferentialGeometry
