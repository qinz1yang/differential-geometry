import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.InjectivityRadiusDecay.Existence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.VolumeOverlap
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.HigherRegularityEndpoint

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

def metricSeedOfBG
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
    MetricCompactnessConclusion (I := I) X := by
  let b := metricSeedOfBG (I := I) X hcomplete hgeom hinj hconn
  have hd : Nonempty (BoundedGeometryNormalData (I := I) X b.decay) :=
    exists_bounded_geometry_normal_data (I := I) X hcomplete hconn hgeom b.decay b.realizes
  exact b.higherRegularityMetricCompactness (Classical.choice hd) hcomplete hconn

end HCGCompactness
end DifferentialGeometry
