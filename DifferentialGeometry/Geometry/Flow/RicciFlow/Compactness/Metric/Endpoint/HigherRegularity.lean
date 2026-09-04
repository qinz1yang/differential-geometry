import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.BoundedGeometry



import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Canonical.Construction

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

namespace MetricCompactSeed

def higherRegularityCanonicalMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    CanonicalMetricCompactness (I := I) X := by
  let P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j) :=
    fun j => properMetricOn (I := I) (X.obj j)
      (hcomplete.complete j) (hconn j)
  let hraw := b.exists_pairwise_approximate_isometry_subsequence_of_bounded_geometry d hcomplete hconn
  let psi : Nat → Nat := Classical.choose hraw
  have hraw_spec := Classical.choose_spec hraw
  have hpsi : StrictMono psi := hraw_spec.1
  have B := hraw_spec.2
  let Ppsi : ∀ k : Nat, ProperMetricOn (I := I) ((X.subseq psi).obj k) :=
    fun k => P (psi k)
  let canon : CanonicalMetricCompactness (I := I) (X.subseq psi) :=
    canonicalMetricCompactness Ppsi B
  exact canon.ofSubsequence psi hpsi

def higherRegularityMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactnessConclusion (I := I) X :=
  (b.higherRegularityCanonicalMetricCompactness d hcomplete hconn).compactness

theorem higher_regularity_canonical_metric_compactness_connected
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let C := b.higherRegularityCanonicalMetricCompactness d hcomplete hconn
    letI : TopologicalSpace C.compactness.limit.M := C.compactness.limit.topology
    ConnectedSpace C.compactness.limit.M := by
  classical
  dsimp only [higherRegularityCanonicalMetricCompactness, CanonicalMetricCompactness.ofSubsequence,
    MetricCompactnessConclusion.ofSeqSubseq]
  exact canonical_metric_compactness_connected (I := I) _ _

end MetricCompactSeed

namespace MetricCompactBase

def higherRegularityCanonicalMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    CanonicalMetricCompactness (I := I) X :=
  b.toSeed.higherRegularityCanonicalMetricCompactness d hcomplete hconn

def higherRegularityMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactnessConclusion (I := I) X :=
  b.toSeed.higherRegularityMetricCompactness d hcomplete hconn

theorem higher_regularity_canonical_metric_compactness_connected
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let C := b.higherRegularityCanonicalMetricCompactness d hcomplete hconn
    letI : TopologicalSpace C.compactness.limit.M := C.compactness.limit.topology
    ConnectedSpace C.compactness.limit.M := by
  change @ConnectedSpace
    (b.toSeed.higherRegularityCanonicalMetricCompactness d hcomplete hconn).compactness.limit.M
    (b.toSeed.higherRegularityCanonicalMetricCompactness d hcomplete hconn).compactness.limit.topology
  exact
    b.toSeed.higher_regularity_canonical_metric_compactness_connected d hcomplete hconn

end MetricCompactBase
end HCGCompactness
end DifferentialGeometry
