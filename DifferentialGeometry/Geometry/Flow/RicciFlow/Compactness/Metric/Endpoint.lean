import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.BoundedGeometry


import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.CanonicalConstruction
open DifferentialGeometry.Geometry.Curvature

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

namespace MetricCompactnessInputs

def canonicalMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    CanonicalMetricCompactness (I := I) X := by
  let P : forall j : Nat, ProperMetricOn (I := I) (X.obj j) :=
    fun j => properMetricOn (I := I) (X.obj j)
      (hcomplete.complete j) (hconn j)
  let hraw := inp.toBase.exists_pairwise_approximate_isometry_subsequence hcomplete hconn
  let psi : Nat → Nat := Classical.choose hraw
  have hraw_spec := Classical.choose_spec hraw
  have hpsi : StrictMono psi := hraw_spec.1
  have B := hraw_spec.2
  let Ppsi : forall k : Nat, ProperMetricOn (I := I) ((X.subseq psi).obj k) :=
    fun k => P (psi k)
  let canon : CanonicalMetricCompactness (I := I) (X.subseq psi) :=
    HCGCompactness.canonicalMetricCompactness Ppsi B
  exact canon.ofSubsequence psi hpsi

def metricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactnessConclusion (I := I) X :=
  (canonicalMetricCompactness inp hcomplete hconn).compactness

end MetricCompactnessInputs
end HCGCompactness
end DifferentialGeometry
