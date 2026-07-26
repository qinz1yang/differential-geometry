import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1RawProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDAssembly

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM135 Theorem 3.9 -- conditional Chapter-4 endpoint

This final assembly file combines the concrete B/C `StepB1RawInput` producer
with the checked Step-D consumer and transports the resulting nested
subsequence conclusion back to the original pointed sequence.
-/

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

/-- The conditional Chapter-4 construction with the concrete canonical
reference-metric provenance retained alongside its public compactness output. -/
def metricCanon
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (_hgeom : SeqBoundedGeometry (I := I) X)
    (_hinj : BaseInjBound (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    StepDCanonData (I := I) X := by
  let P : forall j : Nat, ProperMetricOn (I := I) (X.obj j) :=
    fun j => properMetricOn (I := I) (X.obj j)
      (hcomplete.complete j) (hconn j)
  let hraw := inp.toBase.exists_b1_raw hcomplete hconn
  let psi : Nat → Nat := Classical.choose hraw
  have hraw_spec := Classical.choose_spec hraw
  have hpsi : StrictMono psi := hraw_spec.1
  have B := hraw_spec.2
  let Ppsi : forall k : Nat, ProperMetricOn (I := I) ((X.subseq psi).obj k) :=
    fun k => P (psi k)
  let canon : StepDCanonData (I := I) (X.subseq psi) :=
    compactness_canon Ppsi B
  exact canon.ofSeqSubseq psi hpsi

/-- **MSM135 Theorem 3.9, conditional form -- the Chapter 4 working target.**
Compactness for complete connected pointed Riemannian manifolds, given the
bundled book-external geometric inputs. -/
def metricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessInputs (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hgeom : SeqBoundedGeometry (I := I) X)
    (hinj : BaseInjBound (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactnessConclusion (I := I) X :=
  (metricCanon inp hcomplete hgeom hinj hconn).mc

end MetricCompactnessInputs
end HCGCompactness
end DifferentialGeometry
