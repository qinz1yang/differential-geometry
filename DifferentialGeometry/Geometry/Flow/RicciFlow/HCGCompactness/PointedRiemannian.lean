import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.Riemannian.Basic
import DifferentialGeometry.Geometry.Metric.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Pointed Riemannian Manifold Data For HCG Compactness

This file contains the metric-only pointed Riemannian layer used by MSM135
Theorem 3.9.  Completeness is stated using Mathlib's Riemannian emetric induced
by the stored smooth Riemannian metric.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

/-- One pointed Riemannian manifold candidate.

This is the metric-only Riemannian-manifold object used by MSM135 Theorem 3.9.
Completeness is kept as a separate theorem-facing predicate below, but that
predicate uses the Riemannian emetric canonically induced by `metric`. -/
structure PointedRiemannianManifold
    (I : ModelWithCorners Real E H) where
  M : Type u
  [topology : TopologicalSpace M]
  [charted : ChartedSpace H M]
  [smooth : IsManifold I ∞ M]
  [sigmaCompact : SigmaCompactSpace M]
  [t2 : T2Space M]
  [t2TangentBundle : T2Space (TangentBundle I M)]
  basepoint : M
  metric : SmoothRiemannianMetric I M

namespace PointedRiemannianManifold

variable {I : ModelWithCorners Real E H}

/-- Replace only the distinguished point of a pointed Riemannian manifold. -/
def repoint (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) :=
  { X with basepoint := x }

end PointedRiemannianManifold

/-- A sequence of pointed Riemannian manifold candidates. -/
structure PointedRiemannianSeq (I : ModelWithCorners Real E H) where
  obj : Nat -> PointedRiemannianManifold.{u, uE, uH} (I := I)

namespace PointedRiemannianSeq

variable {I : ModelWithCorners Real E H}

/-- Basepoint of the `i`th pointed metric in the sequence. -/
def basepoint (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (i : Nat) :
    (X.obj i).M :=
  (X.obj i).basepoint

/-- Reindex a pointed metric sequence along a subsequence. -/
def subseq (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (f : Nat -> Nat) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj := fun i => X.obj (f i)

/-- Replace only the distinguished point of every member of a pointed sequence. -/
def repoint (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (b : forall i : Nat, (X.obj i).M) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj i := (X.obj i).repoint (b i)

end PointedRiemannianSeq

/-- Completeness of the Riemannian distance induced by the stored smooth
Riemannian metric.

The active uniform structure in this predicate is Mathlib's
`EMetricSpace.ofRiemannianMetric`, built from the `RiemannianBundle` determined
by `X.metric`. -/
def MetricComplete {I : ModelWithCorners Real E H}
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : IsManifold I 1 X.M :=
    IsManifold.of_le (I := I) (M := X.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  letI : TopologicalSpace.MetrizableSpace X.M :=
    Manifold.metrizableSpace I X.M
  letI : T3Space X.M := inferInstance
  letI : RiemannianBundle (fun x : X.M => TangentSpace I x) :=
    ⟨X.metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : X.M => TangentSpace I x) :=
    ⟨⟨X.metric.inner, X.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
  letI : EMetricSpace X.M := EMetricSpace.ofRiemannianMetric I X.M
  CompleteSpace X.M

namespace MetricComplete

/-- Projection from the pointed-manifold completeness predicate to the active
Riemannian emetric `CompleteSpace` instance. -/
theorem complete {I : ModelWithCorners Real E H}
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hX : MetricComplete (I := I) X) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : IsManifold I 1 X.M :=
      IsManifold.of_le (I := I) (M := X.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    letI : TopologicalSpace.MetrizableSpace X.M :=
      Manifold.metrizableSpace I X.M
    letI : T3Space X.M := inferInstance
    letI : RiemannianBundle (fun x : X.M => TangentSpace I x) :=
      ⟨X.metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : X.M => TangentSpace I x) :=
      ⟨⟨X.metric.inner, X.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace X.M := EMetricSpace.ofRiemannianMetric I X.M
    CompleteSpace X.M := by
  simpa [MetricComplete] using hX

end MetricComplete

/-- Completeness input for every term of a pointed metric sequence. -/
structure SeqMetricComplete {I : ModelWithCorners Real E H}
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop where
  complete : forall i : Nat, MetricComplete (I := I) (X.obj i)

namespace SeqMetricComplete

variable {I : ModelWithCorners Real E H}

/-- Reindex sequence completeness along a subsequence. -/
theorem subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqMetricComplete (I := I) X) (f : Nat -> Nat) :
    SeqMetricComplete (I := I) (X.subseq f) where
  complete := by
    intro i
    simpa [PointedRiemannianSeq.subseq] using hX.complete (f i)

end SeqMetricComplete

end HCGCompactness
end DifferentialGeometry
