import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedRiemannian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Basic Hamilton--Cheeger--Gromov Compactness Vocabulary

This file contains theorem-facing data and input packages for pointed
Ricci-flow compactness.  The metric-only pointed Riemannian layer and concrete
Riemannian-distance completeness predicate live in `PointedRiemannian.lean`.
The legacy numeric injectivity-radius slot remains for older wrappers.  The
canonical noncollapse-to-injectivity boundary lives in
`NoncollapseInjectivity.lean` and uses actual metric balls and volumes.
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
variable {I : ModelWithCorners Real E H}

/-- One complete pointed Ricci-flow solution candidate on a fixed real time
interval.

The source manifold is part of the data so a sequence may vary its underlying
manifold, as in the Hamilton compactness theorem. -/
structure PointedFlowData
    (I : ModelWithCorners Real E H) (D : DifferentialGeometry.Integral.Connection.RealTimeInterval) where
  M : Type u
  [topology : TopologicalSpace M]
  [charted : ChartedSpace H M]
  [smooth : IsManifold I ∞ M]
  [sigmaCompact : SigmaCompactSpace M]
  [t2 : T2Space M]
  [t2TangentBundle : T2Space (TangentBundle I M)]
  basepoint : M
  S :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D
  isSolution :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S

namespace PointedFlowData

variable {I : ModelWithCorners Real E H}
variable {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}

/-- The Riemannian pointed metric obtained by slicing a pointed flow at time
`t`. -/
def atTime (F : PointedFlowData.{u, uE, uH} (I := I) D) (t : Real) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := F.M
  topology := F.topology
  charted := F.charted
  smooth := F.smooth
  sigmaCompact := F.sigmaCompact
  t2 := F.t2
  t2TangentBundle := F.t2TangentBundle
  basepoint := F.basepoint
  metric := by
    letI : TopologicalSpace F.M := F.topology
    letI : ChartedSpace H F.M := F.charted
    letI : IsManifold I ∞ F.M := F.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
      change IsManifold I ∞ F.M
      infer_instance
    letI : SigmaCompactSpace F.M := F.sigmaCompact
    letI : T2Space F.M := F.t2
    exact F.S.family.metric t

/-- Canonical squared norm of the lowered Riemann tensor of a pointed flow. -/
def rmNormSq (F : PointedFlowData (I := I) D) (t : Real) (x : F.M) : Real :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  Tensor0SBundle.normSq0S (I := I) (F.S.family.metric t) x 4
    (F.S.base.rm04 t x)

end PointedFlowData

/-- A sequence of pointed Ricci-flow solution candidates on one common time
interval. -/
structure PointedFlowSeq (I : ModelWithCorners Real E H) where
  D : DifferentialGeometry.Integral.Connection.RealTimeInterval
  term : Nat -> PointedFlowData.{u, uE, uH} (I := I) D

namespace PointedFlowSeq

variable {I : ModelWithCorners Real E H}

/-- Basepoint of the `i`th pointed flow in the sequence. -/
def basepoint (X : PointedFlowSeq.{u, uE, uH} (I := I)) (i : Nat) :
    (X.term i).M :=
  (X.term i).basepoint

/-- Time-slice pointed metric sequence associated to a pointed flow sequence. -/
def atTime (X : PointedFlowSeq.{u, uE, uH} (I := I)) (t : Real) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj := fun i => (X.term i).atTime (I := I) t

/-- The time-zero pointed metric sequence associated to a pointed flow
sequence. -/
def atZero (X : PointedFlowSeq.{u, uE, uH} (I := I)) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) :=
  X.atTime (I := I) 0

end PointedFlowSeq

/-- Completeness input for a pointed flow sequence, using the Riemannian
distance of each time-slice metric. -/
structure CompleteInput {I : ModelWithCorners Real E H}
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  complete_on :
    forall i : Nat, forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) ((X.term i).atTime (I := I) t)

namespace CompleteInput

/-- Completeness of a pointed flow sequence restricts to completeness of every
chosen time-slice sequence. -/
def at_time {I : ModelWithCorners Real E H}
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (h : CompleteInput (I := I) X) {t : Real} (ht : t ∈ X.D.carrier) :
    SeqMetricComplete (I := I) (X.atTime (I := I) t) where
  complete := fun i => h.complete_on i t ht

end CompleteInput

/-- Uniform curvature bound on every compact time window inside the common
time interval.  The bound is stated for the squared norm of the canonical
lowered Riemann tensor. -/
structure CurvBoundInput {I : ModelWithCorners Real E H}
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop where
  bound_on_window :
    forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
      exists C : Real, 0 <= C /\
        forall i : Nat, forall t : Real, t ∈ Set.Icc a b ->
          forall x : (X.term i).M,
            (X.term i).rmNormSq (I := I) t x <= C

/-- Injectivity-radius input at the basepoints at time zero.

Legacy compatibility slot for older Hamilton wrappers.  The numeric accessor is
not tied to the normal-coordinate injectivity-radius backend, and this record is
not used by the new compactness theorem.  Use `FlowBaseInjBound` from
`InjectivityRadius.lean` for the real MSM135 injectivity-radius hypothesis. -/
structure InjInput {I : ModelWithCorners Real E H}
    (_X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  injRadiusAtBase : Nat -> Real
  iota : Real
  iota_pos : 0 < iota
  inj_lower : forall i : Nat, iota <= injRadiusAtBase i

end HCGCompactness
end DifferentialGeometry
