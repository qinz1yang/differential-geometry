import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpenLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompleteness

set_option autoImplicit false

/-!
# Completeness of open-window limit metrics

A windowwise positive lower bound for the selected metric sequence makes every
time slice of the open-window limit complete whenever the reference pointed
manifold is complete.
-/

noncomputable section

open Set Bundle Manifold
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace OpenConvOut

/-- A time slice of an open-window metric limit is complete when the reference
metric is complete and the selected sequence has positive windowwise lower
bounds relative to it. -/
theorem complete_at
    (hP : MetricComplete (I := I) P)
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real}
    (co : OpenConvOut (I := I) Φ P.metric bf hsrc htgt a b t₀)
    (c : Nat → Real) (hc : ∀ n, 0 < c n)
    (hseq : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      ∀ (n k : Nat) (t : Real),
        t ∈ RealTimeInterval.openWindow a b t₀ n →
          ∀ (x : P.M) (v : TangentSpace I x),
            c n * P.metric.inner x v v ≤
              (gSeqExt (I := I) Φ P.metric bf hsrc htgt (co.φ k) t).inner x v v)
    {t : Real} (ht : t ∈ Set.Ioo a b) :
    MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  obtain ⟨c₀, hc₀, hlower⟩ := metric_lower Φ co c hc hseq ht
  exact MetricComplete.complete_of_lower P hP (co.gInf t) c₀ hc₀ hlower

end OpenConvOut
end HCGCompactness
end DifferentialGeometry

end
