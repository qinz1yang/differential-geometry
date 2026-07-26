import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldLower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Positive lower bounds on an open-window metric limit

The coefficient may vary with the canonical compact time window.  At each
interior time, one window therefore supplies one positive global comparison
constant for the limit metric at that time.
-/

noncomputable section

open Set Bundle Manifold
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace OpenConvOut

/-- Windowwise positive lower bounds along the selected sequence give a
positive global lower bound for the limit metric at each interior time. -/
theorem metric_lower
    {R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀)
    (c : Nat → Real) (hc : ∀ n, 0 < c n)
    (hseq : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      ∀ (n k : Nat) (t : Real),
        t ∈ RealTimeInterval.openWindow a b t₀ n →
          ∀ (x : P.M) (v : TangentSpace I x),
            c n * R.inner x v v ≤
              (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t).inner x v v)
    {t : Real} (ht : t ∈ Set.Ioo a b) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ∃ c₀ : Real, 0 < c₀ ∧
      ∀ (x : P.M) (v : TangentSpace I x),
        c₀ * R.inner x v v ≤ (co.gInf t).inner x v v := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  obtain ⟨n, htn⟩ := RealTimeInterval.mem_openWindow (t₀ := t₀) ht
  refine ⟨c n, hc n, ?_⟩
  exact ConvOut.lower_of (I := I) (Φ := Φ) (OpenConvOut.at_window Φ co n)
    (hseq n) t htn

end OpenConvOut
end HCGCompactness
end DifferentialGeometry
