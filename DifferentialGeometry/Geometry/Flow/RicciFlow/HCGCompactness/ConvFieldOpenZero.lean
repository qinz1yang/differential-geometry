import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpen

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Time-zero identification for an open-window metric limit

The open-window output has the same selected sequence and limit family on each
canonical closed window, so time-zero identification is read from any window
containing zero.
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

/-- Identify the time-zero open-window limit with any pointwise time-zero
limit of the pulled-back source metrics along the underlying sequence. -/
theorem gInf_zero_eq
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    {a b t₀ : Real} (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀)
    (hzero : (0 : Real) ∈ Set.Ioo a b)
    (g₀ : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (hconv₀ : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : T2Space P.M := P.t2;
      letI : IsManifold I ∞ P.M := P.smooth;
      letI : SigmaCompactSpace P.M := P.sigmaCompact;
      ∀ (x : P.M) (v w : TangentSpace I x) (ε : Real), 0 < ε →
        ∃ k₀ : Nat, ∀ k : Nat, k₀ ≤ k → ∀ hx : x ∈ Φ.source k,
          |(letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
                sourceDomSmooth (I := I) Φ k
            (srcMetric (I := I) Φ hsrc htgt k 0).inner ⟨x, hx⟩ v w) -
              g₀.inner x v w| < ε) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    co.gInf 0 = g₀ := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  obtain ⟨n, hzeroN⟩ := RealTimeInterval.mem_openWindow (t₀ := t₀) hzero
  exact DifferentialGeometry.HCGCompactness.gInf_zero_eq (I := I) Φ R bf hsrc htgt
    (RealTimeInterval.openWindowLeft a t₀ n)
    (RealTimeInterval.openWindowRight b t₀ n)
    (OpenConvOut.at_window Φ co n) hzeroN g₀ hconv₀

end OpenConvOut
end HCGCompactness
end DifferentialGeometry
