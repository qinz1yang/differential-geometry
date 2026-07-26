import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldPDE

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Scalar-curvature convergence on an open time interval

This module reads the fixed-window pointwise scalar producer through the one
subsequence and one limit metric family supplied by `OpenConvOut`.
-/

noncomputable section

open Set Function Filter Bundle Manifold TopologicalSpace Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
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

/-- Scalar curvature converges pointwise at every carrier time of an open
interval, using the canonical compact window that contains that time. -/
theorem scalar_conv
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b t₀ ht₀)
    (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀)
    (cLow : Nat → Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n k : Nat, ∀ t : Real,
        t ∈ RealTimeInterval.openWindow a b t₀ n →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow n * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (srcMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real),
        t ∈ RealTimeInterval.openWindow a b t₀ n →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C) :
    FunctionPullbackTendsto (I := I) (Φ.compSubseq co.φ co.hφ)
      (fun k t x ↦
        letI : TopologicalSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).topology
        letI : ChartedSpace H (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).charted
        letI : IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
            (X.term ((subseq ∘ co.φ) k)).M := by
          change IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M
          infer_instance
        letI : SigmaCompactSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).sigmaCompact
        letI : T2Space (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).t2
        (X.term ((subseq ∘ co.φ) k)).S.scalar t x)
      (fun t x ↦
        letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
          change IsManifold I ∞ P.M
          infer_instance
        letI : SigmaCompactSpace P.M := P.sigmaCompact
        letI : T2Space P.M := P.t2
        metricScalarAt (I := I) (co.gInf t) x) := by
  intro t ht x
  have htOpen : t ∈ Set.Ioo a b := by
    simpa only [hD, RealTimeInterval.openInterval] using ht
  obtain ⟨n, hn⟩ := RealTimeInterval.exists_window_nhds ht₀ htOpen
  have htWin : t ∈ RealTimeInterval.openWindow a b t₀ n :=
    mem_of_mem_nhds hn
  simpa only [Function.comp_apply, PointedCGHMaps.compSubseq, PointedCGHMaps.map,
    OpenConvOut.at_window] using
    ConvOut.scalar_conv_at (I := I) Φ R bf hsrc htgt
      (RealTimeInterval.openWindowLeft a t₀ n)
      (RealTimeInterval.openWindowRight b t₀ n) (cLow n) (hcLow n)
      (fun k s hs ↦ hbound n k s hs) (fun q ↦ hcovTail n q)
      (OpenConvOut.at_window Φ co n) htWin x

/-- The intrinsic squared Ricci norm converges pointwise at every carrier time
of an open interval, using the same canonical compact windows as `scalar_conv`. -/
theorem ricNorm_conv
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b t₀ ht₀)
    (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀)
    (cLow : Nat → Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n k : Nat, ∀ t : Real,
        t ∈ RealTimeInterval.openWindow a b t₀ n →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow n * R.inner (y : P.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (srcMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real),
        t ∈ RealTimeInterval.openWindow a b t₀ n →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C) :
    FunctionPullbackTendsto (I := I) (Φ.compSubseq co.φ co.hφ)
      (fun k t x ↦
        letI : TopologicalSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).topology
        letI : ChartedSpace H (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).charted
        letI : IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
            (X.term ((subseq ∘ co.φ) k)).M := by
          change IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M
          infer_instance
        letI : SigmaCompactSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).sigmaCompact
        letI : T2Space (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).t2
        DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (X.term ((subseq ∘ co.φ) k)).S t x)
      (fun t x ↦
        letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
          change IsManifold I ∞ P.M
          infer_instance
        letI : SigmaCompactSpace P.M := P.sigmaCompact
        letI : T2Space P.M := P.t2
        normSq0S (I := I) (co.gInf t) x 2
          (metricRicci (I := I) (co.gInf t) x)) := by
  intro t ht x
  have htOpen : t ∈ Set.Ioo a b := by
    simpa only [hD, RealTimeInterval.openInterval] using ht
  obtain ⟨n, hn⟩ := RealTimeInterval.exists_window_nhds ht₀ htOpen
  have htWin : t ∈ RealTimeInterval.openWindow a b t₀ n :=
    mem_of_mem_nhds hn
  simpa only [Function.comp_apply, PointedCGHMaps.compSubseq, PointedCGHMaps.map,
    OpenConvOut.at_window] using
    ConvOut.ricNorm_conv_at (I := I) Φ R bf hsrc htgt
      (RealTimeInterval.openWindowLeft a t₀ n)
      (RealTimeInterval.openWindowRight b t₀ n) (cLow n) (hcLow n)
      (fun k s hs ↦ hbound n k s hs) (fun q ↦ hcovTail n q)
      (OpenConvOut.at_window Φ co n) htWin x

end OpenConvOut

end HCGCompactness
end DifferentialGeometry
