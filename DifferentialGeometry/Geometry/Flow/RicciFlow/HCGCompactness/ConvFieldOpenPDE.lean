import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldPDE

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Ricci-flow equation for the open-window metric limit

This module reads the checked fixed-window PDE through `OpenConvOut`.  It uses
the canonical-window neighborhood property to upgrade a derivative within one
closed window to an ordinary derivative at each regular time of the ambient
open interval.
-/

noncomputable section

open Set Function Filter Bundle Manifold TopologicalSpace
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
variable {subseq : Nat -> Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace OpenConvOut

/-- The metric family glued from all canonical compact windows satisfies the
Ricci-flow metric equation at every regular time of the ambient open interval. -/
theorem gInf_pde
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b t₀ ht₀)
    (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀)
    (cLow : Nat -> Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n k : Nat, ∀ t : Real,
        t ∈ RealTimeInterval.openWindow a b t₀ n ->
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow n * R.inner (y : P.M) v v <=
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
        t ∈ RealTimeInterval.openWindow a b t₀ n ->
        ∀ z : P.M, z ∈ bf.grow k ->
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z <= C)
    {t : Real} (ht : t ∈ X.D.regular) (x : P.M)
    (v w : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      TangentSpace I x) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    HasDerivAt (fun s : Real => (co.gInf s).inner x v w)
      ((-2 : Real) * ricciTensor (I := I) (co.gInf t) x v w) t := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  have htOpen : t ∈ Set.Ioo a b := by
    simpa only [hD, RealTimeInterval.openInterval] using ht
  obtain ⟨n, hn⟩ := RealTimeInterval.exists_window_nhds ht₀ htOpen
  have htWin : t ∈ RealTimeInterval.openWindow a b t₀ n :=
    mem_of_mem_nhds hn
  have hwin : RealTimeInterval.openWindow a b t₀ n ⊆ X.D.regular := by
    intro s hs
    have hsOpen := RealTimeInterval.openWindow_subset ht₀ n hs
    simpa only [hD, RealTimeInterval.openInterval] using hsOpen
  have hd := ConvOut.gInf_pde (I := I) (Φ := Φ) R bf hsrc htgt
    (RealTimeInterval.openWindowLeft a t₀ n)
    (RealTimeInterval.openWindowRight b t₀ n) hwin (cLow n) (hcLow n)
    (fun k s hs => hbound n k s hs) (fun q => hcovTail n q)
    (OpenConvOut.at_window Φ co n) x v w htWin
  exact hd.hasDerivAt hn

end OpenConvOut

end HCGCompactness
end DifferentialGeometry
