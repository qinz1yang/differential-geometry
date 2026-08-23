import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.SourceCovariantLipschitz


set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold Topology ContDiff

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

noncomputable def convOut_of_src
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ)
    (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    {β ψ Bmax : Real}
    (hβψ : β ≤ ψ) (hBmax : 1 ≤ Bmax)
    (hequiv :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        ∀ t : Real, t ∈ Set.Icc β ψ →
          MetricUniformEquivalentOn (I := I)
            (Set.univ : Set (SourceDomain (I := I) Φ k))
            (refRes (I := I) Φ R k)
            (srcMetric (I := I) Φ hsrc htgt k t) Bmax)
    (src : SrcCovLipData (I := I) Φ R hsrc htgt β ψ) :
    ConvOut (I := I) Φ R bf hsrc htgt β ψ := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  let cLow : Real := Bmax⁻¹
  have hcLow : 0 < cLow := by
    exact inv_pos.mpr (lt_of_lt_of_le one_pos hBmax)
  have hbound : ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
      ∀ (y : SourceDomain (I := I) Φ k)
        (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
          TangentSpace I y),
        cLow * R.inner (y : P.M) v v ≤
          letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
            sourceDomTop (I := I) Φ k
          letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
            sourceDomCharted (I := I) Φ k
          letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
            sourceDomSmooth (I := I) Φ k
          (srcMetric (I := I) Φ hsrc htgt k t).inner y v v := by
    intro k t ht y v
    simpa only [cLow] using
      ((hequiv k t ht).2 y (Set.mem_univ y) v).1
  have hcovTail : ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real),
      t ∈ Set.Icc β ψ → ∀ z : P.M, z ∈ bf.grow k →
        metricCovDerivNorm (I := I) q
          (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C := by
    have hcovSrc : ∀ q : Nat, ∃ C : Real, 0 ≤ C ∧
        ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
          ∀ y : SourceDomain (I := I) Φ k, (y : P.M) ∈ bf.grow k →
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : T2Space (SourceDomain (I := I) Φ k) :=
              sourceDomT2 (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
              sourceDomSigmaOf (I := I) Φ k (hsrc k)
            metricCovDerivNorm (I := I) q
              (srcMetric (I := I) Φ hsrc htgt k t)
              (refRes (I := I) Φ R k) y ≤ C := by
      intro q
      obtain ⟨C, hC, hcov⟩ := src.cov q
      exact ⟨C, hC, fun k t ht y _hy => hcov k t ht y⟩
    exact covTail_of_bounds (I := I) Φ R bf hsrc htgt β ψ hcovSrc
  have hlipTail : ∀ p : Nat, ∃ Lt : Real, 0 ≤ Lt ∧
      ∀ (k : Nat) (s t : Real), s ∈ Set.Icc β ψ → t ∈ Set.Icc β ψ →
        ∀ q : Nat, q ≤ p → ∀ z : P.M, z ∈ bf.grow k →
          metricDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k s)
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤
              Lt * |s - t| := by
    have hlipG : ∀ p : Nat, ∃ Lt : Real, 0 ≤ Lt ∧
        ∀ (k : Nat) (s t : Real), s ∈ Set.Icc β ψ → t ∈ Set.Icc β ψ →
          ∀ q : Nat, q ≤ p →
            ∀ y : SourceDomain (I := I) Φ k, (y : P.M) ∈ bf.grow k →
              letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
              letI : T2Space (SourceDomain (I := I) Φ k) :=
                sourceDomT2 (I := I) Φ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
                sourceDomSmooth (I := I) Φ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
                sourceDomSigmaOf (I := I) Φ k (hsrc k)
              metricDerivNorm (I := I) q
                (srcMetric (I := I) Φ hsrc htgt k s)
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R k) y ≤ Lt * |s - t| := by
      intro p
      obtain ⟨Lt, hLt, hlip⟩ := src.lip p
      exact ⟨Lt, hLt, fun k s t hs ht q hq y _hy =>
        hlip k s t hs ht q hq y⟩
    exact lipTail_of_src (I := I) Φ R bf hsrc htgt β ψ hlipG
  have hlipSrc : ∀ k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
        sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
        sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) :=
        sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
        sourceDomSmooth (I := I) Φ k
      letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
        sourceDomSigmaOf (I := I) Φ k (hsrc k)
      letI : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) :=
        sourceDomSigmaOf (I := I) Φ k (hsrc k)
      letI : T2Space ↥(sourceOpen (I := I) Φ k) :=
        sourceDomT2 (I := I) Φ k
      ∀ C : Set (SourceDomain (I := I) Φ k), IsCompact C → ∀ p : Nat,
        ∃ Ls : Real, 0 ≤ Ls ∧
          ∀ (s t : Real), s ∈ Set.Icc β ψ → t ∈ Set.Icc β ψ →
            ∀ q : Nat, q ≤ p →
              ∀ y : SourceDomain (I := I) Φ k, y ∈ C →
                metricDerivNorm (I := I) q
                  (srcMetric (I := I) Φ hsrc htgt k s)
                  (srcMetric (I := I) Φ hsrc htgt k t)
                  (refRes (I := I) Φ R k) y ≤ Ls * |s - t| := by
    intro k C _hC p
    obtain ⟨Ls, hLs, hlip⟩ := src.lip p
    exact ⟨Ls, hLs, fun s t hs ht q hq y _hy =>
      hlip k s t hs ht q hq y⟩
  exact convOut (I := I) (Φ := Φ) R bf hsrc htgt β ψ hβψ cLow hcLow
    hbound hcovTail hlipTail hlipSrc

end HCGCompactness
end DifferentialGeometry
