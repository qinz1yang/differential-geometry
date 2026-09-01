import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.DirectLimit.Defs
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativePullback
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNormRestriction
import DifferentialGeometry.Topology.SigmaCompactOpen

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
  [∀ k, SigmaCompactSpace (A k)] [∀ k, T2Space (A k)]

def limitCGConverges
    (S : SmoothSeqSystem I A) (O₀ : A 0)
    (gSeq gLim : ∀ k, SmoothRiemannianMetric I (A k))
    (hgLim : S.MetricCocycle gLim)
    (hstage : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ K : Set (A k), IsCompact K →
        metricDerivNormSupOn (I := I) K p (gSeq k) (gLim k) (gLim k) < ε) :
    PointedRiemannianCGConverges (I := I)
      (factorSeq S O₀ gSeq) (limitPointedCoc S O₀ gLim hgLim) id
      (limitCGMapsOf S O₀ gSeq gLim hgLim) := by
  let Φ := limitCGMapsOf S O₀ gSeq gLim hgLim
  have hσsrc : ∀ k : ℕ,
      letI : TopologicalSpace (limitPointedCoc S O₀ gLim hgLim).M :=
        (limitPointedCoc S O₀ gLim hgLim).topology
      IsSigmaCompact (Φ.source k) := by
    intro k
    let : TopologicalSpace (limitPointedCoc S O₀ gLim hgLim).M :=
      (limitPointedCoc S O₀ gLim hgLim).topology
    let : ChartedSpace H (limitPointedCoc S O₀ gLim hgLim).M :=
      (limitPointedCoc S O₀ gLim hgLim).charted
    let : SigmaCompactSpace (limitPointedCoc S O₀ gLim hgLim).M :=
      (limitPointedCoc S O₀ gLim hgLim).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (Φ.source_open k)
  have hσtgt : ∀ k : ℕ,
      letI : TopologicalSpace ((factorSeq S O₀ gSeq).obj (id k)).M :=
        ((factorSeq S O₀ gSeq).obj (id k)).topology
      IsSigmaCompact (Φ.target k) := by
    intro k
    let : TopologicalSpace ((factorSeq S O₀ gSeq).obj (id k)).M :=
      ((factorSeq S O₀ gSeq).obj (id k)).topology
    let : ChartedSpace H ((factorSeq S O₀ gSeq).obj (id k)).M :=
      ((factorSeq S O₀ gSeq).obj (id k)).charted
    let : SigmaCompactSpace ((factorSeq S O₀ gSeq).obj (id k)).M :=
      ((factorSeq S O₀ gSeq).obj (id k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (Φ.target_open k)
  let refMetric : ∀ k : ℕ,
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomTop (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomSmooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k) := fun k => by
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomTop (I := I) Φ k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomCharted (I := I) Φ k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomSmooth (I := I) Φ k
    letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
    letI : T2Space (MetricSourceDomain (I := I) Φ k) :=
      metricSourceDomT2 (I := I) Φ k
    exact (S.limitMetric gLim hgLim).restrictOpen (I := I) (metricSourceOpen (I := I) Φ k)
  refine PointedRiemannianCGConverges.ofRestrictPullback (I := I)
    Φ hσsrc refMetric ?_
  intro K hK p ε hε
  obtain ⟨kSrc, hkSrc⟩ := Φ.source_subset hK
  obtain ⟨kConv, hkConv⟩ := hstage ε hε p
  refine ⟨max kSrc kConv, fun k hk => ?_⟩
  have hkS : kSrc ≤ k := le_trans (Nat.le_max_left kSrc kConv) hk
  have hkC : kConv ≤ k := le_trans (Nat.le_max_right kSrc kConv) hk
  let : TopologicalSpace (limitPointedCoc S O₀ gLim hgLim).M :=
    (limitPointedCoc S O₀ gLim hgLim).topology
  let : ChartedSpace H (limitPointedCoc S O₀ gLim hgLim).M :=
    (limitPointedCoc S O₀ gLim hgLim).charted
  let : TopologicalSpace ((factorSeq S O₀ gSeq).obj (id k)).M :=
    ((factorSeq S O₀ gSeq).obj (id k)).topology
  let : ChartedSpace H ((factorSeq S O₀ gSeq).obj (id k)).M :=
    ((factorSeq S O₀ gSeq).obj (id k)).charted
  let : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomTop (I := I) Φ k
  let : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomCharted (I := I) Φ k
  let : T2Space (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
    metricSourceDomSigmaOf (I := I) Φ k (hσsrc k)
  let : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  let : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomCharted (I := I) Φ k
  let : T2Space (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomT2 (I := I) Φ k
  let : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSigmaOf (I := I) Φ k (hσtgt k)
  let F := metricSourceTargetDiff (I := I) Φ k
  let targetSigma : SigmaCompactSpace (metricTargetOpen (I := I) Φ k) := by
    change SigmaCompactSpace (MetricTargetDomain (I := I) Φ k)
    exact metricTargetDomSigmaOf (I := I) Φ k (hσtgt k)
  let targetT2 : T2Space (metricTargetOpen (I := I) Φ k) := by
    change T2Space (MetricTargetDomain (I := I) Φ k)
    exact metricTargetDomT2 (I := I) Φ k
  let sourceMetric : SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k) :=
    (S.limitMetric gLim hgLim).restrictOpen (I := I) (metricSourceOpen (I := I) Φ k)
  let targetSeq : SmoothRiemannianMetric I (MetricTargetDomain (I := I) Φ k) :=
    (gSeq k).restrictOpen (I := I) (metricTargetOpen (I := I) Φ k)
  let targetLim : SmoothRiemannianMetric I (MetricTargetDomain (I := I) Φ k) :=
    (gLim k).restrictOpen (I := I) (metricTargetOpen (I := I) Φ k)
  have hlim : sourceMetric = Diffeomorph.pullbackMetric (I := I) targetLim F := by
    have metric_ext : ∀ (g₁ g₂ : SmoothRiemannianMetric I
        (MetricSourceDomain (I := I) Φ k)),
        (∀ (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
          g₁.inner x v w = g₂.inner x v w) → g₁ = g₂ := by
      intro g₁ g₂ h
      obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
      obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
      have hi : i₁ = i₂ :=
        funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
      subst hi
      rfl
    apply metric_ext
    intro x v w
    let inclS : MetricSourceDomain (I := I) Φ k →
        (limitPointedCoc S O₀ gLim hgLim).M := Subtype.val
    have hsrc : sourceMetric.inner x v w =
        (S.limitMetric gLim hgLim).inner (x : (limitPointedCoc S O₀ gLim hgLim).M)
          (mfderiv I I inclS x v) (mfderiv I I inclS x w) := by
      rw [SmoothRiemannianMetric.restrictOpen_inner,
        mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
    have htgt :
        (Diffeomorph.pullbackMetric (I := I) targetLim F).inner x v w =
          (gLim k).inner
            (F x).1
            (mfderiv I I F x v)
            (mfderiv I I F x w) := by
      dsimp only [targetLim]
      rw [Diffeomorph.pullbackMetric_inner,
        SmoothRiemannianMetric.restrictOpen_inner]
    rw [hsrc, htgt]
    rw [S.limitMetric_of_mem gLim hgLim k x.2]
    rw [metricSourceTargetDiff_mfderiv (I := I) Φ k x v,
      metricSourceTargetDiff_mfderiv (I := I) Φ k x w]
    simp only [inclS, mfderiv_subtype_val_apply]
    let z : (limitPointedCoc S O₀ gLim hgLim).M := x
    have hFx : (F x).1 =
        Function.invFun (S.toSeqSystem.incl k) z := by
      calc
        (F x).1 = Φ.map k z :=
          metricSourceTargetDiff_apply (I := I) Φ k x
        _ = Function.invFun (S.toSeqSystem.incl k) z := rfl
    have hmapv : mfderiv I I (Φ.map k) z v =
        mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z v := by
      rfl
    have hmapw : mfderiv I I (Φ.map k) z w =
        mfderiv I I (Function.invFun (S.toSeqSystem.incl k)) z w := by
      rfl
    rw [hFx, hmapv, hmapw]
  change metricDerivNormSupOn (I := I)
      (metricSourceCompactSet (I := I) Φ k K) p
      (Diffeomorph.pullbackMetric (I := I) targetSeq F)
      sourceMetric sourceMetric < ε
  rw [hlim, metricDerivNormSupOn_pullback_image (I := I)]
  have hKsource : IsCompact (metricSourceCompactSet (I := I) Φ k K) :=
    metricSourceCompactSet_isCompact (I := I) Φ k hK (hkSrc k hkS)
  have hKtarget : IsCompact (F '' metricSourceCompactSet (I := I) Φ k K) :=
    hKsource.image F.continuous
  let stageVal : MetricTargetDomain (I := I) Φ k → A k := by
    change {x : A k // x ∈ Set.univ} → A k
    exact Subtype.val
  let stageSet : Set (A k) :=
    stageVal '' (F '' metricSourceCompactSet (I := I) Φ k K)
  have hvalCont : Continuous stageVal := by
    dsimp only [stageVal]
    exact continuous_subtype_val
  have hKstage : IsCompact stageSet := hKtarget.image hvalCont
  calc
    metricDerivNormSupOn (I := I)
        (F '' metricSourceCompactSet (I := I) Φ k K) p targetSeq targetLim targetLim =
      metricDerivNormSupOn (I := I) stageSet p (gSeq k) (gLim k) (gLim k) := by
          dsimp only [targetSeq, targetLim]
          dsimp only [stageSet, stageVal]
          exact @metricDerivNormSupOn_restrictOpen E inferInstance inferInstance
            inferInstance inferInstance H inferInstance I
            (A k) inferInstance inferInstance inferInstance inferInstance
            (gSeq k) (gLim k) (gLim k) (metricTargetOpen (I := I) Φ k)
            targetSigma targetT2 (F '' metricSourceCompactSet (I := I) Φ k K) p
    _ < ε := hkConv k hkC stageSet hKstage

end

end HCGCompactness
end DifferentialGeometry
