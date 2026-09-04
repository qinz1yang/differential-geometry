import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Regularity

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Equation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.CurvatureConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.FlowLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn)

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace OpenMetricConvergenceData

theorem isSolution
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b t₀ ht₀)
    (co : OpenMetricConvergenceData (I := I) Φ R bf hsrc htgt a b t₀)
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
            (sourceMetric (I := I) Φ hsrc htgt k t).inner y v v)
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
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    IsSolutionOn (I := I)
      ({ base := { metric := co.gInf } } :
        SolutionOn (I := I) (M := P.M) X.D) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  have hgram := OpenMetricConvergenceData.gramSmooth (I := I) (Φ := Φ) ht₀ hD co
  have hsmooth : MetricFamilySmoothOn (I := I) (M := P.M) X.D
      ({ base := { metric := co.gInf } } :
        SolutionOn (I := I) (M := P.M) X.D).family.metric := by
    exact hD.symm ▸
      OpenMetricConvergenceData.smoothMetric_of_convergence (I := I) (Φ := Φ) ht₀ hD co
  have hpde : ∀ t ∈ X.D.regular, ∀ (x : P.M) (v w : TangentSpace I x),
      HasDerivAt (fun s : Real => (co.gInf s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (co.gInf t) x v w) t :=
    fun t ht x v w => OpenMetricConvergenceData.gInf_pde (I := I) (Φ := Φ) ht₀ hD co
      cLow hcLow hbound hcovTail ht x v w
  have hscalarCont : ContinuousOn
      (fun q : Real × P.M => metricScalarAt (I := I) (co.gInf q.1) q.2)
      (X.D.carrier ×ˢ (Set.univ : Set P.M)) := by
    simpa only [hD, RealTimeInterval.openInterval] using
      (DifferentialGeometry.PDE.RicciFlow.scalarCont_interior_of_chartGram
        (I := I) co.gInf a b hgram)
  have hscalarTime : ∀ t ∈ X.D.carrier, ∀ x : P.M,
      DifferentiableWithinAt Real
        (fun s : Real => metricScalarAt (I := I) (co.gInf s) x) X.D.carrier t := by
    intro t ht x
    have htOpen : t ∈ Set.Ioo a b := by
      simpa only [hD, RealTimeInterval.openInterval] using ht
    simpa only [hD, RealTimeInterval.openInterval] using
      (DifferentialGeometry.PDE.RicciFlow.scalarTime_interior_of_chartGram
        (I := I) co.gInf a b hgram t htOpen x)
  have hricciCont : tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 2 X.D.carrier
      (fun t x => metricRicciAt (I := I) (co.gInf t) x) := by
    simpa only [hD, RealTimeInterval.openInterval] using
      (DifferentialGeometry.PDE.RicciFlow.ricciCont_interior_of_chartGram
        (I := I) co.gInf a b hgram)
  have hrm04Cont : tensor0SFamilyContinuousOnSet (I := I) (M := P.M) 4 X.D.carrier
      (fun t x => metricRm04At (I := I) (co.gInf t) x) := by
    simpa only [hD, RealTimeInterval.openInterval] using
      (DifferentialGeometry.PDE.RicciFlow.rm04Cont_interior_of_chartGram
        (I := I) co.gInf a b hgram)
  exact DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_regularity (I := I)
    co.gInf hsmooth hpde hscalarCont hscalarTime hricciCont hrm04Cont

end OpenMetricConvergenceData

noncomputable def flowUpgradeOfOpen
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (P : PointedRiemannianManifold (I := I))
    (hPlim : P = mc.limit)
    (hPL : L.atTime (I := I) 0 = P)
    (Φ : PointedCGHMaps (I := I) X P mc.subseq)
    (R :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ)
    (hsrc : SourceIsSigmaCompact (I := I) Φ)
    (htgt : TargetIsSigmaCompact (I := I) Φ)
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b t₀ ht₀)
    (co : OpenMetricConvergenceData (I := I) Φ R bf hsrc htgt a b t₀)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t : Real, t ∈ X.D.carrier →
        HEq (L.S.family.metric t) (co.gInf t))
    (scalar : ScalarPullbackTendsto (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ)))
    (ricciNorm : RicNormPullback (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ))) :
    FlowUpgrade (I := I) X mc := by
  have hL0 : L.atTime (I := I) 0 = mc.limit := hPL.trans hPlim
  subst hPL
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (L.atTime 0).M := L.topology
  letI : ChartedSpace H (L.atTime 0).M := L.charted
  letI : T2Space (L.atTime 0).M := L.t2
  letI : IsManifold I ∞ (L.atTime 0).M := L.smooth
  letI : SigmaCompactSpace (L.atTime 0).M := L.sigmaCompact
  have hLm : ∀ t : Real, t ∈ X.D.carrier →
      L.S.family.metric t = co.gInf t :=
    fun t ht => eq_of_heq (hLmetric t ht)
  have hscalar : ScalarPullbackTendsto (I := I) (Φ.compSubseq co.φ co.hφ) := scalar
  have hricciNorm : RicNormPullback (I := I) (Φ.compSubseq co.φ co.hφ) := ricciNorm
  set mc' := mc.compSubseq co.φ co.hφ with hmc'
  set Φ' := Φ.compSubseq co.φ co.hφ with hΦ'
  have hσsource' : ∀ k : Nat, IsSigmaCompact (Φ'.source k) :=
    fun k => Geometry.isSigmaCompact_of_isOpen I
      (PointedCGHMaps.source_open (I := I) Φ' k)
  refine ⟨co.φ, co.hφ, ?_⟩
  change FlowLimitData (I := I) X mc'
  refine
    { L := L
      hL0 := by simpa [mc'] using hL0
      maps := Φ'
      scalar := hscalar
      ricciNorm := hricciNorm
      hσsource := hσsource'
      hσtarget := ?_
      refMetric := ?_
      convergence := ?_ }
  · intro k
    let : TopologicalSpace (X.term (mc'.subseq k)).M :=
      (X.term (mc'.subseq k)).topology
    let : ChartedSpace H (X.term (mc'.subseq k)).M :=
      (X.term (mc'.subseq k)).charted
    let : SigmaCompactSpace (X.term (mc'.subseq k)).M :=
      (X.term (mc'.subseq k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I
      (PointedCGHMaps.target_open (I := I) Φ' k)
  · intro k
    exact fun _ => sourceMetricRestriction (I := I) Φ' R k
  · intro K hK p c d hcd ε hε
    have hcdOpen : Set.Icc c d ⊆ Set.Ioo a b := by
      intro t ht
      simpa only [hD, RealTimeInterval.openInterval] using hcd ht
    obtain ⟨n, hn⟩ := RealTimeInterval.exists_window_superset ht₀ hcdOpen
    let coN := OpenMetricConvergenceData.atWindow Φ co n
    have hLmN : ∀ t : Real,
        t ∈ Set.Icc (RealTimeInterval.openWindowLeft a t₀ n)
          (RealTimeInterval.openWindowRight b t₀ n) →
        L.S.family.metric t = coN.gInf t := by
      intro t ht
      change L.S.family.metric t = co.gInf t
      apply hLm t
      have htOpen := RealTimeInterval.openWindow_subset ht₀ n ht
      simpa only [hD, RealTimeInterval.openInterval] using htOpen
    have hbridge := ofRP_supOn_convergence (I := I) Φ R bf hsrc htgt
      (RealTimeInterval.openWindowLeft a t₀ n)
      (RealTimeInterval.openWindowRight b t₀ n) coN
      (letI : TopologicalSpace L.M := L.topology;
        letI : ChartedSpace H L.M := L.charted;
        letI : IsManifold I ∞ L.M := L.smooth;
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
          change IsManifold I ∞ L.M
          infer_instance
        letI : SigmaCompactSpace L.M := L.sigmaCompact;
        letI : T2Space L.M := L.t2;
        L.S.family.metric) hLmN K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := hbridge
    refine ⟨k₀, fun k hk t ht => ?_⟩
    exact hk₀ k hk t (hn ht)

omit [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] in
theorem flowUpgrade_open_L
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (P : PointedRiemannianManifold (I := I))
    (hPlim : P = mc.limit)
    (hPL : L.atTime (I := I) 0 = P)
    (Φ : PointedCGHMaps (I := I) X P mc.subseq)
    (R :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ)
    (hsrc : SourceIsSigmaCompact (I := I) Φ)
    (htgt : TargetIsSigmaCompact (I := I) Φ)
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b t₀ ht₀)
    (co : OpenMetricConvergenceData (I := I) Φ R bf hsrc htgt a b t₀)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t : Real, t ∈ X.D.carrier →
        HEq (L.S.family.metric t) (co.gInf t))
    (scalar : ScalarPullbackTendsto (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ)))
    (ricciNorm : RicNormPullback (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ))) :
    (flowUpgradeOfOpen (I := I) mc L P hPlim hPL Φ R bf hsrc htgt ht₀ hD co
      hLmetric scalar ricciNorm).data.L = L := by
  cases hPL
  rfl

omit [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] in
theorem flowLimit_of_open
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (P : PointedRiemannianManifold (I := I))
    (hPlim : P = mc.limit)
    (hPL : L.atTime (I := I) 0 = P)
    (Φ : PointedCGHMaps (I := I) X P mc.subseq)
    (R :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ)
    (hsrc : SourceIsSigmaCompact (I := I) Φ)
    (htgt : TargetIsSigmaCompact (I := I) Φ)
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b t₀ ht₀)
    (co : OpenMetricConvergenceData (I := I) Φ R bf hsrc htgt a b t₀)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t : Real, t ∈ X.D.carrier →
        HEq (L.S.family.metric t) (co.gInf t))
    (scalar : ScalarPullbackTendsto (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ)))
    (ricciNorm : RicNormPullback (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ))) :
    compactnessConclusion (I := I) X :=
  (flowUpgradeOfOpen (I := I) mc L P hPlim hPL Φ R bf hsrc htgt ht₀ hD co
    hLmetric scalar ricciNorm).toConclusion

end CheegerGromovCompactness
end DifferentialGeometry
