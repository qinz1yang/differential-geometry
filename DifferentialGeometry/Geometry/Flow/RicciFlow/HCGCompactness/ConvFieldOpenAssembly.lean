import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpenEndgame
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpenZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpenComplete

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Open-window flow-upgrade assembly

This module is the concrete P4 capstone after the raw compact-window estimates
have been produced.  It selects the common open-window limit, constructs the
limit Ricci flow, identifies its time-zero slice, assembles `FlowUpgradeData`,
and proves completeness of every limit time slice.
-/

noncomputable section

open Set Function Filter Bundle Manifold Tensor0SBundle
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

/-- Assemble a concrete smooth flow upgrade, together with completeness of all
its time slices, from the four raw open-window estimates and the time-zero
metric convergence witness aligned with the chosen comparison maps. -/
theorem open_upgrade_of_raw
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (Phi : PointedCGHMaps (I := I) X mc.limit mc.subseq)
    (bf : BumpFamily (I := I) Phi)
    (hsrc : SrcSigma (I := I) Phi) (htgt : TgtSigma (I := I) Phi)
    {a b : Real} (hzero_mem : (0 : Real) ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b 0 hzero_mem)
    (cLow : Nat -> Real) (hcLow : forall n, 0 < cLow n)
    (hbound : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      forall n k : Nat, forall t : Real,
        t ∈ RealTimeInterval.openWindow a b 0 n ->
        forall (y : SourceDomain (I := I) Phi k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
                sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
                sourceDomCharted (I := I) Phi k
            TangentSpace I y),
          cLow n * mc.limit.metric.inner (y : mc.limit.M) v v <=
            letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
            letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
            letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
            (srcMetric (I := I) Phi hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      forall n q : Nat, exists C : Real, forall (k : Nat) (t : Real),
        t ∈ RealTimeInterval.openWindow a b 0 n ->
        forall z : mc.limit.M, z ∈ bf.grow k ->
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt k t)
              mc.limit.metric z <= C)
    (hlipTail : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      forall n p : Nat, exists Lt : Real, 0 <= Lt /\
        forall (k : Nat) (s t : Real),
          s ∈ RealTimeInterval.openWindow a b 0 n ->
          t ∈ RealTimeInterval.openWindow a b 0 n ->
          forall q : Nat, q <= p -> forall z : mc.limit.M, z ∈ bf.grow k ->
            metricDerivNorm (I := I) q
              (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt k s)
              (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt k t)
              mc.limit.metric z <= Lt * |s - t|)
    (hlipSrc : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      forall n k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
          sourceDomTop (I := I) Phi k
        letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
          sourceDomCharted (I := I) Phi k
        letI : T2Space (SourceDomain (I := I) Phi k) :=
          sourceDomT2 (I := I) Phi k
        letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
          sourceDomSmooth (I := I) Phi k
        letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
          sourceDomSigmaOf (I := I) Phi k (hsrc k)
        letI : SigmaCompactSpace ↥(sourceOpen (I := I) Phi k) :=
          sourceDomSigmaOf (I := I) Phi k (hsrc k)
        letI : T2Space ↥(sourceOpen (I := I) Phi k) := sourceDomT2 (I := I) Phi k
        forall C : Set (SourceDomain (I := I) Phi k), IsCompact C -> forall p : Nat,
          exists Ls : Real, 0 <= Ls /\
            forall (s t : Real),
              s ∈ RealTimeInterval.openWindow a b 0 n ->
              t ∈ RealTimeInterval.openWindow a b 0 n ->
              forall q : Nat, q <= p ->
                forall y : SourceDomain (I := I) Phi k, y ∈ C ->
                  metricDerivNorm (I := I) q
                    (srcMetric (I := I) Phi hsrc htgt k s)
                    (srcMetric (I := I) Phi hsrc htgt k t)
                    (refRes (I := I) Phi mc.limit.metric hsrc k) y <=
                      Ls * |s - t|)
    (hcp : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      forall K : Set mc.limit.M, IsCompact K -> forall eps : Real, 0 < eps ->
        exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Phi.source k /\
          (letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
           letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
           letI : T2Space (SourceDomain (I := I) Phi k) := sourceDomT2 (I := I) Phi k
           letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
              sourceDomSmooth (I := I) Phi k
           letI : SigmaCompactSpace (SourceDomain (I := I) Phi k) :=
              sourceDomSigmaOf (I := I) Phi k (hsrc k)
           metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Phi k K) 0
             (srcMetric (I := I) Phi hsrc htgt k 0)
             (resSrc (I := I) Phi hsrc k mc.limit.metric)
             (refRes (I := I) Phi mc.limit.metric hsrc k) < eps)) :
    exists d : FlowUpgradeData (I := I) X mc,
      forall t : Real, t ∈ X.D.carrier ->
        MetricComplete (I := I) (d.data.L.atTime (I := I) t) := by
  letI : TopologicalSpace mc.limit.M := mc.limit.topology
  letI : ChartedSpace H mc.limit.M := mc.limit.charted
  letI : T2Space mc.limit.M := mc.limit.t2
  letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
  letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
  letI : IsManifold I 1 mc.limit.M :=
    IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) <= ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
    change IsManifold I ∞ mc.limit.M
    infer_instance
  obtain ⟨co⟩ := exists_openConv_raw (I := I) (Φ := Phi)
    (R := mc.limit.metric) (bf := bf) (hsrc := hsrc) (htgt := htgt)
    hzero_mem cLow hcLow hbound hcovTail hlipTail hlipSrc
  have hsol := OpenConvOut.isSolution (I := I) (Φ := Phi)
    hzero_mem hD co cLow hcLow hbound hcovTail
  have hzero : co.gInf 0 = mc.limit.metric :=
    OpenConvOut.gInf_zero_eq (I := I) Phi mc.limit.metric bf hsrc htgt co
      hzero_mem mc.limit.metric
      (conv0_of_cp (I := I) Phi mc.limit.metric hsrc htgt mc.limit.metric hcp)
  let L := flowOfMetric (I := I) X.D mc.limit co.gInf hsol
  have hL0 : L.atTime (I := I) 0 = mc.limit :=
    flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero
  have hscalarRaw := OpenConvOut.scalar_conv (I := I) (Φ := Phi)
    hzero_mem hD co cLow hcLow hbound hcovTail
  have hricRaw := OpenConvOut.ricNorm_conv (I := I) (Φ := Phi)
    hzero_mem hD co cLow hcLow hbound hcovTail
  have map_cast {P Q : PointedRiemannianManifold (I := I)}
      {s : Nat -> Nat} (h : P = Q) (maps : PointedCGHMaps (I := I) X Q s)
      (k : Nat) (x : P.M) :
      HEq ((h.symm ▸ maps : PointedCGHMaps (I := I) X P s).map k x)
        (maps.map k (h ▸ x)) := by
    cases h
    rfl
  have hmap (k : Nat) (x : mc.limit.M) :
      (hL0.symm ▸ (Phi.compSubseq co.φ co.hφ) : PointedCGHMaps (I := I) X
        (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)).map k x =
        (Phi.compSubseq co.φ co.hφ).map k x := by
    have hx : hL0 ▸ x = x :=
      eq_of_heq ((eqRec_heq
        (φ := fun Q : PointedRiemannianManifold (I := I) => Q.M) hL0) x)
    exact (eq_of_heq (map_cast hL0 (Phi.compSubseq co.φ co.hφ) k x)).trans
      (congrArg (fun y => (Phi.compSubseq co.φ co.hφ).map k y) hx)
  have scalar : ScalarPullbackTendsto (I := I)
      (hL0.symm ▸ (Phi.compSubseq co.φ co.hφ) : PointedCGHMaps (I := I) X
        (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)) := by
    unfold ScalarPullbackTendsto FunctionPullbackTendsto
    intro t ht x
    change mc.limit.M at x
    change Filter.Tendsto _ Filter.atTop
      (nhds (metricScalarAt (I := I) (co.gInf t) x))
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun k => ?_))
      (hscalarRaw t ht x)
    letI : TopologicalSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).topology
    letI : ChartedSpace H (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).charted
    letI : IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).smooth
    letI : SigmaCompactSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).sigmaCompact
    letI : T2Space (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).t2
    letI : IsManifold I 1 (X.term ((mc.subseq ∘ co.φ) k)).M :=
      IsManifold.of_le (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (X.term ((mc.subseq ∘ co.φ) k)).M := by
      change IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M
      infer_instance
    exact congrArg
      (fun y => (X.term ((mc.subseq ∘ co.φ) k)).S.scalar t y) (hmap k x).symm
  have ricciNorm : RicNormPullback (I := I)
      (hL0.symm ▸ (Phi.compSubseq co.φ co.hφ) : PointedCGHMaps (I := I) X
        (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)) := by
    unfold RicNormPullback FunctionPullbackTendsto
    intro t ht x
    change mc.limit.M at x
    change Filter.Tendsto _ Filter.atTop
      (nhds (normSq0S (I := I) (co.gInf t) x 2
        (metricRicci (I := I) (co.gInf t) x)))
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun k => ?_))
      (hricRaw t ht x)
    letI : TopologicalSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).topology
    letI : ChartedSpace H (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).charted
    letI : IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).smooth
    letI : SigmaCompactSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).sigmaCompact
    letI : T2Space (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).t2
    letI : IsManifold I 1 (X.term ((mc.subseq ∘ co.φ) k)).M :=
      IsManifold.of_le (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (X.term ((mc.subseq ∘ co.φ) k)).M := by
      change IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M
      infer_instance
    exact congrArg
      (fun y => DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
        (X.term ((mc.subseq ∘ co.φ) k)).S t y) (hmap k x).symm
  let d := flowUpgrade_of_open (I := I) mc L mc.limit rfl hL0 Phi
    mc.limit.metric bf hsrc htgt hzero_mem hD co (fun _ _ => HEq.rfl) scalar
    ricciNorm
  refine ⟨d, ?_⟩
  intro t ht
  have htOpen : t ∈ Set.Ioo a b := by
    simpa only [hD, RealTimeInterval.openInterval] using ht
  have hcExt : forall n : Nat, 0 < min (cLow n) 1 :=
    fun n => lt_min (hcLow n) one_pos
  have hseq : forall (n k : Nat) (s : Real),
      s ∈ RealTimeInterval.openWindow a b 0 n ->
        forall (x : mc.limit.M) (v : TangentSpace I x),
          min (cLow n) 1 * mc.limit.metric.inner x v v <=
            (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt (co.φ k) s).inner x v v := by
    intro n k s hs x v
    exact gSeqExt_lower (I := I) Phi mc.limit.metric bf hsrc htgt
      (cLow n) (RealTimeInterval.openWindowLeft a 0 n)
      (RealTimeInterval.openWindowRight b 0 n) (hcLow n)
      (fun j u hu => hbound n j u hu) (co.φ k) s hs x v
  have hcomplete := OpenConvOut.complete_at (I := I) Phi mc.limit_complete co
    (fun n => min (cLow n) 1) hcExt hseq htOpen
  have hdL : d.data.L = L := by
    exact flowUpgrade_open_L (I := I) mc L mc.limit rfl hL0 Phi
      mc.limit.metric bf hsrc htgt hzero_mem hD co (fun _ _ => HEq.rfl) scalar
      ricciNorm
  rw [hdL]
  change MetricComplete (I := I)
    ({ mc.limit with metric := co.gInf t } : PointedRiemannianManifold (I := I))
  exact hcomplete

end HCGCompactness
end DifferentialGeometry

end
