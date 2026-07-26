import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDCanonP4
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.OpenWindowEquiv
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MovingShiOpen
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.SourceCovLip
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldOpenAssembly

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical open-flow upgrade producer

This module is the readable meeting point of the concrete Step-D provenance
lane and the open-window analytic lane.  It keeps the canonical metric
conclusion, comparison maps, bump family, window data, source estimates, and
raw open-window inputs visible before invoking `open_upgrade_of_raw`.

No claim is made for an arbitrary `MetricCompactnessConclusion`: the time-zero
reference and covariant data come specifically from `StepDCanonData`.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.Connection

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}

/-- Produce the open Ricci-flow upgrade from the concrete canonical Step-D
sidecar, completeness, and the sequence curvature bound.  The analytic
producers remain separate: canonical-window metric equivalence, complete Shi,
and the constants-first varying-source covariant/Lipschitz theorem are called
explicitly before the grow-local raw inputs are assembled. -/
theorem open_upgrade_canon
    (canon : StepDCanonData (I := I) (X.atZero (I := I)))
    {a b : Real} (hzero : (0 : Real) ∈ Set.Ioo a b)
    (hD : X.D = RealTimeInterval.openInterval a b 0 hzero)
    (hcomplete : CompleteInput (I := I) X)
    (hcurv : CurvBoundInput (I := I) X) :
    ∃ d : FlowUpgradeData (I := I) X canon.mc,
      ∀ t : Real, t ∈ X.D.carrier →
        MetricComplete (I := I) (d.data.L.atTime (I := I) t) := by
  classical
  let mc := canon.mc
  let Phi := pointedCGHMaps_of_manifold (I := I) X
    mc.limit mc.subseq mc.maps
  letI : TopologicalSpace mc.limit.M := mc.limit.topology
  letI : ChartedSpace H mc.limit.M := mc.limit.charted
  letI : T2Space mc.limit.M := mc.limit.t2
  letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
  letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact

  have hsrc : SrcSigma (I := I) Phi := by
    intro k
    exact Geometry.isSigmaCompact_of_isOpen I
      (PointedCGHMaps.source_open (I := I) Phi k)
  have htgt : TgtSigma (I := I) Phi := by
    intro k
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I
      (PointedCGHMaps.target_open (I := I) Phi k)
  let bf := Classical.choice (nonempty_bumpFamily (I := I) Phi)

  let gRefT : ∀ k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).charted
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).smooth
      SmoothRiemannianMetric I (X.term (mc.subseq k)).M :=
    fun k =>
      letI : TopologicalSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).charted
      letI : T2Space (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).t2
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).smooth
      letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).sigmaCompact
      (X.term (mc.subseq k)).S.family.metric 0

  have hcanonRel := StepDCanonData.canon_rel (I := I) canon hsrc htgt
  dsimp only at hcanonRel
  obtain ⟨Crel, hCrel, hrelZero⟩ := hcanonRel
  have hsrcZero (k : Nat) :
      tgtRefSrc (I := I) Phi gRefT hsrc htgt k =
        srcMetric (I := I) Phi hsrc htgt k 0 := by
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : T2Space (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).t2
    letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).smooth
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    rfl
  have hrel : ∀ k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
        sourceDomTop (I := I) Phi k
      letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
        sourceDomCharted (I := I) Phi k
      letI : T2Space (SourceDomain (I := I) Phi k) :=
        sourceDomT2 (I := I) Phi k
      letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
        sourceDomSmooth (I := I) Phi k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Phi k))
        (refRes (I := I) Phi mc.limit.metric hsrc k)
        (tgtRefSrc (I := I) Phi gRefT hsrc htgt k) Crel := by
    intro k
    rw [hsrcZero k]
    exact hrelZero k
  have hinit := StepDCanonData.canon_init (I := I) canon hsrc htgt
  dsimp only at hinit
  have hcp := StepDCanonData.canon_cp (I := I) canon hsrc htgt
  dsimp only at hcp

  let beta : Nat → Real := fun n => RealTimeInterval.openWindowLeft a 0 n
  let psi : Nat → Real := fun n => RealTimeInterval.openWindowRight b 0 n
  have hwindow : ∀ n : Nat, ∃ A Bmax : Real,
      0 ≤ A ∧ 1 ≤ Bmax ∧
        (∀ t : Real, t ∈ Set.Icc (beta n) (psi n) →
          metricEquivalenceFactor 1 A t 0 ≤ Bmax) ∧
        ∀ k : Nat,
          letI : TopologicalSpace (X.term k).M := (X.term k).topology
          letI : ChartedSpace H (X.term k).M := (X.term k).charted
          letI : T2Space (X.term k).M := (X.term k).t2
          letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
          letI : SigmaCompactSpace (X.term k).M := (X.term k).sigmaCompact
          MetricUniformEquivalentOnWindow (I := I) Set.univ
            (beta n) (psi n) ((X.term k).S.family.metric 0)
            (fun _ t => (X.term k).S.family.metric t)
            (fun t => metricEquivalenceFactor 1 A t 0) := by
    intro n
    simpa only [beta, psi] using
      CurvBoundInput.metricEquiv_open (I := I) hzero X hD hcurv n
  choose A Bmax hwindowData using hwindow
  let B : Nat → Real → Real := fun n t =>
    metricEquivalenceFactor 1 (A n) t 0
  have hA (n : Nat) : 0 ≤ A n := (hwindowData n).1
  have hBmax (n : Nat) : 1 ≤ Bmax n := (hwindowData n).2.1
  have hBmajor (n : Nat) : ∀ t : Real, t ∈ Set.Icc (beta n) (psi n) →
      B n t ≤ Bmax n := by
    simpa only [B] using (hwindowData n).2.2.1
  have hequivT (n : Nat) : ∀ k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).charted
      letI : T2Space (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).t2
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).smooth
      letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
        (X.term (mc.subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Phi.target k)
        (beta n) (psi n) (gRefT k)
        (fun _ t => (X.term (mc.subseq k)).S.family.metric t) (B n) := by
    intro k
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    letI : ChartedSpace H (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).charted
    letI : T2Space (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).t2
    letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).smooth
    letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).sigmaCompact
    have hall := (hwindowData n).2.2.2 (mc.subseq k)
    have hrestricted := metricUniformEquivalentOnWindow_mono (I := I)
      (Set.subset_univ (Phi.target k)) hall
    simpa only [gRefT, B] using hrestricted

  have hzeroWindow (n : Nat) : (0 : Real) ∈ Set.Icc (beta n) (psi n) := by
    simpa only [beta, psi, RealTimeInterval.openWindow] using
      RealTimeInterval.initial_mem_window hzero n
  have hbetaPsi (n : Nat) : beta n ≤ psi n :=
    (hzeroWindow n).1.trans (hzeroWindow n).2
  have hregular (n : Nat) : Set.Icc (beta n) (psi n) ⊆ X.D.regular := by
    intro t ht
    rw [hD]
    exact RealTimeInterval.openWindow_subset hzero n ht

  have hShiT (n N : Nat) : ∃ KShi : Real, 0 ≤ KShi ∧
      ∀ k : Nat,
        letI : TopologicalSpace (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).topology
        letI : ChartedSpace H (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).charted
        letI : T2Space (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).t2
        letI : IsManifold I ∞ (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).smooth
        letI : SigmaCompactSpace (X.term (mc.subseq k)).M :=
          (X.term (mc.subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Phi.target k) (beta n) (psi n)
          (fun _ t => (X.term (mc.subseq k)).S.family.metric t) N KShi := by
    obtain ⟨KShi, hKShi, hShiAll⟩ :=
      CurvBoundInput.movingShi_open (I := I) hzero X hD hcomplete hcurv n N
    refine ⟨KShi, hKShi, ?_⟩
    intro k
    have hk := hShiAll (mc.subseq k)
    intro s hs i t ht x _hx
    exact hk s hs i t ht x (Set.mem_univ x)
  have hShiSrc (n : Nat) : ∀ N : Nat, ∃ KShi : Real, 0 ≤ KShi ∧
      ∀ k : Nat,
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
        MovingShiBoundOn (I := I)
          (Set.univ : Set (SourceDomain (I := I) Phi k))
          (beta n) (psi n)
          (fun _ t => srcMetric (I := I) Phi hsrc htgt k t) N KShi := by
    intro N
    obtain ⟨KShi, hKShi, hShi⟩ := hShiT n N
    exact ⟨KShi, hKShi, fun k =>
      srcShi (I := I) Phi hsrc htgt (beta n) (psi n) N KShi hShi k⟩

  have hBsrc (n : Nat) : 1 ≤ Crel * Bmax n := by
    exact one_le_mul_of_one_le_of_one_le hCrel (hBmax n)
  have hequivSrc (n : Nat) : ∀ k : Nat,
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
      ∀ t : Real, t ∈ Set.Icc (beta n) (psi n) →
        MetricUniformEquivalentOn (I := I)
          (Set.univ : Set (SourceDomain (I := I) Phi k))
          (refRes (I := I) Phi mc.limit.metric hsrc k)
          (srcMetric (I := I) Phi hsrc htgt k t) (Crel * Bmax n) := by
    intro k t ht
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
    have hEq := srcEquivOn (I := I) Phi mc.limit.metric hsrc htgt
      (beta n) (psi n) gRefT (B n) Crel (hequivT n) hrel k t ht
    exact metricUniformEquivalentOn_of_le (I := I) hEq
      (mul_le_mul_of_nonneg_left (hBmajor n t ht) (zero_le_one.trans hCrel))

  have srcData (n : Nat) : SrcCovLipData (I := I) Phi mc.limit.metric
      hsrc htgt (beta n) (psi n) :=
    srcCovLip_of_soln (I := I) Phi mc.limit.metric hsrc htgt
      (hbetaPsi n) (hzeroWindow n) (hregular n)
      (Crel * Bmax n) (hBsrc n) (hequivSrc n) (hShiSrc n) hinit

  let cLow : Nat → Real := fun n => (Crel * Bmax n)⁻¹
  have hcLow (n : Nat) : 0 < cLow n := by
    exact inv_pos.mpr (zero_lt_one.trans_le (hBsrc n))
  have hbound : ∀ n k : Nat, ∀ t : Real,
      t ∈ RealTimeInterval.openWindow a b 0 n →
      ∀ (y : SourceDomain (I := I) Phi k)
        (v : letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
              sourceDomTop (I := I) Phi k
          letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
              sourceDomCharted (I := I) Phi k
          TangentSpace I y),
        cLow n * mc.limit.metric.inner (y : mc.limit.M) v v ≤
          letI : TopologicalSpace (SourceDomain (I := I) Phi k) :=
            sourceDomTop (I := I) Phi k
          letI : ChartedSpace H (SourceDomain (I := I) Phi k) :=
            sourceDomCharted (I := I) Phi k
          letI : IsManifold I ∞ (SourceDomain (I := I) Phi k) :=
            sourceDomSmooth (I := I) Phi k
          (srcMetric (I := I) Phi hsrc htgt k t).inner y v v := by
    intro n k t ht y v
    have ht' : t ∈ Set.Icc (beta n) (psi n) := by
      simpa only [beta, psi, RealTimeInterval.openWindow] using ht
    simpa only [cLow] using
      (hbound_of_equiv (I := I) Phi mc.limit.metric hsrc htgt
        (beta n) (psi n) gRefT (B n) Crel (Bmax n)
        (hBmajor n) hCrel (hequivT n) hrel k t ht' y v)

  have hcovTail : ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real),
      t ∈ RealTimeInterval.openWindow a b 0 n →
      ∀ z : mc.limit.M, z ∈ bf.grow k →
        metricCovDerivNorm (I := I) q
          (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt k t)
          mc.limit.metric z ≤ C := by
    intro n
    have hcovSrc : ∀ q : Nat, ∃ C : Real, 0 ≤ C ∧
        ∀ (k : Nat) (t : Real), t ∈ Set.Icc (beta n) (psi n) →
          ∀ y : SourceDomain (I := I) Phi k, (y : mc.limit.M) ∈ bf.grow k →
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
            metricCovDerivNorm (I := I) q
              (srcMetric (I := I) Phi hsrc htgt k t)
              (refRes (I := I) Phi mc.limit.metric hsrc k) y ≤ C := by
      intro q
      obtain ⟨C, hC, hboundC⟩ := (srcData n).cov q
      exact ⟨C, hC, fun k t ht y _ => hboundC k t ht y⟩
    have hcov := covTail_of_bounds (I := I) Phi mc.limit.metric bf hsrc htgt
      (beta n) (psi n) hcovSrc
    intro q
    obtain ⟨C, hC⟩ := hcov q
    exact ⟨C, fun k t ht z hz => hC k t (by
      simpa only [beta, psi, RealTimeInterval.openWindow] using ht) z hz⟩

  have hlipTail : ∀ n p : Nat, ∃ Lt : Real, 0 ≤ Lt ∧
      ∀ (k : Nat) (s t : Real),
        s ∈ RealTimeInterval.openWindow a b 0 n →
        t ∈ RealTimeInterval.openWindow a b 0 n →
        ∀ q : Nat, q ≤ p → ∀ z : mc.limit.M, z ∈ bf.grow k →
          metricDerivNorm (I := I) q
            (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt k s)
            (gSeqExt (I := I) Phi mc.limit.metric bf hsrc htgt k t)
            mc.limit.metric z ≤ Lt * |s - t| := by
    intro n
    have hlipG : ∀ p : Nat, ∃ Lt : Real, 0 ≤ Lt ∧
        ∀ (k : Nat) (s t : Real),
          s ∈ Set.Icc (beta n) (psi n) → t ∈ Set.Icc (beta n) (psi n) →
          ∀ q : Nat, q ≤ p →
            ∀ y : SourceDomain (I := I) Phi k, (y : mc.limit.M) ∈ bf.grow k →
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
              metricDerivNorm (I := I) q
                (srcMetric (I := I) Phi hsrc htgt k s)
                (srcMetric (I := I) Phi hsrc htgt k t)
                (refRes (I := I) Phi mc.limit.metric hsrc k) y ≤ Lt * |s - t| := by
      intro p
      obtain ⟨Lt, hLt, hlip⟩ := (srcData n).lip p
      exact ⟨Lt, hLt, fun k s t hs ht q hq y _ =>
        hlip k s t hs ht q hq y⟩
    have hlip := lipTail_of_src (I := I) Phi mc.limit.metric bf hsrc htgt
      (beta n) (psi n) hlipG
    intro p
    obtain ⟨Lt, hLt, hlipLt⟩ := hlip p
    refine ⟨Lt, hLt, ?_⟩
    intro k s t hs ht q hq z hz
    exact hlipLt k s t
      (by simpa only [beta, psi, RealTimeInterval.openWindow] using hs)
      (by simpa only [beta, psi, RealTimeInterval.openWindow] using ht)
      q hq z hz

  have hlipSrc : ∀ n k : Nat,
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
      letI : T2Space ↥(sourceOpen (I := I) Phi k) :=
        sourceDomT2 (I := I) Phi k
      ∀ C : Set (SourceDomain (I := I) Phi k), IsCompact C → ∀ p : Nat,
        ∃ Ls : Real, 0 ≤ Ls ∧
          ∀ (s t : Real), s ∈ RealTimeInterval.openWindow a b 0 n →
            t ∈ RealTimeInterval.openWindow a b 0 n →
            ∀ q : Nat, q ≤ p →
              ∀ y : SourceDomain (I := I) Phi k, y ∈ C →
                metricDerivNorm (I := I) q
                  (srcMetric (I := I) Phi hsrc htgt k s)
                  (srcMetric (I := I) Phi hsrc htgt k t)
                  (refRes (I := I) Phi mc.limit.metric hsrc k) y ≤
                    Ls * |s - t| := by
    intro n k C _hC p
    obtain ⟨Ls, hLs, hlip⟩ := (srcData n).lip p
    refine ⟨Ls, hLs, ?_⟩
    intro s t hs ht q hq y _hy
    exact hlip k s t
      (by simpa only [beta, psi, RealTimeInterval.openWindow] using hs)
      (by simpa only [beta, psi, RealTimeInterval.openWindow] using ht)
      q hq y

  simpa only [mc] using
    (open_upgrade_of_raw (I := I) (X := X) mc Phi bf hsrc htgt
      hzero hD cLow hcLow hbound hcovTail hlipTail hlipSrc hcp)

end HCGCompactness
end DifferentialGeometry
