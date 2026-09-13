import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.FlowLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Completeness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FlowOfMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.FlowConvergence

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace HalfLineMetricConvergenceData

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem metricComplete
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hR : MetricComplete (I := I)
      ({ P with metric := R } : PointedRiemannianManifold (I := I)))
    (hcarrier : X.D.carrier ⊆ Set.Iic 0)
    (c : Nat → Real) (hc : ∀ n, 0 < c n)
    (hseq : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (n k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ (x : P.M) (v : TangentSpace I x),
          c n * R.inner x v v ≤
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t).inner x v v)
    {t : Real} (ht : t ∈ X.D.carrier) :
    MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  obtain ⟨n, hn⟩ : ∃ n : Nat, t ∈ Set.Icc (-(n : Real)) 0 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (-t)
    exact ⟨n, ⟨by linarith, hcarrier ht⟩⟩
  let coN := HalfLineMetricConvergenceData.atWindow Φ co n
  have hlow := (FlowMetricConvergenceData.lower_of (I := I) (Φ := Φ) coN
    (fun k s hs => hseq n k s hs)) t hn
  exact MetricComplete.complete_of_lower (I := I)
    ({ P with metric := R } : PointedRiemannianManifold (I := I)) hR (coN.gInf t) (c n) (hc n)
    hlow

end HalfLineMetricConvergenceData

section HalfLineFlowLimit

variable {Y : PointedFlowSeq (I := I)}

noncomputable def smoothFlowLimitSubsequenceOfHalfLineMetricData
    (mc : MetricCompactLimit (I := I) (Y.atZero (I := I)))
    (L : PointedFlowData (I := I) Y.D)
    (P : PointedRiemannianManifold (I := I))
    (hPlim : P = mc.limit)
    (hPL : L.atTime (I := I) 0 = P)
    (Φ : PointedCGHMaps (I := I) Y P mc.subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact (I := I) Φ)
    (htgt : TargetIsSigmaCompact (I := I) Φ)
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : Y.D.carrier ⊆ Set.Iic 0)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t : Real, t ∈ Set.Iic 0 → HEq (L.S.family.metric t) (co.gInf t))
    (scalar : ScalarPullbackTendsto (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.strictMono) :
        PointedCGHMaps (I := I) Y (L.atTime 0) (mc.subseq ∘ co.φ)))
    (ricci : MetricRicciPullbackTendsto (I := I)
      (Φ.compSubseq co.φ co.strictMono) co.gInf)
    (ricciNorm : RicNormPullback (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.strictMono) :
        PointedCGHMaps (I := I) Y (L.atTime 0) (mc.subseq ∘ co.φ))) :
    SmoothFlowLimitSubsequence (I := I) Y mc := by
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
  have hLm : ∀ t : Real, t ∈ Set.Iic 0 → L.S.family.metric t = co.gInf t :=
    fun t ht => eq_of_heq (hLmetric t ht)
  have hmetricRaw : MetricInnerPullbackTendsto (I := I)
      (Φ.compSubseq co.φ co.strictMono) co.gInf :=
    HalfLineMetricConvergenceData.metric_convergence (I := I) Φ co hcarrier
  have hmetric : MetricPullbackTendsto (I := I) (Φ.compSubseq co.φ co.strictMono) :=
    MetricInnerPullbackTendsto.congr_metric (I := I)
      (fun t ht => (hLm t (hcarrier ht)).symm) hmetricRaw
  have hscalar : ScalarPullbackTendsto (I := I) (Φ.compSubseq co.φ co.strictMono) := scalar
  have hricci : RicciPullbackTendsto (I := I) (Φ.compSubseq co.φ co.strictMono) :=
    MetricRicciPullbackTendsto.congr_metric (I := I)
      (fun t ht => (hLm t (hcarrier ht)).symm) ricci
  have hricciNorm : RicNormPullback (I := I) (Φ.compSubseq co.φ co.strictMono) := ricciNorm
  set mc' := mc.compSubseq co.φ co.strictMono with hmc'
  set Φ' := (Φ).compSubseq co.φ co.strictMono with hΦ'
  refine ⟨co.φ, co.strictMono, ?_⟩
  change SmoothFlowLimitAlongMetricSubsequence (I := I) Y mc'
  refine
    { L := L
      atTime_zero := by simpa [mc'] using hL0
      maps := Φ'
      metric := hmetric
      scalar := hscalar
      ricci := hricci
      ricciNorm := hricciNorm
      source_sigmaCompact := ?_
      target_sigmaCompact := ?_
      refMetric := ?_
      convergence := ?_ }
  · intro k
    exact Geometry.isSigmaCompact_of_isOpen I (PointedCGHMaps.source_open (I := I) Φ' k)
  · intro k
    let : TopologicalSpace (Y.term (mc'.subseq k)).M := (Y.term (mc'.subseq k)).topology
    let : ChartedSpace H (Y.term (mc'.subseq k)).M := (Y.term (mc'.subseq k)).charted
    let : SigmaCompactSpace (Y.term (mc'.subseq k)).M := (Y.term (mc'.subseq k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (PointedCGHMaps.target_open (I := I) Φ' k)
  · intro k
    exact fun _ => sourceMetricRestriction (I := I) Φ' R k
  · intro K hK p a b hab ε hε
    by_cases hle : a ≤ b
    · have hb0 : b ≤ 0 := hcarrier (hab ⟨hle, le_rfl⟩)
      obtain ⟨n, hn⟩ := exists_nat_ge (-a)
      have hna : -(n : Real) ≤ a := by linarith
      have hsub' : Set.Icc a b ⊆ Set.Icc (-(n : Real)) 0 :=
        fun t ht => ⟨hna.trans ht.1, ht.2.trans hb0⟩
      have hLmN : ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
          L.S.family.metric t = co.gInf t :=
        fun t ht => hLm t ht.2
      have hbridge := ofRP_supOn_convergence (I := I) Φ R bf hsrc htgt (-(n : Real)) 0
        (HalfLineMetricConvergenceData.atWindow Φ co n) (L.S.family.metric) hLmN K hK p ε hε
      obtain ⟨k0, hk0⟩ := hbridge
      exact ⟨k0, fun k hk t ht => hk0 k hk t (hsub' ht)⟩
    · exact ⟨0, fun _ _ t ht => absurd (ht.1.trans ht.2) hle⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem smoothFlowLimitSubsequenceOfHalfLineMetricData_limit
    (mc : MetricCompactLimit (I := I) (Y.atZero (I := I)))
    (L : PointedFlowData (I := I) Y.D)
    (P : PointedRiemannianManifold (I := I))
    (hPlim : P = mc.limit)
    (hPL : L.atTime (I := I) 0 = P)
    (Φ : PointedCGHMaps (I := I) Y P mc.subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact (I := I) Φ)
    (htgt : TargetIsSigmaCompact (I := I) Φ)
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hcarrier : Y.D.carrier ⊆ Set.Iic 0)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      ∀ t : Real, t ∈ Set.Iic 0 → HEq (L.S.family.metric t) (co.gInf t))
    (scalar : ScalarPullbackTendsto (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.strictMono) :
        PointedCGHMaps (I := I) Y (L.atTime 0) (mc.subseq ∘ co.φ)))
    (ricci : MetricRicciPullbackTendsto (I := I)
      (Φ.compSubseq co.φ co.strictMono) co.gInf)
    (ricciNorm : RicNormPullback (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.strictMono) :
        PointedCGHMaps (I := I) Y (L.atTime 0) (mc.subseq ∘ co.φ))) :
    (smoothFlowLimitSubsequenceOfHalfLineMetricData (I := I) mc L P hPlim hPL Φ R bf hsrc htgt co
      hcarrier hLmetric scalar ricci ricciNorm).limit.L = L := by
  cases hPL
  rfl

theorem exists_complete_smooth_flow_limit_subsequence_of_halfLine_metric_bounds
    (mc : MetricCompactLimit (I := I) (Y.atZero (I := I)))
    (Φ₀ : PointedCGHMaps (I := I) Y mc.limit mc.subseq)
    (R : letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      SmoothRiemannianMetric I mc.limit.M)
    (bf : BumpFamily (I := I) Φ₀) (hsrc : SourceIsSigmaCompact (I := I) Φ₀)
    (htgt : TargetIsSigmaCompact (I := I) Φ₀)
    (co : HalfLineMetricConvergenceData (I := I) Φ₀ R bf hsrc htgt)
    (hsol : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I 1 mc.limit.M :=
          IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
            (by decide : (1 : WithTop ℕ∞) ≤ ∞)
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
          change IsManifold I ∞ mc.limit.M
          infer_instance
        DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
          ({ base := { metric := co.gInf } } :
            DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := mc.limit.M) Y.D))
    (hzero : co.gInf 0 = mc.limit.metric)
    (hR : MetricComplete (I := I)
      ({ mc.limit with metric := R } : PointedRiemannianManifold (I := I)))
    (cLow : Nat → Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      ∀ n k : Nat, ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ (y : SourceDomain (I := I) Φ₀ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) :=
                sourceDomTop (I := I) Φ₀ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) :=
                sourceDomCharted (I := I) Φ₀ k
            TangentSpace I y),
          cLow n * R.inner (y : mc.limit.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) :=
              sourceDomTop (I := I) Φ₀ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) :=
              sourceDomCharted (I := I) Φ₀ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) :=
              sourceDomSmooth (I := I) Φ₀ k
            (sourceMetric (I := I) Φ₀ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ z : mc.limit.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ₀ R bf hsrc htgt k t) R z ≤ C)
    (hcarrier : Y.D.carrier ⊆ Set.Iic 0) :
    ∃ d : SmoothFlowLimitSubsequence (I := I) Y mc,
      ∀ t ∈ Y.D.carrier, MetricComplete (I := I) (d.limit.L.atTime (I := I) t) := by
  let : TopologicalSpace mc.limit.M := mc.limit.topology
  let : ChartedSpace H mc.limit.M := mc.limit.charted
  let : T2Space mc.limit.M := mc.limit.t2
  let : IsManifold I ∞ mc.limit.M := mc.limit.smooth
  let : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
  let : IsManifold I 1 mc.limit.M :=
    IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
    change IsManifold I ∞ mc.limit.M
    infer_instance
  let L := flowOfMetric (I := I) Y.D mc.limit co.gInf hsol
  have hL0 : L.atTime (I := I) 0 = mc.limit :=
    flowOfMetric_atTime (I := I) Y.D mc.limit co.gInf hsol 0 hzero
  have hseq : ∀ (n k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
      ∀ (x : mc.limit.M) (v : TangentSpace I x),
        min (cLow n) 1 * R.inner x v v ≤
          (gSeqExt (I := I) Φ₀ R bf hsrc htgt (co.φ k) t).inner x v v := by
    intro n k t ht x v
    exact gSeqExt_lower (I := I) Φ₀ R bf hsrc htgt (cLow n) (-(n : Real)) 0 (hcLow n)
      (fun j u hu => hbound n j u hu) (co.φ k) t ht x v
  have map_cast {P Q : PointedRiemannianManifold (I := I)}
      {s : Nat → Nat} (h : P = Q) (maps : PointedCGHMaps (I := I) Y Q s)
      (k : Nat) (x : P.M) :
      HEq ((h.symm ▸ maps : PointedCGHMaps (I := I) Y P s).map k x)
        (maps.map k (h ▸ x)) := by
    cases h
    rfl
  have hmap (k : Nat) (x : mc.limit.M) :
      (hL0.symm ▸ (Φ₀.compSubseq co.φ co.strictMono) : PointedCGHMaps (I := I) Y
        (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)).map k x =
        (Φ₀.compSubseq co.φ co.strictMono).map k x := by
    have hx : hL0 ▸ x = x :=
      eq_of_heq ((eqRec_heq
        (φ := fun Q : PointedRiemannianManifold (I := I) => Q.M) hL0) x)
    exact (eq_of_heq (map_cast hL0 (Φ₀.compSubseq co.φ co.strictMono) k x)).trans
      (congrArg (fun y => (Φ₀.compSubseq co.φ co.strictMono).map k y) hx)
  have hscalarRaw := HalfLineMetricConvergenceData.scalar_convergence (I := I) Φ₀
    cLow hcLow hbound hcovTail co hcarrier
  have hricciRaw := HalfLineMetricConvergenceData.ricci_convergence (I := I) Φ₀
    cLow hcLow hbound hcovTail co hcarrier
  have hricRaw := HalfLineMetricConvergenceData.ricNorm_convergence (I := I) Φ₀
    cLow hcLow hbound hcovTail co hcarrier
  have scalar : ScalarPullbackTendsto (I := I)
      (hL0.symm ▸ (Φ₀.compSubseq co.φ co.strictMono) : PointedCGHMaps (I := I) Y
        (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)) := by
    unfold ScalarPullbackTendsto FunctionPullbackTendsto
    intro t ht x
    change mc.limit.M at x
    change Filter.Tendsto _ Filter.atTop
      (nhds (metricScalarAt (I := I) (co.gInf t) x))
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun k => ?_))
      (hscalarRaw t ht x)
    let : TopologicalSpace (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      (Y.term ((mc.subseq ∘ co.φ) k)).topology
    let : ChartedSpace H (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      (Y.term ((mc.subseq ∘ co.φ) k)).charted
    let : IsManifold I ∞ (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      (Y.term ((mc.subseq ∘ co.φ) k)).smooth
    let : SigmaCompactSpace (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      (Y.term ((mc.subseq ∘ co.φ) k)).sigmaCompact
    let : T2Space (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      (Y.term ((mc.subseq ∘ co.φ) k)).t2
    let : IsManifold I 1 (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      IsManifold.of_le (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    let : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (Y.term ((mc.subseq ∘ co.φ) k)).M := by
      change IsManifold I ∞ (Y.term ((mc.subseq ∘ co.φ) k)).M
      infer_instance
    exact congrArg
      (fun y => (Y.term ((mc.subseq ∘ co.φ) k)).S.scalar t y) (hmap k x).symm
  have ricciNorm : RicNormPullback (I := I)
      (hL0.symm ▸ (Φ₀.compSubseq co.φ co.strictMono) : PointedCGHMaps (I := I) Y
        (L.atTime (I := I) 0) (mc.subseq ∘ co.φ)) := by
    unfold RicNormPullback FunctionPullbackTendsto
    intro t ht x
    change mc.limit.M at x
    change Filter.Tendsto _ Filter.atTop
      (nhds (normSq0S (I := I) (co.gInf t) x 2
        (metricRicci (I := I) (co.gInf t) x)))
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun k => ?_))
      (hricRaw t ht x)
    let : TopologicalSpace (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      (Y.term ((mc.subseq ∘ co.φ) k)).topology
    let : ChartedSpace H (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      (Y.term ((mc.subseq ∘ co.φ) k)).charted
    let : IsManifold I ∞ (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      (Y.term ((mc.subseq ∘ co.φ) k)).smooth
    let : SigmaCompactSpace (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      (Y.term ((mc.subseq ∘ co.φ) k)).sigmaCompact
    let : T2Space (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      (Y.term ((mc.subseq ∘ co.φ) k)).t2
    let : IsManifold I 1 (Y.term ((mc.subseq ∘ co.φ) k)).M :=
      IsManifold.of_le (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    let : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (Y.term ((mc.subseq ∘ co.φ) k)).M := by
      change IsManifold I ∞ (Y.term ((mc.subseq ∘ co.φ) k)).M
      infer_instance
    exact congrArg
      (fun y => DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
        (Y.term ((mc.subseq ∘ co.φ) k)).S t y) (hmap k x).symm
  refine ⟨smoothFlowLimitSubsequenceOfHalfLineMetricData (I := I) mc L mc.limit rfl hL0 Φ₀ R
    bf hsrc htgt co hcarrier (fun _ _ => HEq.rfl) scalar hricciRaw ricciNorm, ?_⟩
  intro t ht
  rw [smoothFlowLimitSubsequenceOfHalfLineMetricData_limit (I := I) mc L mc.limit rfl hL0 Φ₀ R
    bf hsrc htgt co hcarrier (fun _ _ => HEq.rfl) scalar hricciRaw ricciNorm]
  change MetricComplete (I := I)
    ({ mc.limit with metric := co.gInf t } : PointedRiemannianManifold (I := I))
  exact HalfLineMetricConvergenceData.metricComplete (I := I) Φ₀ co hR hcarrier
    (fun n => min (cLow n) 1) (fun n => lt_min (hcLow n) one_pos) hseq ht

theorem exists_complete_smooth_flow_limit_subsequence_of_halfLine_regularity
    (mc : MetricCompactLimit (I := I) (Y.atZero (I := I)))
    (Φ₀ : PointedCGHMaps (I := I) Y mc.limit mc.subseq)
    (R : letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      SmoothRiemannianMetric I mc.limit.M)
    (bf : BumpFamily (I := I) Φ₀) (hsrc : SourceIsSigmaCompact (I := I) Φ₀)
    (htgt : TargetIsSigmaCompact (I := I) Φ₀)
    (co : HalfLineMetricConvergenceData (I := I) Φ₀ R bf hsrc htgt)
    (hzero : co.gInf 0 = mc.limit.metric)
    (hR : MetricComplete (I := I)
      ({ mc.limit with metric := R } : PointedRiemannianManifold (I := I)))
    (cLow : Nat → Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      ∀ n k : Nat, ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ (y : SourceDomain (I := I) Φ₀ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) :=
                sourceDomTop (I := I) Φ₀ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) :=
                sourceDomCharted (I := I) Φ₀ k
            TangentSpace I y),
          cLow n * R.inner (y : mc.limit.M) v v ≤
            letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) :=
              sourceDomTop (I := I) Φ₀ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) :=
              sourceDomCharted (I := I) Φ₀ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) :=
              sourceDomSmooth (I := I) Φ₀ k
            (sourceMetric (I := I) Φ₀ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc (-(n : Real)) 0 →
        ∀ z : mc.limit.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ₀ R bf hsrc htgt k t) R z ≤ C)
    (hcarrier : Y.D.carrier ⊆ Set.Iic 0)
    (hregular : Y.D.regular = Set.Iio 0)
    (hsmooth : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I 1 mc.limit.M :=
          IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
            (by decide : (1 : WithTop ℕ∞) ≤ ∞)
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
          change IsManifold I ∞ mc.limit.M
          infer_instance
        MetricFamilySmoothOn (I := I) (M := mc.limit.M) Y.D
          ({ base := { metric := co.gInf } } :
            DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I)
              (M := mc.limit.M) Y.D).family.metric)
    (hscalarCont : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      ContinuousOn
        (fun q : Real × mc.limit.M => metricScalarAt (I := I) (co.gInf q.1) q.2)
        (Y.D.carrier ×ˢ (Set.univ : Set mc.limit.M)))
    (hscalarTime : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      ∀ t ∈ Y.D.carrier, ∀ x : mc.limit.M,
        DifferentiableWithinAt Real
          (fun s : Real => metricScalarAt (I := I) (co.gInf s) x) Y.D.carrier t)
    (hricciCont : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      tensor0SFamilyContinuousOnSet (I := I) (M := mc.limit.M) 2 Y.D.carrier
        (fun t x => metricRicciAt (I := I) (co.gInf t) x))
    (hrm04Cont : letI : TopologicalSpace mc.limit.M := mc.limit.topology
        letI : ChartedSpace H mc.limit.M := mc.limit.charted
        letI : T2Space mc.limit.M := mc.limit.t2
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      tensor0SFamilyContinuousOnSet (I := I) (M := mc.limit.M) 4 Y.D.carrier
        (fun t x => metricRm04At (I := I) (co.gInf t) x)) :
    ∃ d : SmoothFlowLimitSubsequence (I := I) Y mc,
      ∀ t ∈ Y.D.carrier, MetricComplete (I := I) (d.limit.L.atTime (I := I) t) := by
  let : TopologicalSpace mc.limit.M := mc.limit.topology
  let : ChartedSpace H mc.limit.M := mc.limit.charted
  let : T2Space mc.limit.M := mc.limit.t2
  let : IsManifold I ∞ mc.limit.M := mc.limit.smooth
  let : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
  let : IsManifold I 1 mc.limit.M :=
    IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
    change IsManifold I ∞ mc.limit.M
    infer_instance
  have hpde : ∀ t ∈ Y.D.regular, ∀ (x : mc.limit.M) (v w : TangentSpace I x),
      HasDerivAt (fun s : Real => (co.gInf s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (co.gInf t) x v w) t := by
    intro t ht x v w
    have htneg : t < 0 := by
      simpa only [hregular, Set.mem_Iio] using ht
    exact HalfLineMetricConvergenceData.gInf_pde (I := I) Φ₀ co cLow hcLow hbound hcovTail
      (fun s hs => by simpa only [hregular] using hs) ht htneg x v w
  have hsol : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
      ({ base := { metric := co.gInf } } :
        DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := mc.limit.M) Y.D) :=
    DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_regularity (I := I) co.gInf hsmooth hpde
      hscalarCont hscalarTime hricciCont hrm04Cont
  exact exists_complete_smooth_flow_limit_subsequence_of_halfLine_metric_bounds (I := I) mc Φ₀ R
    bf hsrc htgt co hsol hzero hR cLow hcLow hbound hcovTail hcarrier

end HalfLineFlowLimit

end CheegerGromovCompactness
end DifferentialGeometry
