import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedBufferedCurvatureJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedExtensionJetControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFixedReferenceEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.Tail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance uniformCovTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance uniformCovCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance uniformCovSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance uniformCovC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance uniformCovC2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 2 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance uniformCovT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance uniformCovSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance uniformCovTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

private local instance uniformCovMetricTopology
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace P.M := P.topology
private local instance uniformCovMetricCharted
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H P.M := P.charted
private local instance uniformCovMetricSmooth
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ P.M := P.smooth
private local instance uniformCovMetricT2
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : T2Space P.M := P.t2


theorem exists_pointed_uniform_positive_covariant_bound
    (hdim : Module.finrank ℝ E = 3)
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    (hnormalized : ∀ i, (X.term i).S.scalar 0 (X.term i).basepoint = 1)
    (hcomplete : MetricComplete (I := I) (L.atTime (I := I) 0))
    (G : ℕ → ℝ → SmoothRiemannianMetric I L.M)
    (hG : ∀ K : Set L.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set L.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
      ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
        (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
          (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x w))
    {a : ℝ} (ha : a < 0)
    (C0 : MetricConvergenceData (I := I) (Phi.atTime (L := L) 0))
    (hc0 : ∀ i, C0.domain i = CanonicalMetricCompactness.canonicalSourceData
      (I := I) (Phi.atTime (L := L) 0) i)
    (Ca : MetricConvergenceData (I := I) (Phi.atTime (L := L) a))
    (hca : ∀ i, Ca.domain i = CanonicalMetricCompactness.canonicalSourceData
      (I := I) (Phi.atTime (L := L) a) i)
    (A : ℝ) (hA : 0 ≤ A) (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Ico a 0,
      ∀ x ∈ riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint A,
        metricCovDerivNorm (I := I) p (G i t) (L.S.base.metric a) x ≤ C := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have hmetricComplete : RiemannianMetricComplete (I := I) (L.S.base.metric 0) :=
    ⟨MetricComplete.complete (I := I) (L.atTime (I := I) 0) hcomplete⟩
  let K := riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint A
  let Kbig := riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint (A + 1)
  have hK : IsCompact K := hmetricComplete.closedEBall_isCompact L.basepoint A
  have hKbig : IsCompact Kbig := hmetricComplete.closedEBall_isCompact L.basepoint (A + 1)
  have hdist : Continuous (fun x : L.M =>
      riemannianEDistOf (I := I) (L.S.base.metric 0) L.basepoint x) :=
    DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist
      (I := I) (L.S.base.metric 0) L.basepoint
  let U : TopologicalSpace.Opens L.M :=
    ⟨riemannianBallOf (I := I) (L.S.base.metric 0) L.basepoint (A + 1),
      isOpen_lt hdist continuous_const⟩
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  have hKU : K ⊆ U := by
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < A + 1)).mpr
      (by linarith : A < A + 1))
  have hUKbig : (U : Set L.M) ⊆ Kbig := by
    intro x hx
    change riemannianEDistOf (I := I) (L.S.base.metric 0) L.basepoint x ≤
      ENNReal.ofReal (A + 1)
    exact le_of_lt hx
  obtain ⟨Bm, hBm, hequiv⟩ := exists_pointed_fixed_reference_equivalence
    Phi hsource ha.le Kbig hKbig C0 hc0 Ca hca
  obtain ⟨W, hW, Nb, hNb⟩ := exists_pointed_buffered_mixed_curvature_bounds
    hdim Phi hsource hnormalized C0 hc0 hcomplete (A + 1) (by linarith)
  have hinitial := eventually_pointed_extension_positive_covariant_bound
    (Phi.atTime (L := L) a) Ca hca (fun i => G i a) Kbig hKbig
    (by
      filter_upwards [hG Kbig hKbig] with i hi
      obtain ⟨V, hV, hKV, hVsource, hpair⟩ := hi
      exact ⟨⟨V, hV⟩, hKV, hVsource, fun x hx v w => hpair a x hx v w⟩)
    p 1 zero_lt_one
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    ((hG Kbig hKbig).and (hequiv.and (hinitial.and (Filter.eventually_ge_atTop Nb))))
  let gSeq : ℕ → ℝ → SmoothRiemannianMetric I L.M := fun i t => G (i + N0) t
  have hgate (i : ℕ) := hN0 (i + N0) (by omega)
  have hUmap (i : ℕ) : (U : Set L.M) ⊆ Phi.source (i + N0) := by
    obtain ⟨V, _hV, hKV, hVsource, _hpair⟩ := (hgate i).1
    exact hUKbig.trans (hKV.trans hVsource)
  have hpair (i : ℕ) (t : ℝ) (x : L.M) (hx : x ∈ U)
      (v w : TangentSpace I x) :
      (gSeq i t).inner x v w =
        ((X.term (phi (i + N0))).S.base.metric t).inner (Phi.map (i + N0) x)
          (mfderiv I I (Phi.map (i + N0)) x v)
          (mfderiv I I (Phi.map (i + N0)) x w) := by
    obtain ⟨V, _hV, hKV, _hVsource, hVpair⟩ := (hgate i).1
    exact hVpair t x (hKV (hUKbig hx)) v w
  let Cjet : ℕ → ℝ := fun q =>
    Real.sqrt ((Module.finrank ℝ E : ℝ) ^ ((2 + q) + 2)) * W q 0
  have hCjet (q : ℕ) : 0 ≤ Cjet q := mul_nonneg (Real.sqrt_nonneg _) (hW q 0).le
  let KShi : ℝ := ∑ q ∈ Finset.range (p + 1), Cjet q
  have hKShi : 0 ≤ KShi := Finset.sum_nonneg fun q _ => hCjet q
  have hcurv (i q : ℕ) {t : ℝ} (ht : t ≤ 0) (x : L.M) (hx : x ∈ U) :
      Real.sqrt (Tensor0SBundle.normSq0S (I := I) (gSeq i t) x (2 + q)
        (ricCovTower (I := I) (gSeq i t) (gSeq i t) q x)) ≤ Cjet q := by
    rw [@ricCovTower_normSq_eq_of_local_pullback E _ _ _ _ H _ I _
      L.M L.topology L.charted L.smooth L.t2 (X.term (phi (i + N0))).M
      (X.term (phi (i + N0))).topology (X.term (phi (i + N0))).charted
      (X.term (phi (i + N0))).smooth (X.term (phi (i + N0))).t2
      (X.term (phi (i + N0))).sigmaCompact (Phi.partialDiffeomorph (i + N0))
      U inferInstance (hUmap i) (gSeq i t) ((X.term (phi (i + N0))).S.base.metric t)
      (hpair i t) q ⟨x, hx⟩]
    have htrace := Real.sqrt_le_sqrt (ricTower_normSq_le
      (X.term (phi (i + N0))).S t q (Phi.map (i + N0) x))
    rw [Real.sqrt_mul (by positivity)] at htrace
    have hbound := ((hNb (i + N0) (hgate i).2.2.2).2 x (hUKbig hx)).2 q 0 t ht
    exact htrace.trans (mul_le_mul_of_nonneg_left hbound.2 (Real.sqrt_nonneg _))
  have hflow (i : ℕ) : ∃ S : SolutionOn (I := I) (M := U) X.D,
      IsSolutionOn S ∧ ∀ t : ℝ, S.family.metric t = (gSeq i t).restrictOpen (I := I) U :=
    @exists_local_solution_of_pullback E _ _ _ _ H _ I _
      L.M L.topology L.charted L.smooth L.t2 (X.term (phi (i + N0))).M
      (X.term (phi (i + N0))).topology (X.term (phi (i + N0))).charted
      (X.term (phi (i + N0))).smooth (X.term (phi (i + N0))).t2
      (X.term (phi (i + N0))).sigmaCompact X.D (X.term (phi (i + N0))).S
      (X.term (phi (i + N0))).isSolution (Phi.partialDiffeomorph (i + N0)) U
      inferInstance (hUmap i) (gSeq i) (hpair i)
  obtain ⟨Cw, hCw⟩ := covOrder_Ico_tail (I := I) (K := K) (U := U)
    (t0 := a) (omega := 0) (gSeq := gSeq) (gRef := L.S.base.metric a)
    hK U.isOpen hKU p Bm hBm KShi hKShi (fun _ => 1) (fun _ => zero_le_one)
    (-a) (fun _ => Bm)
    (by
      intro psi hpsi i t ht
      refine ⟨hBm, fun x hx v => ?_⟩
      rw [hpair i t x hx v v]
      exact (hgate i).2.1.2 t ⟨ht.1, ht.2.trans hpsi.2.le⟩ x (hUKbig hx) v)
    (fun _ _ => le_rfl)
    (by
      intro psi hpsi q hq i t ht x hx
      exact (hcurv i q (ht.2.trans hpsi.2.le) x hx).trans
        (Finset.single_le_sum (fun q _ => hCjet q)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))))
    (by
      intro psi hpsi q _hq _hqp i x hx t ht slots
      obtain ⟨S, hS, hmet⟩ := hflow i
      apply metricCovDeriv_hasDerivAt_of_local_solution (gSeq i) (L.S.base.metric a)
        U S hS hmet q (x := ⟨x, hx⟩) (slots := slots)
      rw [(hsource 0).regular_eq]
      exact ht.2.trans_lt hpsi.2)
    (by
      intro q hq hqp i x hx
      exact (hgate i).2.2.1 q hq hqp x (hUKbig hx))
    (by
      intro t ht
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      linarith [ht.2]) p hp le_rfl
  refine ⟨max 0 Cw, le_max_left _ _, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N0] with i hi
  intro t ht x hx
  have h := (hCw (i - N0) t ht x hx).trans (le_max_right 0 Cw)
  simpa only [gSeq, Nat.sub_add_cancel hi] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
