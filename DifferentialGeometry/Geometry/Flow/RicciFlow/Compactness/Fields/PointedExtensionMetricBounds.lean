import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.EventualTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedExtensionJetControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Canonical.ReferenceChange

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_eventually_pointed_extension_metric_bounds
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}
    (hphi : Tendsto phi atTop atTop)
    (F : PointedRiemannianConvergenceMaps (X.atZero (I := I)) P phi)
    (C : MetricConvergenceData F)
    (hcanonical : ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i)
    (hcomplete : MetricComplete P)
    (G : ℕ → ℝ → SmoothRiemannianMetric I P.M)
    (hG : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ F.source i ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I x,
          (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (F.map i x)
            (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x w))
    {a : ℝ} (ha : a < 0) (hcarrier : Icc a 0 ⊆ X.D.carrier)
    (hregular : Ico a 0 ⊆ X.D.regular) (N : ℕ)
    (hlocal : ∀ A : ℝ, 0 < A → ∀ q ≤ N, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in atTop,
      ∀ t ∈ Icc a 0, ∀ x : (X.term i).M,
        riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint x ≤
          ENNReal.ofReal A → curvDerivNorm q ((X.term i).S.base.metric t) x ≤ B)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ᶠ i in atTop,
      (∀ q ≤ N, ∀ t ∈ Icc a 0,
        ∀ x ∈ riemannianClosedBallOf P.metric P.basepoint A,
          metricCovDerivNorm q (G i t) P.metric x ≤ C) ∧
      (∀ q ≤ N, ∀ s ∈ Icc a 0, ∀ t ∈ Icc a 0,
        ∀ x ∈ riemannianClosedBallOf P.metric P.basepoint A,
          metricDerivNorm q (G i s) (G i t) P.metric x ≤ L * |s - t|) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hdist : Continuous (fun x => riemannianEDistOf P.metric P.basepoint x) :=
    DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist P.metric P.basepoint
  let U : TopologicalSpace.Opens P.M :=
    ⟨{x | riemannianEDistOf P.metric P.basepoint x < ENNReal.ofReal (A + 1)},
      isOpen_lt hdist continuous_const⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let K := riemannianClosedBallOf P.metric P.basepoint (A + 1)
  have hmetricComplete : RiemannianMetricComplete P.metric :=
    ⟨MetricComplete.complete P hcomplete⟩
  have hK : IsCompact K := hmetricComplete.closedEBall_isCompact P.basepoint (A + 1)
  have hUK : (U : Set P.M) ⊆ K := by
    intro x hx
    change riemannianEDistOf P.metric P.basepoint x < ENNReal.ofReal (A + 1) at hx
    change riemannianEDistOf P.metric P.basepoint x ≤ ENNReal.ofReal (A + 1)
    exact hx.le
  have hAU : riemannianClosedBallOf P.metric P.basepoint A ⊆ U := by
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < A + 1)).mpr
      (by linarith))
  have href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric := by
    intro i
    rw [hcanonical i]
    exact canonicalSourceData_referenceMetric_eq_limitMetric F i
  have hsol : ∀ᶠ i in atTop, ∃ S : SolutionOn (I := I) (M := U) X.D,
      IsSolutionOn S ∧ ∀ t, S.family.metric t = (G i t).restrictOpen U := by
    filter_upwards [hG K hK] with i hi
    obtain ⟨V, _hV, hKV, hVF, hpair⟩ := hi
    exact exists_local_solution_of_pullback (X.term (phi i)).S (X.term (phi i)).isSolution
      (F.partialDiffeomorph i) U (hUK.trans (hKV.trans hVF)) (G i)
      (fun t x hx => hpair t x (hKV (hUK hx)))
  have hcurv : ∀ q ≤ N, ∃ Q : ℝ, 0 ≤ Q ∧ ∀ᶠ i in atTop,
      ∀ t ∈ Icc a 0, ∀ x ∈ U, curvDerivNorm q (G i t) x ≤ Q := by
    intro q hq
    obtain ⟨Q, hQ, hb⟩ := exists_eventually_pointed_extension_curvature_bound
      hphi F C href hcomplete G hG (Icc a 0) q
      (fun R hR => hlocal R hR q hq) (show 0 ≤ A + 1 by linarith)
    exact ⟨Q, hQ, hb.mono fun i hi t ht x hx => hi t ht x (hUK hx)⟩
  have hRm : ∀ R : ℝ, 0 < R → ∃ Q : ℝ, 0 ≤ Q ∧ ∀ᶠ i in atTop,
      ∀ t ∈ Icc a 0, ∀ x : (X.term i).M,
        riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint x ≤
          ENNReal.ofReal R → (X.term i).rmNormSq t x ≤ Q := by
    intro R hR
    obtain ⟨Q, _hQ, hb⟩ := hlocal R hR 0 (Nat.zero_le N)
    refine ⟨Q ^ 2, sq_nonneg _, hb.mono fun i hi t ht x hx => ?_⟩
    exact (Real.sqrt_le_iff.mp (hi t ht x hx)).2
  obtain ⟨B, hB, hb⟩ := exists_eventually_pointed_extension_uniform_equivalence
    hphi F C href hcomplete G hG ha hcarrier (Ioo_subset_Ico_self.trans hregular)
    ⟨ha.le, le_rfl⟩ hRm (show 0 ≤ A + 1 by linarith)
  have hequiv : ∀ᶠ i in atTop, ∀ t ∈ Icc a 0,
      MetricUniformEquivalentOn U P.metric (G i t) B := by
    filter_upwards [hb] with i hi
    intro t ht
    exact ⟨hB, fun x hx => (hi t ht).2 x (hUK hx)⟩
  have hinit : ∀ᶠ i in atTop, ∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
      metricCovDerivNorm q (G i 0) P.metric x ≤ (1 : ℝ) := by
    have hpair : ∀ᶠ i in atTop, ∃ V : TopologicalSpace.Opens P.M,
        K ⊆ V ∧ (V : Set P.M) ⊆ F.source i ∧
        ∀ x ∈ V, ∀ v w : TangentSpace I x,
          (G i 0).inner x v w = ((X.term (phi i)).S.base.metric 0).inner (F.map i x)
            (mfderiv I I (F.map i) x v) (mfderiv I I (F.map i) x w) := by
      filter_upwards [hG K hK] with i hi
      obtain ⟨V, hV, hKV, hVF, hpair⟩ := hi
      exact ⟨⟨V, hV⟩, hKV, hVF, hpair 0⟩
    filter_upwards [eventually_pointed_extension_positive_covariant_bound F C hcanonical
      (fun i => G i 0) K hK hpair N 1 zero_lt_one] with i hi
    exact fun q hq hqN x hx => hi q hq hqN x (hUK hx)
  obtain ⟨C₀, L, hC₀, hL, hbounds⟩ :=
    exists_eventually_metric_bounds_from_terminal_values_of_local_solutions
      G P.metric U X.D ha hcarrier hregular hsol hB hequiv N hcurv
      (fun _ => 1) (fun _ => zero_le_one) hinit
  refine ⟨C₀, L, hC₀, hL, hbounds.mono fun i hi => ?_⟩
  exact ⟨fun q hq t ht x hx => hi.1 q hq t ht x (hAU hx),
    fun q hq s hs t ht x hx => hi.2 q hq s hs t ht x (hAU hx)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
