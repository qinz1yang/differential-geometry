import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedUniformCovariantBounds
import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Precompactness


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private theorem eventually_uniform_chart_jet_bound
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
    (G : ℕ → ℝ → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) (J : Set ℝ)
    (x₀ : M) {Kc : Set M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source) (r : ℕ)
    (hbdd : ∀ q : ℕ, q ≤ r → ∃ C : ℝ, ∀ᶠ i in atTop,
      ∀ t ∈ J, ∀ z ∈ Kc, metricCovDerivNorm (I := I) q (G i t) gRef z ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ J, ∀ y ∈ Kc,
      ∀ j k : Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (G i t) x₀ j k)
          (extChartAt I x₀ y)‖ ≤ C := by
  classical
  choose C hC using fun q : Fin (r + 1) => hbdd q.val (by omega)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Filter.eventually_all.mpr hC)
  let F : {i : ℕ // N ≤ i} × {t : ℝ // t ∈ J} → SmoothRiemannianMetric I M :=
    fun z => G z.1.val z.2.val
  obtain ⟨B, hB, hbound⟩ := chartGram_iter_le (I := I) gRef F x₀ hKc hKchart r
    (by
      intro q hq
      refine ⟨C ⟨q, by omega⟩, ?_⟩
      intro z x hx
      exact hN z.1.val z.1.property ⟨q, by omega⟩ z.2.val z.2.property x hx)
  refine ⟨B, hB, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N] with i hi
  intro t ht y hy j k
  exact hbound (⟨i, hi⟩, ⟨t, ht⟩) y hy j k

private local instance chartJetTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance chartJetCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance chartJetSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance chartJetC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance chartJetT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance chartJetSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact

private local instance chartJetMetricTopology
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace P.M := P.topology
private local instance chartJetMetricCharted
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H P.M := P.charted
private local instance chartJetMetricSmooth
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ P.M := P.smooth


theorem exists_pointed_uniform_chart_jet_bound
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
    (A : ℝ) (hA : 0 ≤ A) (x₀ : L.M) {Kc : Set L.M} (hKc : IsCompact Kc)
    (hKchart : Kc ⊆ (chartAt H x₀).source)
    (hKball : Kc ⊆ riemannianClosedBallOf (I := I)
      (L.S.base.metric 0) L.basepoint A) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc a 0, ∀ y ∈ Kc,
      ∀ j k : Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I) (G i t) x₀ j k)
          (extChartAt I x₀ y)‖ ≤ C := by
  classical
  have hregular : ∀ q : ℕ, q ≤ r → ∃ C : ℝ, ∀ᶠ i in atTop,
      ∀ t ∈ Ico a 0, ∀ z ∈ Kc,
        metricCovDerivNorm (I := I) q (G i t) (L.S.base.metric a) z ≤ C := by
    intro q _hq
    rcases q.eq_zero_or_pos with rfl | hqpos
    · obtain ⟨B, hB, hEq⟩ := exists_pointed_fixed_reference_equivalence
        Phi hsource ha.le Kc hKc C0 hc0 Ca hca
      refine ⟨B * Real.sqrt (Module.finrank ℝ E : ℝ), ?_⟩
      filter_upwards [hEq, hG Kc hKc] with i hi hGi
      obtain ⟨U, _hU, hKU, _hUsource, hpair⟩ := hGi
      intro t ht z hz
      have hmetricEq : MetricUniformEquivalentOn (I := I) Kc
          (L.S.base.metric a) (G i t) B := by
        refine ⟨hB, ?_⟩
        intro x hx v
        rw [hpair t x (hKU hx) v v]
        exact hi.2 t ⟨ht.1, ht.2.le⟩ x hx v
      exact covNorm0_le (I := I) (G i t) (L.S.base.metric a) z hB
        ((metricUniformEquivalentOn_symm hmetricEq).2 z hz)
    · obtain ⟨C, _hC, hbdd⟩ := exists_pointed_uniform_positive_covariant_bound
        hdim Phi hsource hnormalized hcomplete G hG ha C0 hc0 Ca hca A hA q hqpos
      refine ⟨C, ?_⟩
      filter_upwards [hbdd] with i hi
      exact fun t ht z hz => hi t ht z (hKball hz)
  obtain ⟨Breg, hBreg, hreg⟩ := eventually_uniform_chart_jet_bound
    G (L.S.base.metric a) (Ico a 0) x₀ hKc hKchart r hregular
  have hterminal : ∀ q : ℕ, q ≤ r → ∃ C : ℝ, ∀ᶠ i in atTop,
      ∀ t ∈ ({0} : Set ℝ), ∀ z ∈ Kc,
        metricCovDerivNorm (I := I) q (G i t) (L.S.base.metric 0) z ≤ C := by
    intro q hq
    obtain ⟨Cself, hself⟩ := metricCovDerivNorm_bddOn (I := I)
      hKc q (L.S.base.metric 0) (L.S.base.metric 0)
    have hclose := eventually_pointed_extension_metric_close
      (Phi.atTime (L := L) 0) C0 hc0 (fun i => G i 0) Kc hKc
      (by
        filter_upwards [hG Kc hKc] with i hi
        obtain ⟨U, hU, hKU, hUsource, hpair⟩ := hi
        exact ⟨⟨U, hU⟩, hKU, hUsource, fun x hx v w => hpair 0 x hx v w⟩)
      r 1 zero_lt_one
    refine ⟨Cself + 1, ?_⟩
    filter_upwards [hclose] with i hi
    intro t ht z hz
    have ht0 : t = 0 := mem_singleton_iff.mp ht
    subst t
    exact (covNorm_le_add (I := I) q (G i 0) (L.S.base.metric 0)
      (L.S.base.metric 0) z).trans (add_le_add (hself z hz)
        ((derivNorm_le_sup (I := I) hKc hq (G i 0)
          (L.S.base.metric 0) (L.S.base.metric 0) hz).trans hi.le))
  obtain ⟨Bzero, _hBzero, hzero⟩ := eventually_uniform_chart_jet_bound
    G (L.S.base.metric 0) {0} x₀ hKc hKchart r hterminal
  refine ⟨max Breg Bzero, hBreg.trans (le_max_left _ _), ?_⟩
  filter_upwards [hreg, hzero] with i hiReg hiZero
  intro t ht y hy j k
  rcases ht.2.lt_or_eq with htneg | rfl
  · exact (hiReg t ⟨ht.1, htneg⟩ y hy j k).trans (le_max_left _ _)
  · exact (hiZero 0 (mem_singleton 0) y hy j k).trans (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
