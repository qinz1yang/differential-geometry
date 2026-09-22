import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.TerminalWindow
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.Terminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.MovingShi
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedExtensionJetControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CovariantEvolution

section

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff ENNReal _root_.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem StaticTerminalLimit.eventually_positive_covariant_bounds_of_local_pullbacks
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    (G : ℕ → ℝ → SmoothRiemannianMetric I3 L.space.M)
    (hG : ∀ K : Set L.space.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set L.space.M, IsOpen U ∧ K ⊆ U ∧
        U ⊆ (L.maps.partialDiffeomorph i).source ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I3 x,
          (G i t).inner x v w = ((X.term (L.subseq i)).S.base.metric t).inner
            (L.maps.partialDiffeomorph i x)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x v)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x w)) :
    ∀ K : Set L.space.M, IsCompact K → ∀ p : ℕ, 1 ≤ p →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ t ∈ Icc (-width) 0,
        ∀ x ∈ K, metricCovDerivNorm p (G i t) L.space.metric x ≤ C := by
  classical
  intro K hK p hp
  let _ : LocallyCompactSpace L.space.M := Manifold.locallyCompact_of_finiteDimensional I3
  obtain ⟨Kbig, hKbig, hKint, _hbig⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  let U : TopologicalSpace.Opens L.space.M := ⟨interior Kbig, isOpen_interior⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  obtain ⟨B, hB, hBsource⟩ := L.eventually_metric_uniformly_equivalent_on_compact hKbig hw hwd
  have hBbound : ∀ᶠ i in atTop, ∀ t ∈ Icc (-width) 0,
      MetricUniformEquivalentOn Kbig L.space.metric (G i t) B := by
    filter_upwards [hBsource, hG Kbig hKbig] with i hi hj
    obtain ⟨V, hV, hKV, hVs, hmet⟩ := hj
    intro t ht
    refine ⟨hB, ?_⟩
    intro x hx v
    rw [hmet t x (hKV hx) v v]
    exact hi.2 t ht x hx v
  obtain ⟨A, _hA0, hsourceJets⟩ := L.source_curvature_jets_uniform_on_compact hw hwd hKbig
  have hA : ∀ᶠ i in atTop, ∀ q ≤ p, ∀ t ∈ Icc (-width) 0, ∀ x ∈ Kbig,
      curvDerivNorm q (G i t) x ≤ A q := by
    filter_upwards [hsourceJets, hG Kbig hKbig] with i hi hj
    obtain ⟨V, hV, hKV, hVs, hmet⟩ := hj
    intro q _hq t ht x hx
    rw [curvDerivNorm_eq_of_local_pullback (G i t) ((X.term (L.subseq i)).S.base.metric t)
      (L.maps.partialDiffeomorph i) ⟨V, hV⟩ hVs (hmet t) q ⟨x, hKV hx⟩]
    dsimp only [curvDerivNorm]
    rw [curvNormSq_eq]
    exact hi q t ht x hx
  obtain ⟨KShi, hKShi, hShiOf⟩ := exists_movingShiBoundOn_constant_of_curvature_derivative_bounds
    (I := I3) (M := L.space.M) p A
  have hterminal := KappaSolutions.eventually_pointed_extension_positive_covariant_bound
    L.maps L.converges L.canonical_domains (fun i => G i 0) Kbig hKbig
    (by
      filter_upwards [hG Kbig hKbig] with i hi
      obtain ⟨V, hV, hKV, hVs, hpair⟩ := hi
      exact ⟨⟨V, hV⟩, hKV, hVs, fun x hx v w => hpair 0 x hx v w⟩)
    p 1 zero_lt_one
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hG Kbig hKbig).and (hBbound.and (hA.and hterminal)))
  let gSeq : ℕ → ℝ → SmoothRiemannianMetric I3 L.space.M := fun i t => G (i + N) t
  have hgate (i : ℕ) := hN (i + N) (by omega)
  have hUmap (i : ℕ) : (U : Set L.space.M) ⊆ (L.maps.partialDiffeomorph (i + N)).source :=
    interior_subset.trans ((hgate i).1.choose_spec.2.1.trans (hgate i).1.choose_spec.2.2.1)
  have hpair (i : ℕ) (t : ℝ) (x : L.space.M) (hx : x ∈ U)
      (v w : TangentSpace I3 x) :
      (gSeq i t).inner x v w = ((X.term (L.subseq (i + N))).S.base.metric t).inner
        (L.maps.partialDiffeomorph (i + N) x)
        (mfderiv I3 I3 (L.maps.partialDiffeomorph (i + N)) x v)
        (mfderiv I3 I3 (L.maps.partialDiffeomorph (i + N)) x w) :=
    (hgate i).1.choose_spec.2.2.2 t x
      ((hgate i).1.choose_spec.2.1 (interior_subset hx)) v w
  have hflow (i : ℕ) : ∃ S : SolutionOn (I := I3) (M := U) (X.interval (L.subseq (i + N))),
      IsSolutionOn S ∧ ∀ t : ℝ, S.family.metric t = (gSeq i t).restrictOpen U :=
    KappaSolutions.exists_local_solution_of_pullback
      (X.term (L.subseq (i + N))).S (X.term (L.subseq (i + N))).isSolution
      (L.maps.partialDiffeomorph (i + N)) U (hUmap i) (gSeq i) (hpair i)
  have hcarrier (i : ℕ) : Icc (-depthBound) 0 ⊆ (X.interval (L.subseq (i + N))).carrier :=
    L.carrier_window _
  have hregular (i : ℕ) : Ioo (-depthBound) 0 ⊆ (X.interval (L.subseq (i + N))).regular :=
    L.regular_window _
  obtain ⟨C, hC, hbound⟩ := exists_metric_covariant_derivative_bounds_from_terminal_values_of_evolution
    (c := -width) (b := 0) L.space.metric U U.isOpen p B hB KShi hKShi
    (fun _ => 1) (fun _ => zero_le_one)
  have hb := hbound gSeq
    (fun i t ht => ⟨hB, fun x hx v => (hgate i).2.1 t ht |>.2 x (interior_subset hx) v⟩)
    (hShiOf gSeq U (-width) 0
      (fun q hq i t ht x hx => (hgate i).2.2.1 q hq t ht x (interior_subset hx)))
    (fun q hq hqp i x hx => (hgate i).2.2.2 q hq hqp x (interior_subset hx))
    (by
      intro q _hq _hqp i x hx
      obtain ⟨S, hS, hmet⟩ := hflow i
      have hc := solution_metricCovDerivNorm_continuousOn_closed_interval S hS
        (a := -width) (b := 0) (by linarith)
        (fun t ht => hcarrier i ⟨by linarith [ht.1], ht.2⟩)
        (fun t ht => hregular i ⟨by linarith [ht.1], ht.2⟩)
        (L.space.metric.restrictOpen U) q ⟨x, hx⟩
      apply hc.congr
      intro t _ht
      change metricCovDerivNorm q (gSeq i t) L.space.metric x =
        metricCovDerivNorm q (S.family.metric t) (L.space.metric.restrictOpen U) ⟨x, hx⟩
      rw [hmet, covNorm_restrictOpen])
    (by
      intro q _hq _hqp i x hx s hs slots
      obtain ⟨S, hS, hmet⟩ := hflow i
      exact KappaSolutions.metricCovDeriv_hasDerivAt_of_local_solution
        (gSeq i) L.space.metric U S hS hmet q
        (hregular i ⟨by linarith [hs.1], hs.2⟩) ⟨x, hx⟩ slots)
    p hp le_rfl
  refine ⟨C p, hC p, ?_⟩
  filter_upwards [eventually_ge_atTop N] with i hi
  intro t ht x hx
  have h := hb (i - N) t ht x (hKint hx)
  simpa only [gSeq, Nat.sub_add_cancel hi] using h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem StaticTerminalLimit.eventually_covariant_bounds_of_local_pullbacks
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    (G : ℕ → ℝ → SmoothRiemannianMetric I3 L.space.M)
    (hG : ∀ K : Set L.space.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set L.space.M, IsOpen U ∧ K ⊆ U ∧
        U ⊆ (L.maps.partialDiffeomorph i).source ∧
        ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I3 x,
          (G i t).inner x v w = ((X.term (L.subseq i)).S.base.metric t).inner
            (L.maps.partialDiffeomorph i x)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x v)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x w))
    (K : Set L.space.M) (hK : IsCompact K) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop, ∀ q ≤ p, ∀ t ∈ Icc (-width) 0,
      ∀ x ∈ K, metricCovDerivNorm q (G i t) L.space.metric x ≤ C := by
  have hsingle (q : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in atTop,
      ∀ t ∈ Icc (-width) 0, ∀ x ∈ K,
        metricCovDerivNorm q (G i t) L.space.metric x ≤ C := by
    by_cases hq : q = 0
    · subst q
      obtain ⟨B, hB, hbound⟩ := L.eventually_metric_uniformly_equivalent_on_compact hK hw hwd
      refine ⟨B * Real.sqrt (Module.finrank ℝ ThreeSpace), mul_nonneg (by linarith)
        (Real.sqrt_nonneg _), ?_⟩
      filter_upwards [hbound, hG K hK] with i hi hj
      obtain ⟨U, _hU, hKU, _hUs, hmet⟩ := hj
      intro t ht x hx
      have heq : MetricUniformEquivalentOn K L.space.metric (G i t) B := by
        refine ⟨hB, ?_⟩
        intro y hy v
        rw [hmet t y (hKU hy) v v]
        exact hi.2 t ht y hy v
      exact covOrder_zero_le (G i t) L.space.metric heq x hx
    · exact L.eventually_positive_covariant_bounds_of_local_pullbacks hw hwd G hG K hK
        q (by omega)
  choose C hC0 hC using hsingle
  refine ⟨∑ q ∈ Finset.range (p + 1), C q, Finset.sum_nonneg (fun q _ => hC0 q), ?_⟩
  have hfinite : ∀ᶠ i in atTop, ∀ q ∈ Finset.range (p + 1),
      ∀ t ∈ Icc (-width) 0, ∀ x ∈ K,
        metricCovDerivNorm q (G i t) L.space.metric x ≤ C q :=
    (Filter.eventually_all_finset (Finset.range (p + 1))).mpr (fun q _ => hC q)
  filter_upwards [hfinite] with i hi
  intro q hq t ht x hx
  have hqp : q ∈ Finset.range (p + 1) := Finset.mem_range.mpr (by omega)
  exact (hi q hqp t ht x hx).trans
    (Finset.single_le_sum (fun j _ => hC0 j) hqp)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
