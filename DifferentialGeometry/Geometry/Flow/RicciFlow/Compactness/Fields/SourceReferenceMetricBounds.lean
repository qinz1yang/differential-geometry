import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PullbackConnectionBounds
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.CompactExtension
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.LocalIsometryDifference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ}

theorem FlowMetricConvergenceData.exists_eventually_source_reference_metric_bounds
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt a b)
    (hG : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      MetricFamilySmoothOn X.D co.gInf)
    (hreg : Icc a b ⊆ X.D.regular)
    {K : Set P.M} (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ Λ A : ℝ, 1 ≤ Λ ∧ 0 < A ∧ ∃ N : ℕ, ∀ k ≥ N,
      letI : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      letI : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      letI : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      ∃ (h : SmoothRiemannianMetric I (X.term (subseq (co.φ k))).M)
        (U : Opens P.M),
        K ⊆ (U : Set P.M) ∧ (U : Set P.M) ⊆ Φ.source (co.φ k) ∧
        (∀ x ∈ U, ∀ v w : TangentSpace I x,
          R.inner x v w = h.inner (Φ.map (co.φ k) x)
            (mfderiv I I (Φ.map (co.φ k)) x v)
            (mfderiv I I (Φ.map (co.φ k)) x w)) ∧
        (∀ t ∈ Icc a b,
          MetricUniformEquivalentOn ((Φ.map (co.φ k)) '' K) h
            ((X.term (subseq (co.φ k))).S.base.metric t) Λ) ∧
        ∀ t ∈ Icc a b, ∀ x ∈ K,
          ∀ u w : TangentSpace I (Φ.map (co.φ k) x),
            let gt := (X.term (subseq (co.φ k))).S.base.metric t
            Real.sqrt (h.inner (Φ.map (co.φ k) x)
              (CovariantDerivative.difference (metricCov gt) (metricCov h)
                (Φ.map (co.φ k) x) u w)
              (CovariantDerivative.difference (metricCov gt) (metricCov h)
                (Φ.map (co.φ k) x) u w)) ≤
            A * Real.sqrt (h.inner (Φ.map (co.φ k) x) u u) *
              Real.sqrt (h.inner (Φ.map (co.φ k) x) w w) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hcarrier : Icc a b ⊆ X.D.carrier :=
    fun _ ht ↦ X.D.regular_subset (hreg ht)
  obtain ⟨L, hL, hlimit⟩ :=
    exists_metric_uniform_equivalent_on_compact_of_metricFamilySmoothOn
      co.gInf hG isCompact_Icc hcarrier hK R
  obtain ⟨J, hJ, N₁, hN₁⟩ :=
    FlowMetricConvergenceData.exists_eventually_metricCovDerivNorm_bound
      Φ R bf hsrc htgt co hG hreg hK 1
  obtain ⟨N₂, hN₂⟩ :=
    FlowMetricConvergenceData.exists_eventually_metricUniformEquivalentOn
      Φ R bf hsrc htgt co hK hL hlimit
  have hevent := co.strictMono.tendsto_atTop.eventually
    (DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback
      Φ R bf hsrc htgt K hK)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hevent
  let A : ℝ := 3 / 2 * (2 * L) ^ 3 * J
  have hLp : 0 < 2 * L := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨2 * L, A, by linarith, hA, max (max N₁ N₂) N₃, ?_⟩
  intro k hk
  let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).topology
  let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).charted
  let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).smooth
  let : T2Space (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).t2
  let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).sigmaCompact
  have hk₁ : N₁ ≤ k := (le_max_left _ _).trans ((le_max_left _ _).trans hk)
  have hk₂ : N₂ ≤ k := (le_max_right _ _).trans ((le_max_left _ _).trans hk)
  have hk₃ : N₃ ≤ k := (le_max_right _ _).trans hk
  obtain ⟨V, hV, hKV, hVs, hmetric⟩ := hN₃ k hk₃
  obtain ⟨h, W, hKW, hWs, href, _hout⟩ :=
    DifferentialGeometry.PartialDiffeomorph.exists_metric_preserving_on_neighborhood_of_is_compact
      (Φ.partialDiffeomorph (co.φ k)) R ((X.term (subseq (co.φ k))).S.base.metric 0) hK
      (fun x hx ↦ hVs (hKV hx))
  let U : Opens P.M := ⟨V ∩ (W : Set P.M), hV.inter W.isOpen⟩
  have hKU : K ⊆ (U : Set P.M) := fun x hx ↦ ⟨hKV hx, hKW hx⟩
  have hf : IsLocalDiffeomorphOn I I ∞ (Φ.map (co.φ k)) U := by
    intro y
    exact (Φ.partialDiffeomorph (co.φ k)).isLocalDiffeomorphAt I I ∞ (hVs y.2.1)
  have hrefU : ∀ x ∈ U, ∀ v w : TangentSpace I x,
      R.inner x v w = h.inner (Φ.map (co.φ k) x)
        (mfderiv I I (Φ.map (co.φ k)) x v)
        (mfderiv I I (Φ.map (co.φ k)) x w) :=
    fun x hx v w ↦ href x hx.2 v w
  refine ⟨h, U, hKU, fun x hx ↦ hVs hx.1, hrefU, ?_, ?_⟩
  · intro t ht
    refine ⟨by linarith, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ u
    let D := (hf ⟨x, hKU hx⟩).mfderivToContinuousLinearEquiv (by simp)
    obtain ⟨v, hv⟩ := D.surjective u
    change mfderiv I I (Φ.map (co.φ k)) x v = u at hv
    subst u
    rw [← hrefU x (hKU hx), ← hmetric t x (hKV hx)]
    exact (hN₂ k hk₂ t ht).2 x hx v
  · intro t ht x hx u w
    have hEq := hN₂ k hk₂ t ht
    have hJet : MetricCovDerivOrderBoundOn K 1
        (gSeqExt Φ R bf hsrc htgt (co.φ k) t) R J :=
      fun y hy ↦ hN₁ k hk₁ t ht 1 le_rfl y hy
    apply connectionDifference_norm_le_of_local_isometry_on
      (gSeqExt Φ R bf hsrc htgt (co.φ k) t) R
      ((X.term (subseq (co.φ k))).S.base.metric t) h U.isOpen hf
      (fun y hy v w ↦ hmetric t y hy.1 v w) hrefU (hKU hx) ?_ u w
    intro v z
    simpa only [A, metricCov, mul_assoc, mul_comm, mul_left_comm] using
      connectionDifference_gJet_le hEq hJet hx z v

end DifferentialGeometry.CheegerGromovCompactness
