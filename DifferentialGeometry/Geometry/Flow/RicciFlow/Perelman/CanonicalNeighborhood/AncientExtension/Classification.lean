import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabRicciCoefficientLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TerminalScalar
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Integral.Measure

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem BackwardExtension.metric_noncollapsed
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) {t : ℝ} (ht : t ∈ J.carrier) :
    MetricNoncollapsed { L.space with metric := B.solution.base.metric t } kappa univ := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let f := L.subseq ∘ B.subseq
  let F := X.toFlowSequence.sliceMaps (subsequenceMaps L.maps B.subseq B.strictMono)
    B.solution.base.metric t
  obtain ⟨C, hcanonical⟩ := B.convergence.exists_canonical_metric_convergence ht
  have hsigma : 0 < sigma := by
    nlinarith [Real.sqrt_nonneg (X.scale 0), (X.noncollapse 0).1]
  have hradii : Tendsto (fun i => Real.sqrt (X.scale (f i)) * sigma) atTop atTop :=
    ((Real.tendsto_sqrt_atTop.comp X.scale_tendsto).atTop_mul_const hsigma).comp
      (L.strictMono.comp B.strictMono).tendsto_atTop
  have htime : ∀ᶠ i in atTop, t ∈ (X.interval (f i)).carrier := by
    have hconv := B.convergence (∅ : Set L.space.M) isCompact_empty t t le_rfl
      (by simpa only [Icc_self, singleton_subset_iff] using ht) 0 1 one_pos
    exact hconv.mono fun i hi => hi.1 ⟨le_rfl, le_rfl⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hnc := KappaSolutions.tensor_noncollapsed_of_eventually_pointed_canonical_convergence
    (Φ := F) C hcanonical (B.complete t ht) kappa (by
      intro r hr
      filter_upwards [htime, hradii.eventually_ge_atTop r] with i hi hir
      intro p hcurv
      have h := X.metric_noncollapsed_atTime (f i) t hi p r ⟨hr, hir⟩ hr hcurv
      rw [ENNReal.ofReal_mul' (pow_nonneg hr.le 3), ENNReal.ofReal_pow hr.le] at h
      simp only [hdim]
      with_unfolding_all exact h)
  intro p r _ hr hcurv
  simpa only [hdim, ENNReal.ofReal_mul' (pow_nonneg hr.le 3),
    ENNReal.ofReal_pow hr.le] using hnc p r hr hcurv

theorem BackwardExtension.isAncientKappaSolution
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    (B : BackwardExtension L ancientTimeInterval) (hkappa : 0 < kappa) :
    IsAncientKappaSolution kappa B.pointed := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hop : ∀ t ≤ 0, ∀ x : L.space.M,
      metricAlgebraicCurvatureTensorAt (B.solution.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone := by
    intro t ht x
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
      (B.solution.base.metric t) x (by simp [ThreeSpace])).mpr
    intro v w
    have hvec : (fun i => ![v, w, w, v] i) = vec4 (I := I3) v w w v := by
      funext i
      fin_cases i <;> simp [vec4]
    simpa only [zero_mul, metricRm04StandardAt_apply, hvec] using
      B.nonnegative t ht x (mem_univ x) v w
  have hcomplete : ∀ t ∈ ancientTimeInterval.regular,
      RiemannianMetricComplete (B.solution.base.metric t) :=
    fun t ht => ⟨(B.complete t (show t ≤ 0 from le_of_lt ht)).complete⟩
  have hcurv : ∀ c d : ℝ, Icc c d ⊆ ancientTimeInterval.regular →
      ∃ C : ℝ, ∀ t ∈ Icc c d, ∀ x : L.space.M,
        Tensor0SBundle.normSq0S (B.solution.base.metric t) x 4
          (B.solution.base.rm04 t x) ≤ C := by
    intro c d hsub
    by_cases hcd : c ≤ d
    · exact B.compact_time_bound c d hcd (fun t ht => show t ≤ 0 from le_of_lt (hsub ht))
    · exact ⟨0, fun t ht => ((not_le.mp hcd).not_ge (ht.1.trans ht.2)).elim⟩
  obtain ⟨Q, hQ⟩ := L.scalar_bound
  have hscalar : PointedFlowScalarBounded B.pointed Q := by
    intro t ht x
    refine ⟨metricScalarAt_nonnegative_of_curvatureOperator_nonnegative
      (B.solution.base.metric t) x (hop t ht x), ?_⟩
    have h := hamilton_ancient_scalar_le_terminal B.solution B.isSolution hcomplete hcurv
      (fun s hs => hop s (le_of_lt hs)) ht (show (0 : ℝ) ≤ 0 from le_rfl) Subset.rfl x
    exact h.trans (by
      change metricScalarAt (B.solution.base.metric 0) x ≤ Q
      rw [B.terminal]
      exact hQ x)
  have hnonneg : ∀ t ∈ ancientTimeInterval.carrier,
      PointedFlowNonnegativeCurvatureOperator B.pointed t := by
    intro t ht x n c v w
    have h := (mem_algebraicCurvatureOperatorNonnegativeCone.mp (hop t ht x)) n c v w
    with_unfolding_all exact h
  have hnc : PointedFlowNoncollapsedAllScales B.pointed kappa := by
    intro time ball hcontrol
    have h := B.metric_noncollapsed time.property ball.center ball.radius (mem_univ _)
      ball.radius_pos hcontrol
    refine ⟨hkappa, ?_⟩
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    change ENNReal.ofReal kappa * ENNReal.ofReal ball.radius ^ Module.finrank ℝ ThreeSpace ≤
      riemannianVolumeMeasure I3 L.space.M (B.solution.base.metric time)
        (riemannianBallOf (B.solution.base.metric time) ball.center ball.radius)
    simpa only [hdim, ENNReal.ofReal_mul hkappa.le,
      ENNReal.ofReal_pow ball.radius_pos.le] using h
  apply isAncientKappaSolution_of_limit B.pointed hkappa rfl rfl L.connected
    (fun t ht => B.complete t ht) hnonneg hscalar hnc
  change metricScalarAt (B.solution.base.metric 0) L.space.basepoint = 1
  rw [B.terminal]
  exact L.scalar_one

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
