import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ParabolicNoncollapseLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ParabolicOfSpatialAncient
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

theorem BackwardExtension.parabolicallyKappaNoncollapsedBelowScale
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) {rho : ℝ} (hrho : 0 < rho) :
    ParabolicallyKappaNoncollapsedBelowScale B.solution (modelNoncollapseFactor * kappa / 250)
      rho := by
  have hsigma : 0 < sigma := pos_of_mul_pos_right (X.noncollapse 0).1 (Real.sqrt_nonneg _)
  exact B.convergence.parabolicallyKappaNoncollapsedBelowScale
    (fun t ht => ⟨(B.complete t ht).complete⟩) (L.strictMono.comp B.strictMono)
    ((Real.tendsto_sqrt_atTop.comp X.scale_tendsto).atTop_mul_const hsigma) X.noncollapse hrho

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
    have h := pointedFlowNoncollapsedAllScales_of_parabolic_of_curvatureOperator_nonnegative
      B.pointed (kappa := modelNoncollapseFactor * kappa / 250) (by simp [ThreeSpace]) rfl rfl
      (fun t ht => B.complete t ht) hnonneg ⟨Q, hscalar⟩
      (fun rho hrho => B.parabolicallyKappaNoncollapsedBelowScale hrho)
    have hk : modelNoncollapseFactor * kappa / 250 / 30 ^ 3 = kappa := by
      unfold modelNoncollapseFactor
      ring
    rwa [hk] at h
  apply isAncientKappaSolution_of_limit B.pointed hkappa rfl rfl L.connected
    (fun t ht => B.complete t ht) hnonneg hscalar hnc
  change metricScalarAt (B.solution.base.metric 0) L.space.basepoint = 1
  rw [B.terminal]
  exact L.scalar_one

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
