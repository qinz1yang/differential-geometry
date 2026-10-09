import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedFlowSlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedCurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive

section
set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isAncientKappaSolution_of_pointed_limit_of_terminal_scalar_bound
    (X : PointedFlowSeq.{u, uE, uH} I) (hD : X.D = ancientTimeInterval)
    (L : PointedFlowData.{u, uE, uH} I X.D) {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps X (L.atTime 0) phi) {kappa : ℝ}
    (hdim : Module.finrank ℝ E = 3) (hsource : ∀ i, IsAncientKappaSolution kappa (X.term i))
    (hconnected : ConnectedSpace L.M)
    (hcomplete : ∀ t ∈ X.D.carrier, MetricComplete (L.atTime t))
    (hconv : ∀ t ∈ X.D.carrier, ∃ C : MetricConvergenceData (Phi.atTime (L := L) t),
      ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData (Phi.atTime (L := L) t) k)
    {B : ℝ} (hbound : ∀ x : L.M, L.S.scalar 0 x ≤ B)
    (hnonflat : ∃ x : L.M, L.S.scalar 0 x ≠ 0) : IsAncientKappaSolution kappa L := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  have ht0 : (0 : ℝ) ∈ X.D.carrier := by simp only [hD, ancientTimeInterval_carrier, mem_Iic, le_refl]
  obtain ⟨C0, hc0⟩ := hconv 0 ht0
  have hscalar : PointedFlowScalarBounded L B := by
    intro t ht x
    have ht' : t ≤ 0 := by simpa only [hD, ancientTimeInterval_carrier, mem_Iic] using ht
    obtain ⟨Ct, hct⟩ := hconv t ht
    have hlim := pointedScalar_tendsto_of_metricCG_canonical_domains Ct hct x
    have hlim0 := pointedScalar_tendsto_of_metricCG_canonical_domains C0 hc0 x
    have hnn : 0 ≤ L.S.scalar t x := ge_of_tendsto hlim (Eventually.of_forall fun i =>
      ancientKappa_scalar_nonneg (X.term (phi i)) (hsource (phi i)) ht' (Phi.map i x))
    have hle : L.S.scalar t x ≤ L.S.scalar 0 x := le_of_tendsto_of_tendsto hlim hlim0
      (Eventually.of_forall fun i => ancientKappa_scalar_monotoneOn (X.term (phi i))
        (hsource (phi i)) (Phi.map i x) ht' (show (0 : ℝ) ∈ Iic 0 from (le_rfl : (0 : ℝ) ≤ 0)) ht')
    exact ⟨hnn, hle.trans (hbound x)⟩
  have hoperator : ∀ t ∈ X.D.carrier, PointedFlowNonnegativeCurvatureOperator L t := by
    intro t ht
    obtain ⟨Ct, hct⟩ := hconv t ht
    have hcone : ∀ x : L.M, metricAlgebraicCurvatureTensorAt (L.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) := by
      apply curvatureOperator_nonnegative_of_canonical_metricCGConvergence Ct hct
      intro K _hK
      refine Eventually.of_forall fun i y _hy _hs => ?_
      change metricAlgebraicCurvatureTensorAt ((X.term (phi i)).S.base.metric t)
        (Phi.map i y) ∈ algebraicCurvatureOperatorNonnegativeCone (I := I)
      apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
      intro n c v w
      have hh := (hsource (phi i)).nonnegativeCurvatureOperator t ht (Phi.map i y) n c v w
      simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
        tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using hh
    intro x n c v w
    have hh := (mem_algebraicCurvatureOperatorNonnegativeCone.mp (hcone x)) n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using hh
  have hnoncollapsed : PointedFlowNoncollapsedAllScales L kappa := by
    intro time ball hcurvature
    obtain ⟨Ct, hct⟩ := hconv time time.property
    have hnc := tensor_noncollapsed_of_pointed_canonical_convergence Ct hct
      (hcomplete time time.property) kappa (fun i p r hr hcurv => by
        let b : FlowMetricBall (X.term i).S time := ⟨p, r, hr⟩
        have hb : b.IsSpatiallyRmControlled := fun z hz => hcurv z hz
        exact ((hsource i).noncollapsed time b hb).2)
    exact ⟨(hsource 0).kappa_pos, hnc ball.center ball.radius ball.radius_pos hcurvature⟩
  obtain ⟨x, hx⟩ := hnonflat
  exact { kappa_pos := (hsource 0).kappa_pos
          carrier_eq := by rw [hD]; rfl
          regular_eq := by rw [hD]; rfl
          connected := hconnected
          complete := hcomplete
          nonnegativeCurvatureOperator := hoperator
          globalScalarBound := ⟨B, hscalar⟩
          noncollapsed := hnoncollapsed
          notFlat := pointedFlowNotFlat_of_scalar_ne_zero L ht0 x hx }

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
