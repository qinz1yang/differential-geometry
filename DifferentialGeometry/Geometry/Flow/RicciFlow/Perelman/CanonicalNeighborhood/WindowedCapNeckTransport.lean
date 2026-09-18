import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedNeckChainTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCapTransport

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem LocalCap.exists_windowed_transport_tolerance
    {P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval}
    [PreconnectedSpace P.M] {alpha : ℝ} {U : Set P.M}
    (L : LocalCap P.S (neckModelTolerance alpha) P.basepoint 0 U)
    (ha : 0 < alpha) (hsmall : alpha < 1 / 32)
    (hfar : ∀ y ∈ L.tube,
      20000 ≤ metricDistance (P.S.base.metric 0) P.basepoint y) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (delta kappa C : ℝ) (x : M) (t : ℝ)
        (W : WindowedModelWitness delta kappa S x t), delta ≤ delta₀ →
        IsSolutionOn S → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
        ∀ hmodel : W.model = P,
          Nonempty (CanonicalAlternative S (2 * alpha) C x t
            (W.embedding '' (hmodel.symm ▸ U))) := by
  let _ : LocallyCompactSpace P.M := Manifold.locallyCompact_of_finiteDimensional I3
  let _ : RegularSpace P.M := inferInstance
  let _ : PseudoMetricSpace P.M := (P.S.base.metric 0).toPseudoMetricSpace
  have htube : IsCompact L.tube := by
    rw [← L.tube_eq]
    exact (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (L.tube_map.contMDiffOn_toFun.continuousOn.mono L.tube_domain)
  have hU : IsCompact U := by
    rw [L.union_eq]
    exact L.core.compact.union htube
  obtain ⟨rho, hrho, hUrho⟩ := hU.isBounded.subset_closedBall_lt 0 P.basepoint
  have houter : U ⊆ riemannianClosedBallOf (P.S.base.metric 0) P.basepoint rho := by
    intro z hz
    change riemannianEDistOf (P.S.base.metric 0) P.basepoint z ≤ ENNReal.ofReal rho
    rw [← SmoothRiemannianMetric.toPseudoMetricSpace_edist, edist_dist]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [Metric.mem_closedBall, dist_comm] using hUrho hz)
  obtain ⟨d, hdpos, hd⟩ := L.chain.exists_windowed_transport_tolerance ha hsmall
  let delta₀ := min d (min (1 / 4) ((8 * rho + 1)⁻¹ ^ 2))
  have hradpos : 0 < 8 * rho + 1 := by positivity
  have hpos : 0 < delta₀ := lt_min hdpos
    (lt_min (by norm_num) (sq_pos_of_pos (inv_pos.mpr hradpos)))
  refine ⟨delta₀, hpos, ?_⟩
  intro M _ _ _ _ _ D S delta kappa C x t W hdelta hS hreg hmodel
  subst P
  have hdd : delta ≤ d := hdelta.trans (min_le_left _ _)
  have hdelta' := hdelta.trans (min_le_right _ _)
  have hd4 : delta ≤ 1 / 4 := hdelta'.trans (min_le_left _ _)
  have hdsq : delta ≤ (8 * rho + 1)⁻¹ ^ 2 := hdelta'.trans (min_le_right _ _)
  have hbuffer : 8 * rho ≤ modelRadius delta := by
    have hh := modelRadius_anti W.eps_pos hdsq
    rw [modelRadius, Real.sqrt_sq (inv_nonneg.mpr hradpos.le), inv_inv] at hh
    linarith
  obtain ⟨necks, hmap⟩ := hd M D S delta kappa x t W hdd hS hreg rfl
  exact W.canonicalAlternative_cap_of_transported_necks L hd4 hrho.le hbuffer houter
    ((neckModelTolerance_le alpha).trans (by linarith)) (by linarith) necks hmap hfar

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
