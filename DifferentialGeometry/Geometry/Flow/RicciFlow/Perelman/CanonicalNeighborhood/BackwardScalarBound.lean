import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RecenteredScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardScalarExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardFiniteHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalSliceScalarTransfer

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_uniform_backward_scalar_bound_on_finite_horizon
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X) (T : ℝ),
        ∃ C : ℝ, ∀ (a : ℝ) (ha : a < 0), T ≤ a →
          ∀ B : BackwardExtension L (RealTimeInterval.closed a 0 ha.le),
            ∀ t ∈ Icc a 0, ∀ x : L.space.M, B.solution.scalar t x ≤ C := by
  obtain ⟨epsF, hepsF, hfar⟩ := exists_uniform_scalar_bound_outside_terminal_ball.{u} kappa
  obtain ⟨epsS, hepsS, hprop⟩ := uniform_moving_slice_propagation_of_recenteredSourceBound
    (recentered_source_bound hkappa hsigma hPhi)
  refine ⟨min epsF epsS, lt_min hepsF hepsS, ?_⟩
  intro eps heps hle X L T
  classical
  by_cases hcompact : CompactSpace L.space.M
  · let _ : CompactSpace L.space.M := hcompact
    obtain ⟨D, hD, hgeometry⟩ := exists_uniform_scalar_bounded_point_and_diameter_of_compact L T
    obtain ⟨C, hC⟩ := hprop eps heps (hle.trans (min_le_right _ _)) 1 D hD
    refine ⟨C, ?_⟩
    intro a ha hTa B t ht x
    obtain ⟨⟨z, hz⟩, hdiam⟩ := hgeometry a ha hTa B t ht
    exact hC X L _ B t ht z x hz (hdiam z x)
  · let _ : ConnectedSpace L.space.M := L.connected
    let _ : EMetricSpace L.space.M := L.space.emetricSpace
    have hfinite (x y : L.space.M) : edist x y ≠ ⊤ := riemannianEDistOf_ne_top L.space.metric x y
    let _ : MetricSpace L.space.M := EMetricSpace.toMetricSpace hfinite
    have hdist (x y : L.space.M) : dist x y = metricDistance L.space.metric x y := rfl
    obtain ⟨Q₀, hQ₀⟩ := L.scalar_bound
    let Q := max Q₀ 0
    have hQ : 0 ≤ Q := le_max_right _ _
    have hterminal : ∀ x : L.space.M, metricScalarAt L.space.metric x ≤ Q :=
      fun x => (hQ₀ x).trans (le_max_left _ _)
    let A := (20 / 3 : ℝ) * Real.sqrt (2 * (-T) * Q) * Real.sqrt (-T)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    let p := L.space.basepoint
    obtain ⟨R, Cfar, hR, _hCfar, hCfar⟩ :=
      hfar (hle.trans (min_le_left _ _)) X L hcompact A hA p
    have hescape : ∃ z : L.space.M, R < metricDistance L.space.metric p z := by
      by_contra! hbound
      have hball : (univ : Set L.space.M) ⊆ riemannianClosedBallOf L.space.metric p R := by
        intro z _
        exact (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top _ _ _) hR.le).mpr (hbound z)
      have hcomplete : RiemannianMetricComplete L.space.metric := ⟨L.complete.complete⟩
      have hcomp := (RiemannianMetricComplete.closedEBall_isCompact hcomplete p R).of_isClosed_subset isClosed_univ hball
      exact hcompact (isCompact_univ_iff.mp hcomp)
    obtain ⟨z, hz⟩ := hescape
    let D := metricDistance L.space.metric z p + R + A
    have hD : 0 ≤ D := by dsimp [D, metricDistance]; positivity
    obtain ⟨Ccore, hCcore⟩ := hprop eps heps (hle.trans (min_le_right _ _)) Cfar D hD
    refine ⟨max Cfar Ccore, ?_⟩
    intro a ha hTa B t ht x
    have herror : ∀ y w : L.space.M,
        metricDistance L.space.metric y w ≤ metricDistance (B.solution.base.metric t) y w ∧
        metricDistance (B.solution.base.metric t) y w ≤ metricDistance L.space.metric y w + A := by
      intro y w
      have h := B.metricDistance_sub_terminal_le_of_left_endpoint_ge ha hTa hQ hterminal ht y w
      dsimp [A]
      constructor <;> linarith
    by_cases hx : R < metricDistance L.space.metric p x
    · exact (hCfar _ B t ht herror x hx).trans (le_max_left _ _)
    · have hRx : metricDistance L.space.metric p x ≤ R := le_of_not_gt hx
      have hzx : metricDistance (B.solution.base.metric t) z x ≤ D := by
        have htri := dist_triangle z p x
        rw [hdist, hdist, hdist] at htri
        have hd := (herror z x).2
        dsimp [D]
        linarith
      exact (hCcore X L _ B t ht z x (hCfar _ B t ht herror z hz) hzx).trans
        (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
