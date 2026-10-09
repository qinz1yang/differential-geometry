import DifferentialGeometry.Geometry.Collapse.CuspBoundaryDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime

universe u

theorem LateCutFamily.exists_eventual_collar_localization
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ C i, L.thin j C i →
      ∀ p : ((L.decomposition j C).component i).Carrier,
        distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p ≤
          ENNReal.ofReal 10 →
        ∃ (B : NearlyCuspidalBoundary ((L.decomposition j C).component i)
            (L.metric j C i) (K + 4) (1 / 10000)) (a : Fin B.count) (y : Torus),
          (B.collar a).toFun (y, halfZero) ∈
            ((L.decomposition j C).component i).model.boundary
              ((L.decomposition j C).component i).Carrier ∧
          (B.collar a).toFun (y, halfZero) ∈ B.component a ∧
          riemannianEDistOf (L.metric j C i) p ((B.collar a).toFun (y, halfZero)) <
            ENNReal.ofReal 11 ∧
          curvatureRadius (L.metric j C i) p ≤ ENNReal.ofReal 13 ∧
          ∀ r : ℝ, 0 < r → ENNReal.ofReal r < curvatureRadius (L.metric j C i) p →
            r < 13 ∧ riemannianBallOf (L.metric j C i) p r ⊆
              (B.collar a).toFun '' {x : CuspHalfSpace | x.2.val 0 < 25} := by
  obtain ⟨N, hN⟩ := L.alternatives (1 / 10000) (by norm_num) (by
    dsimp only [euclideanThreeUnitBallVolume]
    nlinarith [Real.pi_gt_three])
  refine ⟨N, ?_⟩
  intro j hj C i hi p hp
  obtain ⟨A⟩ := hN j hj C
  cases A i with
  | hyperbolic hnot _ _ => exact (hnot hi).elim
  | nonnegative hnot _ _ => exact (hnot hi).elim
  | thin _ hgeometry =>
    rcases hgeometry with ⟨hclosed, _⟩ | ⟨⟨B⟩, _⟩
    · rw [distanceToBoundary_eq_top_of_boundary_empty _ _ hclosed] at hp
      exact ((not_le_of_gt ENNReal.ofReal_lt_top) hp).elim
    · obtain ⟨a, y, hboundary, hcomponent, hdist, hR, hballs⟩ :=
        exists_collar_localization_of_distanceToBoundary_le B (le_refl _) p hp
      refine ⟨B, a, y, hboundary, hcomponent, hdist, hR, ?_⟩
      intro r hr hrho
      obtain ⟨hr13, hball⟩ := hballs r hr hrho
      exact ⟨hr13, fun q hq => hball (by
      change riemannianEDistOf (L.metric j C i) p q ≤ ENNReal.ofReal r
      exact le_of_lt hq)⟩

/-- The actual arbitrary late-cut family has a single eventual boundary-near
whole-ball derivative bound, uniform over all its thin pieces and orders. -/
theorem LateCutFamily.exists_eventual_nearBoundary_derivative_bound
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ j, N ≤ j → ∀ C i, L.thin j C i →
      ∀ p : ((L.decomposition j C).component i).Carrier,
        distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p ≤
          ENNReal.ofReal 10 →
      ∀ r : ℝ, 0 < r → ENNReal.ofReal r < curvatureRadius (L.metric j C i) p →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (L.metric j C i) p r,
        DifferentialGeometry.Geometry.Curvature.curvatureDerivativeNorm
          (L.metric j C i) k q ≤ A * (r ^ (k + 2))⁻¹ := by
  obtain ⟨A, hA, hbound⟩ := exists_bound_curvatureDerivativeNorm_near_cuspidalBoundary K
  obtain ⟨N, hN⟩ := L.exists_eventual_collar_localization
  refine ⟨A, hA, N, ?_⟩
  intro j hj C i hi p hp r hr hradius k hk q hq
  obtain ⟨B, _⟩ := hN j hj C i hi p hp
  exact hbound ((L.decomposition j C).component i) (L.metric j C i)
    B (le_refl _) p hp r hr hradius k hk q
    (by
      change riemannianEDistOf (L.metric j C i) p q ≤ ENNReal.ofReal r
      exact le_of_lt hq)

end GC.LongTime
