import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalLocalCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalCapMetric
open private exists_diagonal_slab_ball_sandwich_and_depth_with_margin from DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalCapMetric

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open Surgery.Topology
open KappaSolutions

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem exists_localCap_diagonal_shrinking_model
    (S : SolutionOn (I := I3) (M := M) ancientTimeInterval)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (S.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)))
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (p : Cylinder) (H : ℝ) :
    ∃ L r : ℝ, eps⁻¹ < L ∧ |p.2| < L ∧ 1 ≤ r ∧
      let U := d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1)))
      ∃ cap : LocalCap S eps (d (cylinderDiagonalQuotientMap p)) 0 U,
        cap.core.carrier = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ∧
        cap.tube = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc L (L + 1))) ∧
        (∀ z : Cylinder, cap.tubeMap z = d (cylinderDiagonalQuotientMap (z.1, L + z.2))) ∧
        cap.chain.count = 1 ∧
        (∀ i, cap.chain.centers i = d (cylinderDiagonalQuotientMap (p.1, L)) ∧
          (∀ z : Cylinder, (cap.chain.necks i).map z =
            d (cylinderDiagonalQuotientMap (z.1, z.2 + L))) ∧
          cap.chain.lo i = 0 ∧ cap.chain.hi i = 1) ∧
        S.scalar 0 (d (cylinderDiagonalQuotientMap p)) = 1 ∧
        riemannianBallOf (S.base.metric 0) (d (cylinderDiagonalQuotientMap p)) r ⊆ U ∧
        U ⊆ riemannianBallOf (S.base.metric 0) (d (cylinderDiagonalQuotientMap p)) (2 * r) ∧
        ∀ y ∈ cap.tube, max 10000 H < metricDistance (S.base.metric 0)
          (d (cylinderDiagonalQuotientMap p)) y := by
  have hstatic := pullbackMetric_diagonal_at_zero S d hmetric
  obtain ⟨L, hpL, hmargin, hsandwich⟩ :=
    exists_diagonal_slab_ball_sandwich_and_depth_with_margin (S.base.metric 0) d hstatic p
      (max H eps⁻¹)
  have hLeps : eps⁻¹ < L := by
    have hbig : eps⁻¹ ≤ max 10000 (max H eps⁻¹) := (le_max_right _ _).trans (le_max_right _ _)
    linarith [abs_nonneg p.2]
  obtain ⟨R, r, hR, _hLR, hr, hinner, houter, hdepth⟩ := hsandwich 1 zero_lt_one
  subst R
  obtain ⟨cap, hcore, htube, htubemap, hcount, hchain⟩ :=
    exists_localCap_diagonal_slab S d hmetric heps hsmall p L hpL hLeps.le
  refine ⟨L, r, hLeps, hpL, hr, cap, hcore, htube, htubemap, hcount, hchain,
    scalar_eq_one_of_diagonal_shrinking_model S d hmetric _, hinner, houter, ?_⟩
  intro y hy
  apply lt_of_le_of_lt (max_le_max le_rfl (le_max_left H eps⁻¹))
  exact hdepth y (htube ▸ hy)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
