import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiagonalDeepLocalCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalCapCanonicalWitness

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
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem exists_canonicalWitness_diagonal_shrinking_model
    (S : SolutionOn (I := I3) (M := M) ancientTimeInterval)
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    (hmetric : ∀ t : ℝ, ∀ ht : t ≤ 0,
      localPullMetric (Diffeomorph.pullbackMetricCross (S.base.metric t) d) cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
          scalarOneShrinkingCylinderMetric t (ht.trans_lt (by norm_num)))
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (p : Cylinder) (H : ℝ) :
    ∃ L r C : ℝ, eps⁻¹ < L ∧ |p.2| < L ∧ 1 ≤ r ∧ 1 ≤ C ∧
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
        (∀ y ∈ cap.tube, max 10000 H < metricDistance (S.base.metric 0)
          (d (cylinderDiagonalQuotientMap p)) y) ∧
        ∃ K : CanonicalWitness S eps r C (d (cylinderDiagonalQuotientMap p)) 0,
          K.domain.carrier = U ∧ K.radius = r ∧
          ∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap := by
  obtain ⟨L, r, hL, hpL, hr, cap, hcore, htube, hmap, hcount, hchain,
      hscalar, hinner, houter, hdepth⟩ :=
    exists_localCap_diagonal_shrinking_model S d hmetric heps hsmall p H
  have hpositive : ∀ y ∈ d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1))),
      0 < S.scalar 0 y := by
    intro y _hy
    rw [scalar_eq_one_of_diagonal_shrinking_model S d hmetric y]
    norm_num
  have hroot : Real.sqrt (S.scalar 0 (d (cylinderDiagonalQuotientMap p))) = 1 := by
    rw [hscalar, Real.sqrt_one]
  obtain ⟨_hC1, C, hC, K, hKU, hKr, hKcap⟩ :=
    cap.exists_canonicalWitness_of_scalar_pos_of_ball_sandwich hpositive
      (by simpa only [hroot, inv_one] using hr) hinner houter (by
        intro y hy
        rw [hroot, div_one]
        exact ((le_max_left 10000 H).trans_lt (hdepth y hy)).le)
  refine ⟨L, r, C, hL, hpL, hr, hC, cap, hcore, htube, hmap, hcount, hchain, hdepth, ?_⟩
  let result (C1 : ℝ) : Prop := ∃ K : CanonicalWitness S eps C1 C (d (cylinderDiagonalQuotientMap p)) 0,
    K.domain.carrier = d '' (cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-(L + 1)) (L + 1))) ∧
      K.radius = r ∧ ∃ cap' depth, K.alternative = CanonicalAlternative.cap cap' depth ∧ HEq cap' cap
  have hh : result (r * Real.sqrt (S.scalar 0 (d (cylinderDiagonalQuotientMap p)))) :=
    ⟨K, hKU, hKr, hKcap⟩
  have hparam : r * Real.sqrt (S.scalar 0 (d (cylinderDiagonalQuotientMap p))) = r := by
    rw [hroot, mul_one]
  exact Eq.mp (congrArg result hparam) hh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
