import DifferentialGeometry.Geometry.Collapse.CuspEmbeddingFiniteDerivativeBounds
import DifferentialGeometry.Geometry.Collapse.CuspidalCutBallLocalization
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature GC.Endpoint Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- The uniform finite-order cusp estimate holds at height zero as well as at
positive height. The bound is independent of the carrier and the cusp lattice. -/
theorem exists_bound_curvatureDerivativeNorm_of_cuspEmbedding_allPoints (K : ℕ) :
    ∃ C > 0, ∀ (W : CompactCarrier.{u})
      (g : SmoothRiemannianMetric W.model W.Carrier)
      {L : ℕ} {δ : ℝ} {X : Set W.Carrier}
      (e : CuspEmbedding W g L δ X),
      K + 2 ≤ L → δ ≤ 1 / 2 →
      ∀ k : ℕ, k ≤ K → ∀ p ∈ cuspDomain,
        curvatureDerivativeNorm g k (e.toFun p) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_bound_curvatureDerivativeNorm_of_cuspEmbedding K
  refine ⟨C, hC, ?_⟩
  intro W g L δ X e hL hδ k hk p hp
  by_contra hnot
  have hdomain : IsOpen cuspDomain := isOpen_lt
    ((EuclideanSpace.proj 0).continuous.comp
      (continuous_subtype_val.comp continuous_snd)) continuous_const
  let U : Set CuspHalfSpace := cuspDomain ∩
    e.toFun ⁻¹' {x : W.Carrier | C < curvatureDerivativeNorm g k x}
  have hU : IsOpen U := e.contMDiffOn.continuousOn.isOpen_inter_preimage hdomain
    (isOpen_lt continuous_const (continuous_curvatureDerivativeNorm g k))
  have hpU : p ∈ U := ⟨hp, lt_of_not_ge hnot⟩
  obtain ⟨q, hqU, hqint⟩ := mem_closure_iff.mp
    ((ModelWithCorners.dense_interior halfCollarModel) p) U hU hpU
  change q ∈ (torusModel.prod (𝓡∂ 1)).interior
    (Torus × EuclideanHalfSpace 1) at hqint
  rw [ModelWithCorners.interior_prod] at hqint
  have hqhalf : (𝓡∂ 1).IsInteriorPoint q.2 := hqint.2
  have hqpos : 0 < q.2.val 0 := by
    simpa only [ModelWithCorners.IsInteriorPoint, extChartAt_self_apply,
      interior_range_modelWithCornersEuclideanHalfSpace, mem_setOf_eq,
      modelWithCornersEuclideanHalfSpace_apply] using hqhalf
  exact (not_lt_of_ge (hbound W g e hL hδ k hk q hqU.1 hqpos)) hqU.2

/-- One constant controls every derivative order through `K` throughout every
tested closed ball centered within distance ten of an actual nearly cuspidal
boundary. No volume premise or selected cut factory is required. -/
theorem exists_bound_curvatureDerivativeNorm_near_cuspidalBoundary (K : ℕ) :
    ∃ A > 0, ∀ (W : CompactCarrier.{u})
      (g : SmoothRiemannianMetric W.model W.Carrier) {δ : ℝ}
      (B : NearlyCuspidalBoundary W g (K + 4) δ),
      δ ≤ 1 / 10000 →
      ∀ p : W.Carrier, distanceToBoundary W g p ≤ ENNReal.ofReal 10 →
      ∀ r : ℝ, 0 < r → ENNReal.ofReal r < curvatureRadius g p →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianClosedBallOf g p r,
        curvatureDerivativeNorm g k q ≤ A * (r ^ (k + 2))⁻¹ := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_bound_curvatureDerivativeNorm_of_cuspEmbedding_allPoints K
  refine ⟨C * (13 : ℝ) ^ (K + 2), mul_pos hC (by positivity), ?_⟩
  intro W g δ B hδ p hp r hr hradius k hk q hq
  obtain ⟨i, _y, _hboundary, _hcomponent, _hdist, _hR, hballs⟩ :=
    exists_collar_localization_of_distanceToBoundary_le B hδ p hp
  obtain ⟨hr13, hball⟩ := hballs r hr hradius
  obtain ⟨z, hz, rfl⟩ := hball hq
  have hzdomain : z ∈ cuspDomain :=
    hz.trans (by norm_num [cuspDepth] : (25 : ℝ) < cuspDepth)
  have hnorm : curvatureDerivativeNorm g k ((B.collar i).toFun z) ≤ C :=
    hbound W g (B.collar i) (by omega) (hδ.trans (by norm_num)) k hk z hzdomain
  have hpower : r ^ (k + 2) ≤ (13 : ℝ) ^ (K + 2) :=
    (pow_le_pow_left₀ hr.le hr13.le _).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 13) (Nat.add_le_add_right hk 2))
  rw [le_mul_inv_iff₀ (pow_pos hr _)]
  exact (mul_le_mul_of_nonneg_right hnorm (pow_nonneg hr.le _)).trans
    (mul_le_mul_of_nonneg_left hpower hC.le)

end DifferentialGeometry.Geometry.Collapse
