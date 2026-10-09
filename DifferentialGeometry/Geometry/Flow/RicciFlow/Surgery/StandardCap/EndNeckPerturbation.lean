import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.OpenEmbedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndNeckDatum
import DifferentialGeometry.Geometry.Neck.ScalarNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckSpatialBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckMarkSideBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.SpatialCapFrontier
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 3) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

private theorem end_neck_raw_metric_eq_reference
    (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (side : Bool) :
    let d := endNeckDatum r δ hδ hδ1 hr k side
    let hd := isLocalDiffeomorph_of_injective_mfderiv d.map d.smooth d.immersion (by simp)
    pullbackMetricOfInjectiveLocalDiffeomorph metric d.map hd d.injective = referenceMetric δ := by
  let d := endNeckDatum r δ hδ hδ1 hr k side
  let hd := isLocalDiffeomorph_of_injective_mfderiv d.map d.smooth d.immersion (by simp)
  have hscalar : metricScalarAt metric (r • (spherePoint : E3)) = 1 := by
    have hcenter : endNeckMap r δ (cylinderCenter δ hδ) = r • (spherePoint : E3) := by
      rw [endNeckMap_apply]
      simp only [cylinderCenter, add_zero]
    rw [← hcenter]
    exact endNeckMap_scalar hr _
  apply (show pullbackMetricOfInjectiveLocalDiffeomorph metric d.map hd d.injective =
      d.normalizedMetric from ?_).trans (endNeckDatum_normalizedMetric r δ hδ hδ1 hr k side)
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, d.normalizedMetric_inner,
    hscalar, one_mul]

theorem endNeckDatum_metric_derivative_error
    (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (side : Bool)
    (g : SmoothRiemannianMetric (𝓡 3) E3) :
    let d := endNeckDatum r δ hδ hδ1 hr k side
    let hd := isLocalDiffeomorph_of_injective_mfderiv d.map d.smooth d.immersion (by simp)
    metricDerivENormSupOn (controlledCylinder δ) k
      (pullbackMetricOfInjectiveLocalDiffeomorph g d.map hd d.injective)
      (referenceMetric δ) (referenceMetric δ) =
      metricDerivENormSupOn (endNeckMap r δ '' controlledCylinder δ) k g metric metric := by
  let d := endNeckDatum r δ hδ hδ1 hr k side
  let hd := isLocalDiffeomorph_of_injective_mfderiv d.map d.smooth d.immersion (by simp)
  have href := end_neck_raw_metric_eq_reference r δ hδ hδ1 hr k side
  let : SigmaCompactSpace (bufferedCylinder δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (bufferedCylinder δ).isOpen)
  have hnorm := metricDerivENormSupOn_pullbackMetricOfInjectiveLocalDiffeomorph
    (controlledCylinder δ) k g metric metric d.map hd d.injective
  rw [href] at hnorm
  exact hnorm

theorem exists_end_normalizedDatum_of_metric_close
    (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (hk : 2 ≤ k)
    (g : SmoothRiemannianMetric (𝓡 3) ThreeSpace) {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 40000) (hηδ : 20000 * η ≤ δ)
    (hclose : metricDerivENormSupOn (endNeckMap r δ '' controlledCylinder δ) k
      g metric metric < ENNReal.ofReal η) :
    ∃ d : normalizedDatum g (r • (spherePoint : ThreeSpace)) δ k,
      d.map = endNeckMap r δ ∧ d.retainedSide = true ∧
      |metricScalarAt g (r • (spherePoint : ThreeSpace)) - 1| ≤ 4323 * η := by
  let old := endNeckDatum r δ hδ hδ1 hr k true
  let hlocal := isLocalDiffeomorph_of_injective_mfderiv old.map old.smooth old.immersion (by simp)
  have hraw : metricDerivENormSupOn (controlledCylinder δ) k
      (pullbackMetricOfInjectiveLocalDiffeomorph g old.map hlocal old.injective)
      (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal η := by
    rw [endNeckDatum_metric_derivative_error r δ hδ hδ1 hr k true g]
    exact hclose
  have hscale : scaleMetric (1:ℝ) zero_lt_one g = g :=
    SmoothRiemannianMetric.ext_inner (fun x v w => by rw [scaleMetric_inner,one_mul])
  have hresult := exists_normalizedDatum_of_cylinder_pullback_close g
    hδ hδ1 hη hηsmall hηδ zero_lt_one hk old.map hlocal old.injective
    (by rwa [hscale])
  have hcenter : old.map (cylinderCenter δ hδ) = r • (spherePoint : ThreeSpace) := old.center_eq
  rw [hcenter] at hresult
  simpa only [div_one,old,endNeckDatum_map] using hresult

theorem exists_end_spatialNeck_of_metric_close
    (r eps : ℝ) (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r)
    (g : SmoothRiemannianMetric (𝓡 3) ThreeSpace) {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 40000) (hηeps : 20000 * η ≤ eps)
    (hclose : metricDerivENormSupOn (endNeckMap r eps '' controlledCylinder eps) ⌈eps⁻¹⌉₊
      g metric metric < ENNReal.ofReal η) :
    ∃ nk : SpatialNeck g eps (r • (spherePoint : ThreeSpace)),
      (∀ z : neckBuffer eps, nk.map z.val = (r+z.val.2) • (z.val.1 : ThreeSpace)) ∧
      |metricScalarAt g (r • (spherePoint : ThreeSpace)) - 1| ≤ 4323 * η := by
  have hk : 2 ≤ ⌈eps⁻¹⌉₊ := by
    have hi : (2:ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ heps).mpr
      linarith
    exact_mod_cast hi.trans (Nat.le_ceil _)
  obtain ⟨d, hd, _, hscalar⟩ := exists_end_normalizedDatum_of_metric_close r eps heps
    (hsmall.trans (by norm_num)) hr _ hk g hη hηsmall hηeps hclose
  obtain ⟨nk, _, hmap⟩ := d.toNormalizedNeck.exists_spatialNeck le_rfl hsmall le_rfl
  change SpatialNeck g eps (r • (spherePoint : ThreeSpace)) at nk
  refine ⟨nk,?_,hscalar⟩
  intro z
  exact (hmap z).trans ((congrFun hd z).trans (endNeckMap_apply r eps z))

theorem exists_spatial_cap_frontier_of_metric_close
    {eps r : ℝ} (heps : 0 < eps) (hepssmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) {s : ℝ}
    (hs : s ∈ Ioo (-eps⁻¹) eps⁻¹)
    (g : SmoothRiemannianMetric (𝓡 3) ThreeSpace) {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 40000) (hηeps : 20000 * η ≤ eps)
    (hclose : metricDerivENormSupOn (endNeckMap r eps '' controlledCylinder eps) ⌈eps⁻¹⌉₊
      g metric metric < ENNReal.ofReal η) :
    ∃ nk : SpatialNeck g eps (r • (spherePoint : ThreeSpace)),
      (∀ z : neckBuffer eps, nk.map z.val = (r + z.val.2) • (z.val.1 : ThreeSpace)) ∧
      ∃ K : CompactDomain ThreeSpace,
        K.carrier = Metric.closedBall (0 : ThreeSpace) (r+s) ∧ Nonempty (CapCore K.carrier) ∧
        (0 : ThreeSpace) ∈ interior K.carrier ∧
        frontier K.carrier = range (fun q : Sphere 2 => nk.map (q,s)) ∧
        IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q,s)) ∧
        (∀ q : Sphere 2, ∀ t : ℝ, s+t ∈ Ioo (-eps⁻¹) eps⁻¹ →
          (nk.map (q,s+t) ∈ K.carrier ↔ t ≤ 0)) ∧
        |metricScalarAt g (r • (spherePoint : ThreeSpace)) - 1| ≤ 4323 * η := by
  obtain ⟨old, hold, K, hK, hmodel, hzero, hfront, hsmooth, hscalar, hside, hdist⟩ :=
    exists_spatial_neck_closed_ball_frontier heps hepssmall hr hs
  obtain ⟨nk, hnk, hcenter⟩ := exists_end_spatialNeck_of_metric_close r eps heps hepssmall
    hr g hη hηsmall hηeps hclose
  have hmap (q : Sphere 2) (t : ℝ) (ht : t ∈ Ioo (-eps⁻¹) eps⁻¹) :
      nk.map (q,t) = old.map (q,t) := by
    let z : neckBuffer eps := ⟨(q,t),by constructor <;> linarith [ht.1,ht.2]⟩
    exact (hnk z).trans (hold z).symm
  refine ⟨nk,hnk,K,hK,hmodel,hzero,?_,?_,?_,hcenter⟩
  · rw [hfront]
    congr 1
    funext q
    exact (hmap q s hs).symm
  · exact nk.isSmoothEmbedding_level (abs_lt.mpr hs)
  · intro q t ht
    rw [hmap q (s+t) ht]
    exact hside q t ht

end DifferentialGeometry.PDE.RicciFlow.StandardCap
