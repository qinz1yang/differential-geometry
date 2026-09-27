import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndNeckPerturbation
import DifferentialGeometry.Geometry.Neck.ScalarNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.SpatialCapFrontier
import
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactDomainTransport
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩
private local instance (V : Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)
private local instance (δ : ℝ) : SigmaCompactSpace (bufferedCylinder δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen
      ((𝓡 2).prod 𝓘(ℝ)) (bufferedCylinder δ).isOpen)

theorem exists_window_spatialNeck_of_metric_close
    (D r eps : ℝ) (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) (hfit : r + eps⁻¹ + 1 ≤ D)
    (g : SmoothRiemannianMetric (𝓡 3) (standardCapWindow D)) {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 40000) (hηeps : 20000 * η ≤ eps)
    (hclose : metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r+eps⁻¹}
      ⌈eps⁻¹⌉₊ g (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal η) :
    ∃ p : standardCapWindow D, p.val = r • (spherePoint : ThreeSpace) ∧
      ∃ nk : SpatialNeck g eps p,
        (∀ z : neckBuffer eps, (nk.map z.val).val = (r+z.val.2) • (z.val.1 : ThreeSpace)) ∧
        |metricScalarAt g p - 1| ≤ 4323 * η := by
  let old := endNeckDatum r eps heps (hsmall.trans (by norm_num)) hr ⌈eps⁻¹⌉₊ true
  have hmem (z : bufferedCylinder eps) : old.map z ∈ standardCapWindow D := by
    change ‖endNeckMap r eps z‖ < D+1
    rw [endNeckMap_norm hr]
    linarith [z.property.2]
  let Φ : bufferedCylinder eps → standardCapWindow D := fun z => ⟨old.map z,hmem z⟩
  let hold := isLocalDiffeomorph_of_injective_mfderiv old.map old.smooth old.immersion (by simp)
  have hΦ : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ Φ :=
    fun z => isLocalDiffeomorphAt_subtypeCodRestrict hmem (hold z)
  have hinj : Injective Φ := fun x y h => old.injective (congrArg Subtype.val h)
  have hder (z : bufferedCylinder eps) : mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) Φ z =
      mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) old.map z := by
    exact (mfderiv_subtypeVal_comp Φ z).symm
  have href : pullbackMetricOfInjectiveLocalDiffeomorph
      (metric.restrictOpen (standardCapWindow D)) Φ hΦ hinj = referenceMetric eps := by
    have hraw : pullbackMetricOfInjectiveLocalDiffeomorph metric old.map hold old.injective =
        referenceMetric eps := by
      have hscalar : metricScalarAt metric (r • (spherePoint : ThreeSpace)) = 1 := by
        rw [← old.center_eq]
        exact endNeckMap_scalar hr _
      apply (show pullbackMetricOfInjectiveLocalDiffeomorph metric old.map hold old.injective =
          old.normalizedMetric from ?_).trans
        (endNeckDatum_normalizedMetric r eps heps (hsmall.trans (by norm_num)) hr ⌈eps⁻¹⌉₊ true)
      apply SmoothRiemannianMetric.ext_inner
      intro z v w
      rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner,old.normalizedMetric_inner,
        hscalar,one_mul]
    apply (show pullbackMetricOfInjectiveLocalDiffeomorph
        (metric.restrictOpen (standardCapWindow D)) Φ hΦ hinj =
        pullbackMetricOfInjectiveLocalDiffeomorph metric old.map hold old.injective from ?_).trans
          hraw
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner,
      pullbackMetricOfInjectiveLocalDiffeomorph_inner,hder]
    rfl
  have himage : Φ '' controlledCylinder eps ⊆
      {x : standardCapWindow D | ‖x.val‖ ≤ r+eps⁻¹} := by
    rintro x ⟨z,hz,rfl⟩
    change ‖endNeckMap r eps z‖ ≤ r+eps⁻¹
    rw [endNeckMap_norm hr]
    linarith [hz.2]
  have hraw : metricDerivENormSupOn (controlledCylinder eps) ⌈eps⁻¹⌉₊
      (pullbackMetricOfInjectiveLocalDiffeomorph g Φ hΦ hinj)
      (referenceMetric eps) (referenceMetric eps) < ENNReal.ofReal η := by
    rw [← href,metricDerivENormSupOn_pullbackMetricOfInjectiveLocalDiffeomorph]
    exact (metricDerivENormSupOn_mono himage le_rfl g _ _).trans_lt hclose
  have hscale : scaleMetric (1:ℝ) zero_lt_one g = g :=
    SmoothRiemannianMetric.ext_inner (fun x v w => by rw [scaleMetric_inner,one_mul])
  have hk : 2 ≤ ⌈eps⁻¹⌉₊ := by
    have hi : (2:ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ heps).mpr
      linarith
    exact_mod_cast hi.trans (Nat.le_ceil _)
  obtain ⟨d,hd,_,hscalar⟩ := exists_normalizedDatum_of_cylinder_pullback_close g
    heps (hsmall.trans (by norm_num)) hη hηsmall hηeps zero_lt_one hk Φ hΦ hinj
    (by rwa [hscale])
  obtain ⟨nk,_,hmap⟩ := d.toNormalizedNeck.exists_spatialNeck le_rfl hsmall le_rfl
  refine ⟨Φ (cylinderCenter eps heps),old.center_eq,nk,?_,?_⟩
  · intro z
    have hm := (hmap z).trans (congrFun hd z)
    exact (congrArg Subtype.val hm).trans (endNeckMap_apply r eps z)
  · simpa only [div_one] using hscalar

theorem exists_window_spatial_cap_frontier_of_metric_close
    (D r eps : ℝ) (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) (hfit : r + eps⁻¹ + 1 ≤ D)
    {s : ℝ} (hs : s ∈ Ioo (-eps⁻¹) eps⁻¹)
    (g : SmoothRiemannianMetric (𝓡 3) (standardCapWindow D)) {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 40000) (hηeps : 20000 * η ≤ eps)
    (hclose : metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r+eps⁻¹}
      ⌈eps⁻¹⌉₊ g (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal η) :
    ∃ (p z : standardCapWindow D), p.val = r • (spherePoint : ThreeSpace) ∧ z.val = 0 ∧
      ∃ (nk : SpatialNeck g eps p) (K : CompactDomain (standardCapWindow D)),
        K.carrier = {x : standardCapWindow D | ‖x.val‖ ≤ r+s} ∧
        Nonempty (CapCore K.carrier) ∧ z ∈ interior K.carrier ∧
        (∀ w : neckBuffer eps, (nk.map w.val).val = (r+w.val.2) • (w.val.1 : ThreeSpace)) ∧
        frontier K.carrier = range (fun q : Sphere 2 => nk.map (q,s)) ∧
        IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q,s)) ∧
        (∀ q : Sphere 2, ∀ t : ℝ, s+t ∈ Ioo (-eps⁻¹) eps⁻¹ →
          (nk.map (q,s+t) ∈ K.carrier ↔ t ≤ 0)) ∧
        |metricScalarAt g p - 1| ≤ 4323 * η := by
  obtain ⟨p,hp,nk,hmap,hscalar⟩ := exists_window_spatialNeck_of_metric_close
    D r eps heps hsmall hr hfit g hη hηsmall hηeps hclose
  obtain ⟨old,hold,K0,hK0,hmodel,hzero,hfront,_,_,hside,_⟩ :=
    exists_spatial_neck_closed_ball_frontier heps hsmall hr hs
  have hKD : K0.carrier ⊆ standardCapWindow D := by
    intro x hx
    rw [hK0] at hx
    have hn : ‖x‖ ≤ r+s := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    change ‖x‖ < D+1
    linarith [hs.2]
  let K := K0.restrictOpen (standardCapWindow D) hKD
  have hD : 0 < D+1 := by linarith [transitionEnd_pos,inv_pos.mpr heps]
  let z : standardCapWindow D := ⟨0,by change ‖(0:ThreeSpace)‖ < D+1;simpa only [norm_zero]⟩
  have hcarrier : K.carrier = {x : standardCapWindow D | ‖x.val‖ ≤ r+s} := by
    rw [show K.carrier = Subtype.val ⁻¹' K0.carrier from rfl,hK0]
    ext x
    simp only [mem_preimage,Metric.mem_closedBall,dist_zero_right,mem_ofPred_eq]
  have hmap' (q : Sphere 2) (t : ℝ) (ht : t ∈ Ioo (-eps⁻¹) eps⁻¹) :
      (nk.map (q,t)).val = old.map (q,t) := by
    let w : neckBuffer eps := ⟨(q,t),by constructor <;> linarith [ht.1,ht.2]⟩
    exact (hmap w).trans (hold w).symm
  refine ⟨p,z,hp,rfl,nk,K,hcarrier,?_,?_,hmap,?_,?_,?_,hscalar⟩
  · exact hmodel.some.nonempty_preimage_open (standardCapWindow D) hKD
  · rw [K0.interior_restrictOpen_carrier]
    exact hzero
  · rw [K0.frontier_restrictOpen_carrier,hfront]
    ext x
    constructor
    · rintro ⟨q,hq⟩
      refine ⟨q,Subtype.ext ?_⟩
      exact (hmap' q s hs).trans hq
    · rintro ⟨q,rfl⟩
      exact ⟨q,(hmap' q s hs).symm⟩
  · exact nk.isSmoothEmbedding_level (abs_lt.mpr hs)
  · intro q t ht
    change (nk.map (q,s+t)).val ∈ K0.carrier ↔ t ≤ 0
    rw [hmap' q (s+t) ht]
    exact hside q t ht

end DifferentialGeometry.PDE.RicciFlow.StandardCap
