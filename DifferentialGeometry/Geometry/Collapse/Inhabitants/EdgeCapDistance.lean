import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapProduct
import DifferentialGeometry.Geometry.Metric.Path.Composition
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.Metric

/-! Genuine capped-plane radial distances and exact transported edge-axis distances. -/

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open scoped Manifold ContDiff Topology InnerProductSpace

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace DifferentialGeometry.Geometry.Collapse.EdgeCapDistance

local instance capPlaneNativeBundle : RiemannianBundle (TangentSpace (𝓡 2) : E2 → Type _) :=
  ⟨surfaceMetric.toRiemannianMetric⟩
local instance capAmbientNativeBundle : RiemannianBundle (TangentSpace (𝓡 3) : E3 → Type _) :=
  ⟨PDE.RicciFlow.StandardCap.metric.toRiemannianMetric⟩

theorem planeMap_fibre_norm (x : E2) (v : TangentSpace (𝓡 2) x) :
    ‖mfderiv (𝓡 2) (𝓡 3) planeMap x v‖ₑ = ‖v‖ₑ := by
  rw [DifferentialGeometry.Topology.Manifold.enorm_tangent_eq_sqrt_inner
    PDE.RicciFlow.StandardCap.metric,
    DifferentialGeometry.Topology.Manifold.enorm_tangent_eq_sqrt_inner surfaceMetric]
  rw [planeMap_mfderiv]
  exact congrArg (fun a : ℝ => ENNReal.ofReal (Real.sqrt a))
    (surfaceMetric_inner x (show E2 from v) (show E2 from v)).symm

theorem planeMap_edist_le (x y : E2) :
    riemannianEDistOf PDE.RicciFlow.StandardCap.metric (planeMap x) (planeMap y) ≤
      riemannianEDistOf surfaceMetric x y := by
  change riemannianEDist (𝓡 3) (planeMap x) (planeMap y) ≤ riemannianEDist (𝓡 2) x y
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hc
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) γ t :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      ((hγ t (Ioo_subset_Icc_self ht)).contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
        one_ne_zero
  have hmapInf : ContMDiff (𝓡 2) (𝓡 3) ∞ planeMap := planeMap.contDiff.contMDiff
  have hmap : ContMDiff (𝓡 2) (𝓡 3) 1 planeMap := hmapInf.of_le (by decide)
  have heq : pathELength (𝓡 3) (planeMap ∘ γ) 0 1 = pathELength (𝓡 2) γ 0 1 :=
    pathELength_comp_eq_of_enorm_mfderiv_eq planeMap hdiff
      (ae_of_all _ fun t => hmap.mdifferentiableAt one_ne_zero)
      (ae_of_all _ fun t => planeMap_fibre_norm (γ t) _)
  have hd := riemannianEDist_le_pathELength (hmap.comp_contMDiffOn hγ)
    (congrArg planeMap hγ0) (congrArg planeMap hγ1) zero_le_one
  rw [heq] at hd
  exact hd.trans_lt hlen

theorem surface_radial_lower (x y : E2) :
    ENNReal.ofReal |‖y‖ - ‖x‖| ≤ riemannianEDistOf surfaceMetric x y := by
  have h := PDE.RicciFlow.StandardCap.radial_difference_le_edist (planeMap x) (planeMap y)
  have hx : ‖planeMap x‖ = ‖x‖ := planeEmbedding.norm_map x
  have hy : ‖planeMap y‖ = ‖y‖ := planeEmbedding.norm_map y
  rw [hx, hy] at h
  exact h.trans (planeMap_edist_le x y)

theorem surface_edist_zero (x : E2) :
    riemannianEDistOf surfaceMetric 0 x = ENNReal.ofReal ‖x‖ := by
  apply le_antisymm
  · have h := surfaceEDist_le_euclidean 0 x
    rw [show euclideanMetric (E := E2) = standardEuclideanMetric E2 from rfl,
      riemannianEDistOf_standardEuclideanMetric, edist_dist, dist_zero_left] at h
    exact h
  · simpa only [norm_zero, sub_zero, abs_of_nonneg (norm_nonneg x)] using
      surface_radial_lower 0 x

theorem scaledCap_radial_lower (ε : ℝ) (hε : 0 < ε) (x y : E2) :
    ENNReal.ofReal (ε * |‖y‖ - ‖x‖|) ≤ riemannianEDistOf (scaledCapMetric ε hε) x y := by
  rw [scaledCapMetric, edistOf_scale, Real.sqrt_sq_eq_abs, abs_of_pos hε,
    ENNReal.ofReal_mul hε.le]
  exact mul_le_mul_right (surface_radial_lower x y) _

theorem scaledCap_edist_zero (ε : ℝ) (hε : 0 < ε) (x : E2) :
    riemannianEDistOf (scaledCapMetric ε hε) 0 x = ENNReal.ofReal (ε * ‖x‖) := by
  rw [scaledCapMetric, edistOf_scale, Real.sqrt_sq_eq_abs, abs_of_pos hε,
    surface_edist_zero, ENNReal.ofReal_mul hε.le]

def capProductAxis : Set (ℝ × E2) := {p | p.2 = 0}

theorem capProductAxis_closed : IsClosed capProductAxis :=
  isClosed_eq continuous_snd continuous_const

theorem capProduct_axis_infDist (ε : ℝ) (hε : 0 < ε) (p : ℝ × E2) :
    let capMetric := inducedMetricSpace (capProductMetric ε hε)
    let _capUniform := capMetric.toUniformSpace
    let _capEMetric := capMetric.toPseudoEMetricSpace
    let _capPseudo := capMetric.toPseudoMetricSpace
    Metric.infDist p capProductAxis = ε * ‖p.2‖ := by
  let capMetric := inducedMetricSpace (capProductMetric ε hε)
  let _capUniform := capMetric.toUniformSpace
  let _capEMetric := capMetric.toPseudoEMetricSpace
  let _capPseudo := capMetric.toPseudoMetricSpace
  have hmetric := inducedMetricSpace_hmetric (capProductMetric ε hε)
  have hd : dist p (p.1, 0) = ε * ‖p.2‖ := by
    have he : riemannianEDistOf (capProductMetric ε hε) p (p.1, 0) =
        ENNReal.ofReal (ε * ‖p.2‖) := by
      rw [capProductMetric, riemannianEDistOf_prod_right, riemannianEDistOf_comm,
        scaledCap_edist_zero]
    rw [hmetric] at he
    have hr := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_ofReal dist_nonneg,
      ENNReal.toReal_ofReal (mul_nonneg hε.le (norm_nonneg p.2))] at hr
    exact hr
  apply le_antisymm
  · exact (Metric.infDist_le_dist_of_mem
      (show (p.1, (0 : E2)) ∈ capProductAxis from rfl)).trans_eq hd
  · apply (Metric.le_infDist (show capProductAxis.Nonempty from ⟨(0, 0), rfl⟩)).mpr
    intro q hq
    have hz : q.2 = 0 := hq
    have h := riemannianEDistOf_snd_le_prod (euclideanMetric (E := ℝ))
      (scaledCapMetric ε hε) p q
    rw [hz, riemannianEDistOf_comm, scaledCap_edist_zero] at h
    change ENNReal.ofReal (ε * ‖p.2‖) ≤
      riemannianEDistOf (capProductMetric ε hε) p q at h
    rw [hmetric] at h
    exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h

theorem capHeight_axis_error (ε : ℝ) (hε : 0 < ε) (p : ℝ × E2) :
    let capMetric := inducedMetricSpace (capProductMetric ε hε)
    let _capUniform := capMetric.toUniformSpace
    let _capEMetric := capMetric.toPseudoEMetricSpace
    let _capPseudo := capMetric.toPseudoMetricSpace
    |capHeight ε p.2 - Metric.infDist p capProductAxis| ≤ ε := by
  let capMetric := inducedMetricSpace (capProductMetric ε hε)
  let _capUniform := capMetric.toUniformSpace
  let _capEMetric := capMetric.toPseudoEMetricSpace
  let _capPseudo := capMetric.toPseudoMetricSpace
  change |capHeight ε p.2 - Metric.infDist p capProductAxis| ≤ ε
  have hd := capProduct_axis_infDist ε hε p
  change Metric.infDist p capProductAxis = ε * ‖p.2‖ at hd
  rw [hd]
  have hlo := capHeight_norm_le ε hε p.2
  have hs : smoothRadius p.2 ≤ ‖p.2‖ + 1 := by
    have he : smoothRadius p.2 ^ 2 = 1 + ‖p.2‖ ^ 2 := Real.sq_sqrt (by positivity)
    have hf : 0 ≤ smoothRadius p.2 := Real.sqrt_nonneg _
    nlinarith [norm_nonneg p.2]
  have hu := mul_le_mul_of_nonneg_left hs hε.le
  change capHeight ε p.2 ≤ ε * (‖p.2‖ + 1) at hu
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  nlinarith

def capProduct_toThree_Isometry (ε : ℝ) (hε : 0 < ε) :
    let threeMetric := inducedMetricSpace (capThreeMetric ε hε)
    let _threeUniform := threeMetric.toUniformSpace
    let _threeEMetric := threeMetric.toPseudoEMetricSpace
    let _threePseudo := threeMetric.toPseudoMetricSpace
    let productMetric := inducedMetricSpace (capProductMetric ε hε)
    let _productUniform := productMetric.toUniformSpace
    let _productEMetric := productMetric.toPseudoEMetricSpace
    let _productPseudo := productMetric.toPseudoMetricSpace
    (ℝ × E2) ≃ᵢ E3 := by
  let threeMetric := inducedMetricSpace (capThreeMetric ε hε)
  let _threeUniform := threeMetric.toUniformSpace
  let _threeEMetric := threeMetric.toPseudoEMetricSpace
  let _threePseudo := threeMetric.toPseudoMetricSpace
  let productMetric := inducedMetricSpace (capProductMetric ε hε)
  let _productUniform := productMetric.toUniformSpace
  let _productEMetric := productMetric.toPseudoEMetricSpace
  let _productPseudo := productMetric.toPseudoMetricSpace
  refine ⟨capProductCoordinates.toEquiv, ?_⟩
  intro p q
  change riemannianEDistOf (capThreeMetric ε hε)
    (capProductCoordinates p) (capProductCoordinates q) =
      riemannianEDistOf (capProductMetric ε hε) p q
  have he := riemannianEDistOf_pullbackMetricCross (capProductMetric ε hε)
    capProductCoordinates.symm (capProductCoordinates p) (capProductCoordinates q)
  rw [Diffeomorph.symm_apply_apply, Diffeomorph.symm_apply_apply] at he
  change riemannianEDistOf (capThreeMetric ε hε)
    (capProductCoordinates p) (capProductCoordinates q) =
      riemannianEDistOf (capProductMetric ε hε) p q at he
  exact he

def capThreeAxis : Set E3 := capProductCoordinates.symm ⁻¹' capProductAxis

theorem capThreeAxis_closed : IsClosed capThreeAxis :=
  capProductAxis_closed.preimage capProductCoordinates.symm.continuous

theorem capThreeAxis_image : capProductCoordinates '' capProductAxis = capThreeAxis := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    change capProductCoordinates.symm (capProductCoordinates p) ∈ capProductAxis
    rw [Diffeomorph.symm_apply_apply]
    exact hp
  · intro hx
    exact ⟨capProductCoordinates.symm x, hx, Diffeomorph.apply_symm_apply _ _⟩

theorem capThree_axis_infDist (ε : ℝ) (hε : 0 < ε) (x : E3) :
    let threeMetric := inducedMetricSpace (capThreeMetric ε hε)
    let _threeUniform := threeMetric.toUniformSpace
    let _threeEMetric := threeMetric.toPseudoEMetricSpace
    let _threePseudo := threeMetric.toPseudoMetricSpace
    let productMetric := inducedMetricSpace (capProductMetric ε hε)
    let _productUniform := productMetric.toUniformSpace
    let _productEMetric := productMetric.toPseudoEMetricSpace
    let _productPseudo := productMetric.toPseudoMetricSpace
    Metric.infDist x capThreeAxis = ε * ‖(capProductCoordinates.symm x).2‖ := by
  let threeMetric := inducedMetricSpace (capThreeMetric ε hε)
  let _threeUniform := threeMetric.toUniformSpace
  let _threeEMetric := threeMetric.toPseudoEMetricSpace
  let _threePseudo := threeMetric.toPseudoMetricSpace
  let productMetric := inducedMetricSpace (capProductMetric ε hε)
  let _productUniform := productMetric.toUniformSpace
  let _productEMetric := productMetric.toPseudoEMetricSpace
  let _productPseudo := productMetric.toPseudoMetricSpace
  let e := capProduct_toThree_Isometry ε hε
  have h := Metric.infDist_image e.isometry
    (x := capProductCoordinates.symm x) (t := capProductAxis)
  have he : (e : (ℝ × E2) → E3) = capProductCoordinates := rfl
  rw [he] at h
  rw [Diffeomorph.apply_symm_apply, capThreeAxis_image] at h
  exact h.trans (capProduct_axis_infDist ε hε (capProductCoordinates.symm x))

theorem capThreeHeight_axis_error (ε : ℝ) (hε : 0 < ε) (x : E3) :
    let threeMetric := inducedMetricSpace (capThreeMetric ε hε)
    let _threeUniform := threeMetric.toUniformSpace
    let _threeEMetric := threeMetric.toPseudoEMetricSpace
    let _threePseudo := threeMetric.toPseudoMetricSpace
    let productMetric := inducedMetricSpace (capProductMetric ε hε)
    let _productUniform := productMetric.toUniformSpace
    let _productEMetric := productMetric.toPseudoEMetricSpace
    let _productPseudo := productMetric.toPseudoMetricSpace
    |capThreeHeight ε x - Metric.infDist x capThreeAxis| ≤ ε := by
  let threeMetric := inducedMetricSpace (capThreeMetric ε hε)
  let _threeUniform := threeMetric.toUniformSpace
  let _threeEMetric := threeMetric.toPseudoEMetricSpace
  let _threePseudo := threeMetric.toPseudoMetricSpace
  let productMetric := inducedMetricSpace (capProductMetric ε hε)
  let _productUniform := productMetric.toUniformSpace
  let _productEMetric := productMetric.toPseudoEMetricSpace
  let _productPseudo := productMetric.toPseudoMetricSpace
  change |capThreeHeight ε x - Metric.infDist x capThreeAxis| ≤ ε
  have h := capThree_axis_infDist ε hε x
  change Metric.infDist x capThreeAxis = ε * ‖(capProductCoordinates.symm x).2‖ at h
  rw [h]
  have hP := capHeight_axis_error ε hε (capProductCoordinates.symm x)
  simpa only [capProduct_axis_infDist ε hε (capProductCoordinates.symm x), capThreeHeight]
    using hP

end DifferentialGeometry.Geometry.Collapse.EdgeCapDistance
