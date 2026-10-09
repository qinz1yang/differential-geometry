import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapCylindrical
import DifferentialGeometry.Geometry.Collapse.Inhabitants.EdgeCapSplitting
import DifferentialGeometry.Geometry.Metric.Path.Composition
import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
set_option autoImplicit false
noncomputable section
open Bundle Set Function Manifold Metric MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Collapse.EdgeCapSurface
open DifferentialGeometry.Geometry.Collapse.EdgeCapProduct
open DifferentialGeometry.Geometry.Collapse.EdgeCapDistance
open DifferentialGeometry.Geometry.Collapse.EdgeCapCarrier
open DifferentialGeometry.Geometry.Collapse.EdgeCapCylindrical
open DifferentialGeometry.Geometry.Collapse.EdgeCapSplitting
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology InnerProductSpace
attribute [local instance] capPlaneDimensionFact
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
namespace DifferentialGeometry.Geometry.Collapse.EdgeCapRadial

def capRayPoint (θ : AddCircle (1 : ℝ)) (r : ℝ) : E2 :=
  (r / capExampleEpsilon) • (capAngle θ).val

theorem capRayPoint_norm (θ : AddCircle (1 : ℝ)) (r : ℝ) (hr : 0 ≤ r) :
    ‖capRayPoint θ r‖ = r / capExampleEpsilon := by
  unfold capRayPoint
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hr capExampleEpsilon_pos.le),
    norm_eq_of_mem_sphere (capAngle θ), mul_one]

theorem capRayPoint_euclidean_distance (θ : AddCircle (1 : ℝ)) (r s : ℝ) :
    dist (capRayPoint θ r) (capRayPoint θ s) = |r - s| / capExampleEpsilon := by
  rw [dist_eq_norm]
  unfold capRayPoint
  rw [← sub_smul, norm_smul, Real.norm_eq_abs,
    norm_eq_of_mem_sphere (capAngle θ), mul_one, ← sub_div, abs_div,
    abs_of_pos capExampleEpsilon_pos]

theorem capRayPoint_edist (θ : AddCircle (1 : ℝ)) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    riemannianEDistOf (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
      (capRayPoint θ r) (capRayPoint θ s) = ENNReal.ofReal |r - s| := by
  apply le_antisymm
  · have h := scaledCapEDist_le capExampleEpsilon capExampleEpsilon_pos
      (capRayPoint θ r) (capRayPoint θ s)
    rw [capRayPoint_euclidean_distance] at h
    have he : capExampleEpsilon * (|r - s| / capExampleEpsilon) = |r - s| := by
      field_simp [capExampleEpsilon_pos.ne']
    rwa [he] at h
  · have h := scaledCap_radial_lower capExampleEpsilon capExampleEpsilon_pos
      (capRayPoint θ r) (capRayPoint θ s)
    rw [capRayPoint_norm θ r hr, capRayPoint_norm θ s hs] at h
    have he : capExampleEpsilon * |s / capExampleEpsilon - r / capExampleEpsilon| =
        |r - s| := by
      rw [← sub_div, abs_div, abs_of_pos capExampleEpsilon_pos]
      field_simp [capExampleEpsilon_pos.ne']
      exact abs_sub_comm _ _
    rwa [he] at h

theorem capRayPoint_angular_smooth (r : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun θ : AddCircle (1 : ℝ) => capRayPoint θ r) :=
  ((r / capExampleEpsilon) • ContinuousLinearMap.id ℝ E2).contDiff.contMDiff.comp
    (contMDiff_coe_sphere.comp capAngle_smooth)

theorem capRayPoint_polar (r : ℝ) :
    (fun θ : AddCircle (1 : ℝ) => capRayPoint θ r) =
      capPolarPartial capExampleEpsilon capExampleEpsilon_pos ∘ (fun θ => (θ, r)) := by
  funext θ
  simp only [Function.comp_apply, capPolarPartial_apply, capRayPoint, div_eq_mul_inv, mul_comm]

theorem capRayPoint_angular_metric (θ : AddCircle (1 : ℝ)) (r : ℝ)
    (hr : transitionEnd ≤ capExampleEpsilon⁻¹ * r)
    (v w : TangentSpace 𝓘(ℝ, ℝ) θ) :
    (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos).inner (capRayPoint θ r)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun a : AddCircle (1 : ℝ) => capRayPoint a r) θ v)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun a : AddCircle (1 : ℝ) => capRayPoint a r) θ w) =
      smallFlatCircleMetric.inner θ v w := by
  have hrpos : 0 < r := by
    nlinarith [transitionEnd_pos, inv_pos.mpr capExampleEpsilon_pos]
  have hsrc : (θ, r) ∈ (capPolarPartial capExampleEpsilon capExampleEpsilon_pos).source :=
    (capPolarPartial_source _ _).mpr hrpos
  have hC : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞
      (capPolarPartial capExampleEpsilon capExampleEpsilon_pos)
      (capPolarPartial capExampleEpsilon capExampleEpsilon_pos).source (θ, r) :=
    (capPolarPartial capExampleEpsilon capExampleEpsilon_pos).contMDiffOn (θ, r) hsrc
  have hAt := hC.contMDiffAt
    ((capPolarPartial capExampleEpsilon capExampleEpsilon_pos).open_source.mem_nhds hsrc)
  have hMD := hAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hright : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (fun a : AddCircle (1 : ℝ) => (a, r)) θ :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  rw [capRayPoint_polar, mfderiv_comp θ hMD hright, mfderiv_prod_left]
  let vr : ℝ := v
  let wr : ℝ := w
  have hmetric := capPolarPartial_selected_metric (θ, r) hr (vr, 0) (wr, 0)
  rw [SmoothRiemannianMetric.prod_inner smallFlatCircleMetric
    (euclideanMetric (E := ℝ)) (θ, r) (vr, 0) (wr, 0)] at hmetric
  have hpoint := congrFun (capRayPoint_polar r) θ
  simp only [Function.comp_apply] at hpoint
  rw [hpoint]
  have hzero : (euclideanMetric (E := ℝ)).inner r 0 0 = 0 := by
    change ⟪(0 : ℝ), 0⟫_ℝ = 0
    simp
  change @Eq ℝ _ _ at hmetric
  erw [hzero, add_zero] at hmetric
  change @Eq ℝ _ _
  have hv : @Eq E2
      (((mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
        (capPolarPartial capExampleEpsilon capExampleEpsilon_pos) (θ, r)).comp
        (ContinuousLinearMap.inl ℝ ℝ ℝ)) v)
      (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
        (capPolarPartial capExampleEpsilon capExampleEpsilon_pos) (θ, r) (vr, 0)) := rfl
  have hw : @Eq E2
      (((mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
        (capPolarPartial capExampleEpsilon capExampleEpsilon_pos) (θ, r)).comp
        (ContinuousLinearMap.inl ℝ ℝ ℝ)) w)
      (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2)
        (capPolarPartial capExampleEpsilon capExampleEpsilon_pos) (θ, r) (wr, 0)) := rfl
  erw [hv, hw]
  exact hmetric

theorem capRayPoint_path_length (r : ℝ) (hr : transitionEnd ≤ capExampleEpsilon⁻¹ * r)
    (γ : ℝ → AddCircle (1 : ℝ))
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 γ (Icc (0 : ℝ) 1)) :
    metricPathELength (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
      ((fun θ : AddCircle (1 : ℝ) => capRayPoint θ r) ∘ γ) 0 1 =
        metricPathELength smallFlatCircleMetric γ 0 1 := by
  rw [metricPathELength_eq, metricPathELength_eq]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hF := (capRayPoint_angular_smooth r (γ t)).mdifferentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hγd := (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
    (by norm_num : (1 : ℕ∞ω) ≠ 0)
  rw [mfderiv_comp_apply t hF hγd]
  simp only [Function.comp_apply]
  erw [capRayPoint_angular_metric (γ t) r hr]

theorem capRayPoint_circle_edist_le (r : ℝ)
    (hr : transitionEnd ≤ capExampleEpsilon⁻¹ * r) (θ η : AddCircle (1 : ℝ)) :
    riemannianEDistOf (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
      (capRayPoint θ r) (capRayPoint η r) ≤ riemannianEDistOf smallFlatCircleMetric θ η := by
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_lt_of_edistOf_lt smallFlatCircleMetric hc
  have hF1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1
      (fun a : AddCircle (1 : ℝ) => capRayPoint a r) :=
    (capRayPoint_angular_smooth r).of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  have hmap := hF1.comp_contMDiffOn hγ
  have hd := edistOf_le_metricPathELength
    (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos) zero_le_one hmap
  simp only [Function.comp_apply, h0, h1] at hd
  rw [capRayPoint_path_length r hr γ hγ] at hd
  exact hd.trans_lt hlen

theorem capRayPoint_fibre_bound (r : ℝ)
    (hr : transitionEnd ≤ capExampleEpsilon⁻¹ * r) (θ η : AddCircle (1 : ℝ)) :
    riemannianEDistOf (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
      (capRayPoint θ r) (capRayPoint η r) ≤ ENNReal.ofReal (1 / 10000 : ℝ) :=
  (capRayPoint_circle_edist_le r hr θ η).trans (smallFlatCircle_distance θ η)

theorem capRayPoint_positive_cover (z : E2) (hz : z ≠ 0) :
    ∃ θ : AddCircle (1 : ℝ), ∃ r : ℝ, 0 < r ∧
      r = capExampleEpsilon * ‖z‖ ∧ capRayPoint θ r = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨θ, hθ⟩ := capAngle_surjective ⟨‖z‖⁻¹ • z, by
    change dist (‖z‖⁻¹ • z) 0 = 1
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    field_simp [hn.ne']⟩
  refine ⟨θ, capExampleEpsilon * ‖z‖, mul_pos capExampleEpsilon_pos hn, rfl, ?_⟩
  unfold capRayPoint
  have he : capExampleEpsilon * ‖z‖ / capExampleEpsilon = ‖z‖ := by
    field_simp [capExampleEpsilon_pos.ne']
  rw [he, hθ]
  rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

section ActualDistance
attribute [local instance] capSurfaceSigma capSurfaceMetricSpace capSurfaceEDist capSurfaceDist
  capSurfaceUniform capSurfaceEMetric capSurfacePseudo

theorem capRayPoint_distance (θ : AddCircle (1 : ℝ)) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    dist (capRayPoint θ r) (capRayPoint θ s) = |r - s| := by
  change (riemannianEDistOf (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
    (capRayPoint θ r) (capRayPoint θ s)).toReal = |r - s|
  rw [capRayPoint_edist θ r s hr hs, ENNReal.toReal_ofReal (abs_nonneg _)]

theorem capRayPoint_fibre_distance (r : ℝ)
    (hr : transitionEnd ≤ capExampleEpsilon⁻¹ * r) (θ η : AddCircle (1 : ℝ)) :
    dist (capRayPoint θ r) (capRayPoint η r) ≤ 1 / 10000 := by
  change (riemannianEDistOf (scaledCapMetric capExampleEpsilon capExampleEpsilon_pos)
    (capRayPoint θ r) (capRayPoint η r)).toReal ≤ 1 / 10000
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (capRayPoint_fibre_bound r hr θ η)
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 10000)] using h

theorem capRayPoint_distance_zero (θ : AddCircle (1 : ℝ)) (r : ℝ) (hr : 0 ≤ r) :
    dist (capRayPoint θ r) 0 = r := by
  have h := capRayPoint_distance θ r 0 hr le_rfl
  simpa only [capRayPoint, zero_div, zero_smul, sub_zero, abs_of_nonneg hr] using h

theorem capRayPoint_distance_lower (θ η : AddCircle (1 : ℝ)) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) : |r - s| ≤ dist (capRayPoint θ r) (capRayPoint η s) := by
  have h := abs_dist_sub_le (capRayPoint θ r) (capRayPoint η s) (0 : E2)
  rwa [capRayPoint_distance_zero θ r hr, capRayPoint_distance_zero η s hs] at h

theorem capRayPoint_distance_upper (θ η : AddCircle (1 : ℝ)) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hend : transitionEnd ≤ capExampleEpsilon⁻¹ * s) :
    dist (capRayPoint θ r) (capRayPoint η s) ≤ |r - s| + 1 / 10000 := by
  have h := dist_triangle (capRayPoint θ r) (capRayPoint θ s) (capRayPoint η s)
  rw [capRayPoint_distance θ r s hr hs] at h
  exact h.trans (add_le_add le_rfl (capRayPoint_fibre_distance s hend θ η))
end ActualDistance

end DifferentialGeometry.Geometry.Collapse.EdgeCapRadial
