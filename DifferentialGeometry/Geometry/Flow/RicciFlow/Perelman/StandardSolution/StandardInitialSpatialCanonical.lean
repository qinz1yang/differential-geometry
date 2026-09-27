import DifferentialGeometry.Geometry.Neck.BallVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndNeckPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.GrowingInitialCylinderCharts
import DifferentialGeometry.Geometry.Neck.SpatialIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance

open private exists_compactDomain_of_cylinder_slab from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_pos_le_spatialNeck_unit_slab_volume :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
        {B K : ℝ}, 1 ≤ B → metricScalarAt g p ≤ B →
          Real.sqrt (normSq0S g p 4 (metricRm04 g p)) ≤ K →
          ENNReal.ofReal (κ * (2 * (K + B + 1))⁻¹ ^ 3) ≤
            riemannianVolumeMeasure I3 M g (nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  obtain ⟨κ, hκ, hvol⟩ := exists_pos_mul_cube_le_spatialNeck_ball_volume_of_curvature_bound.{u}
  refine ⟨κ, hκ, ?_⟩
  intro M _ _ _ _ _ g eps p nk B K hB hQB hRm
  have hK : 0 ≤ K := (Real.sqrt_nonneg _).trans hRm
  set s := K + B + 1 with hs
  have hs2 : 2 ≤ s := by linarith
  set r := (2 * s)⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hrs : r * (2 * s) = 1 := inv_mul_cancel₀ (by positivity)
  have hN := normSq0S_nonneg g p 4 (metricRm04 g p)
  have hNK : normSq0S g p 4 (metricRm04 g p) ≤ K ^ 2 := by
    have h := Real.sq_sqrt hN
    nlinarith [Real.sqrt_nonneg (normSq0S g p 4 (metricRm04 g p))]
  have htest : r ^ 4 * normSq0S g p 4 (metricRm04At g p) ≤ 1 := by
    rw [← metricRm04_apply]
    have hKs : K ^ 2 ≤ s ^ 2 := by nlinarith
    have h1 : r ^ 4 * normSq0S g p 4 (metricRm04 g p) ≤ r ^ 4 * s ^ 2 :=
      mul_le_mul_of_nonneg_left (hNK.trans hKs) (by positivity)
    have h2 : r ^ 4 * s ^ 2 ≤ 1 := by
      have hrs' : r * s = 1 / 2 := by linarith
      have : r ^ 4 * s ^ 2 = (r * s) ^ 2 * r ^ 2 := by ring
      rw [this, hrs']
      have hr1 : r ≤ 1 := by nlinarith
      nlinarith
    linarith
  have hball := hvol nk r hr0 htest
  have hQ := nk.Q_pos
  have hsmall : (1 : ℝ) < eps⁻¹ := by
    have h := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith [nk.eps_small] :
      eps < (1 : ℝ)⁻¹)
    exact h
  have hsub := nk.ball_subset_image_slab (r := 1) (by norm_num) hsmall
  have hrad : r ≤ 1 * Real.sqrt (1 - eps) / Real.sqrt (metricScalarAt g p) := by
    have hsq : Real.sqrt (metricScalarAt g p) ≤ B := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    have hhalf : (1 / 2 : ℝ) ≤ Real.sqrt (1 - eps) := by
      apply Real.le_sqrt_of_sq_le
      linarith [nk.eps_small]
    have hroot := Real.sqrt_pos.mpr hQ
    rw [one_mul, le_div_iff₀ hroot]
    have hrB : r * B ≤ 1 / 2 := by
      have : r * B ≤ r * s := mul_le_mul_of_nonneg_left (by linarith) hr0.le
      linarith
    calc r * Real.sqrt (metricScalarAt g p) ≤ r * B := mul_le_mul_of_nonneg_left hsq hr0.le
      _ ≤ 1 / 2 := hrB
      _ ≤ Real.sqrt (1 - eps) := hhalf
  exact hball.trans (MeasureTheory.measure_mono
    ((riemannianBallOf_mono g p hrad).trans (by simpa only [neg_one_mul] using hsub)))

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}

theorem SpatialNeck.exists_compactDomain_region (nk : SpatialNeck g eps x) :
    ∃ K : CompactDomain M, K.carrier = nk.map '' (univ ×ˢ Icc (-10 : ℝ) 10) ∧
      x ∈ interior K.carrier ∧
      frontier K.carrier = nk.map '' (univ ×ˢ ({-10, 10} : Set ℝ)) := by
  have hsmall : (10 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
    (by linarith [nk.eps_small])
  have hsrc : univ ×ˢ Icc (-10 : ℝ) 10 ⊆ nk.map.source := by
    intro z hz
    exact nk.domain ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  obtain ⟨K, hK⟩ := exists_compactDomain_of_cylinder_slab nk.map
    (by norm_num : (-10 : ℝ) < 10) hsrc
  have hU : IsOpen (nk.map '' (univ ×ˢ Ioo (-10 : ℝ) 10)) :=
    DifferentialGeometry.image_opens_isOpen nk.map
      (U := ⟨univ ×ˢ Ioo (-10 : ℝ) 10, isOpen_univ.prod isOpen_Ioo⟩)
      ((prod_mono subset_rfl Ioo_subset_Icc_self).trans hsrc)
  refine ⟨K, hK, ?_, ?_⟩
  · rw [hK]
    apply interior_maximal (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)) hU
    exact ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, nk.center_eq⟩
  · rw [hK]
    exact frontier_image_univ_prod_Icc (by norm_num) nk.map hsrc (hK ▸ K.compact.isClosed)

theorem exists_uniform_spatialNeck_canonicalWitness (B K G : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}, SpatialNeck g eps x →
        (∀ y, 1 ≤ metricScalarAt g y ∧ metricScalarAt g y ≤ B) →
        (∀ y, Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ K) →
        (∀ v : TangentSpace I3 x,
          |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) x v)| ≤
            G * Real.sqrt (g.inner x v v)) →
        ∃ W : SpatialCanonicalWitness g eps 9 C x, W.capTubeHasNeckChart eps := by
  obtain ⟨κ, hκ, hvol⟩ := exists_pos_le_spatialNeck_unit_slab_volume.{u}
  set V := κ * (2 * (K + B + 1))⁻¹ ^ 3 with hVdef
  refine ⟨max 1 (max B (max K (max G V⁻¹))), le_max_left _ _, ?_⟩
  intro M _ _ _ _ _ g eps x nk hR hRm hG
  set C := max 1 (max B (max K (max G V⁻¹))) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCB : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : K ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCG : G ≤ C := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hCV : V⁻¹ ≤ C := (((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans (hRm x)
  have hB1 : 1 ≤ B := (hR x).1.trans (hR x).2
  have hV : 0 < V := by positivity
  have hCp : 0 < C := zero_lt_one.trans_le hC1
  set Q := metricScalarAt g x with hQdef
  have hQ1 : 1 ≤ Q := (hR x).1
  have hQ : 0 < Q := zero_lt_one.trans_le hQ1
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hroot1 : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.mpr hQ1
  have hQQ : 1 ≤ Q * Real.sqrt Q := one_le_mul_of_one_le_of_one_le hQ1 hroot1
  have hsmall : (10 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
    (by linarith [nk.eps_small])
  obtain ⟨dom, hdom, hxdom, hfront⟩ := nk.exists_compactDomain_region
  have hinner : riemannianBallOf g x (9 / Real.sqrt Q) ⊆ dom.carrier := by
    have hbound : 9 ≤ 10 * Real.sqrt (1 - eps) := by
      have h : (9 / 10 : ℝ) ≤ Real.sqrt (1 - eps) := by
        apply Real.le_sqrt_of_sq_le
        linarith [nk.eps_small]
      linarith
    have hball := nk.ball_subset_image_slab (r := 10) (by norm_num) hsmall
    rw [← hQdef] at hball
    rw [hdom]
    exact (riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right hbound hroot.le)).trans hball
  have houter : dom.carrier ⊆ riemannianBallOf g x (2 * (9 / Real.sqrt Q)) := by
    have hnum : (10 + 6) * Real.sqrt (1 + eps) < 18 := by
      have hs := Real.sq_sqrt (by linarith [nk.eps_pos] : 0 ≤ 1 + eps)
      nlinarith [nk.eps_small, Real.sqrt_nonneg (1 + eps)]
    rw [hdom]
    intro y hy
    have hcb := nk.image_slab_subset_closedBall (r := 10) (by norm_num) hsmall
    rw [← hQdef] at hcb
    have hc := hcb hy
    change riemannianEDistOf g x y ≤ _ at hc
    change riemannianEDistOf g x y < _
    apply hc.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    rw [← mul_div_assoc]
    exact div_lt_div_of_pos_right (by linarith) hroot
  let data : SpatialLocalNeck g eps x dom.carrier :=
    { neck := nk
      region_eq := hdom
      boundary_eq := hfront }
  have hslab : nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ⊆ dom.carrier := by
    rw [hdom]
    exact image_mono (prod_mono subset_rfl (Icc_subset_Icc (by norm_num) (by norm_num)))
  have hvolume := (hvol nk hB1 (hR x).2 (hRm x)).trans (MeasureTheory.measure_mono hslab)
  let W : SpatialCanonicalWitness g eps 9 C x :=
    { Q_pos := hQ
      eps_pos := nk.eps_pos
      eps_lt_one := nk.eps_small.trans (by norm_num)
      domain := dom
      center_inside := hxdom
      radius := 9 / Real.sqrt Q
      radius_lower := by
        rw [← one_div]
        exact div_le_div_of_nonneg_right (by norm_num) hroot.le
      radius_upper := le_rfl
      ball_inside := hinner
      inside_ball := houter
      scalar_bounds := by
        intro y _
        have hQC : C⁻¹ * Q ≤ 1 := by
          rw [← div_eq_inv_mul, div_le_one hCp]
          exact (hR x).2.trans hCB
        exact ⟨hQC.trans (hR y).1, ((hR y).2.trans hCB).trans (le_mul_of_one_le_right hCp.le hQ1)⟩
      rm_bound := fun y _ => ((hRm y).trans hCK).trans (le_mul_of_one_le_right hCp.le hQ1)
      alternative := SpatialCanonicalAlternative.neck data
      volume := by
        intro _
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvolume
        have h1 : C⁻¹ / (Q * Real.sqrt Q) ≤ C⁻¹ :=
          div_le_self (inv_nonneg.mpr hCp.le) hQQ
        have h2 : C⁻¹ ≤ V := by
          rw [inv_le_comm₀ hCp hV]
          exact hCV
        exact h1.trans h2
      gradient := by
        intro v
        apply (hG v).trans
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have h := mul_le_mul hCG hQQ zero_le_one hCp.le
        rw [mul_one] at h
        simpa only [mul_assoc] using h }
  refine ⟨W, ?_⟩
  intro cap depth heq
  change SpatialCanonicalAlternative.neck data = _ at heq
  cases heq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

open Function DifferentialGeometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

theorem metric_pullback_linearIsometryEquiv_eq (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    (he : IsLocalDiffeomorph I3 I3 ∞ (e : ThreeSpace → ThreeSpace)) :
    pullbackMetricOfInjectiveLocalDiffeomorph metric e he e.injective = metric := by
  apply SmoothRiemannianMetric.ext_inner
  intro y v w
  rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner]
  have hd (u : TangentSpace I3 y) : mfderiv I3 I3 (e : ThreeSpace → ThreeSpace) y u =
      (show TangentSpace I3 (e y) from e u) := by
    rw [mfderiv_eq_fderiv]
    exact congrArg (fun D : ThreeSpace →L[ℝ] ThreeSpace => D u)
      e.toContinuousLinearEquiv.hasFDerivAt.fderiv
  rw [hd, hd]
  exact metric_inner_linearIsometry e.toLinearIsometry y v w

theorem nonempty_spatialNeck_of_metric_close_of_far
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (g : SmoothRiemannianMetric I3 ThreeSpace) {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 40000) (hηeps : 20000 * η ≤ eps)
    (hclose : ∀ j ≤ ⌈eps⁻¹⌉₊, ∀ y, metricDerivNorm j g metric metric y ≤ η / 2)
    {x : ThreeSpace} (hx : transitionEnd + eps⁻¹ + 1 < ‖x‖) :
    Nonempty (SpatialNeck g eps x) := by
  let e := pointedInitialRotation x
  have he : IsLocalDiffeomorph I3 I3 ∞ (e : ThreeSpace → ThreeSpace) :=
    e.toContinuousLinearEquiv.toDiffeomorph.isLocalDiffeomorph
  let g' := pullbackMetricOfInjectiveLocalDiffeomorph g e he e.injective
  have hmet := metric_pullback_linearIsometryEquiv_eq e he
  have hclose' : metricDerivENormSupOn (endNeckMap ‖x‖ eps '' controlledCylinder eps)
      ⌈eps⁻¹⌉₊ g' metric metric < ENNReal.ofReal η := by
    apply lt_of_le_of_lt _ ((ENNReal.ofReal_lt_ofReal_iff hη).mpr (half_lt_self hη))
    refine iSup_le fun j => iSup_le fun hj => iSup_le fun y => iSup_le fun _ => ?_
    apply ENNReal.ofReal_le_ofReal
    rw [← hmet, metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph]
    exact hclose j hj (e y)
  obtain ⟨nk', _, _⟩ := exists_end_spatialNeck_of_metric_close ‖x‖ eps heps hsmall hx g'
    hη hηsmall hηeps hclose'
  obtain ⟨nk, _, _, _⟩ := nk'.exists_image_of_local_isometry (e : ThreeSpace → ThreeSpace) he
    e.injective (fun y v w => (pullbackMetricOfInjectiveLocalDiffeomorph_inner g _ he
      e.injective y v w))
  have hcenter : e (‖x‖ • (spherePoint : ThreeSpace)) = x := by
    have h := pointedInitialRotation_center x
    rw [initialPolarDiffeomorph_apply, add_zero] at h
    rw [LinearIsometryEquiv.map_smul]
    exact h
  rw [hcenter] at nk
  exact ⟨nk⟩

private theorem edist_comparison_of_metric_close (g : SmoothRiemannianMetric I3 ThreeSpace)
    (h0 : ∀ y, metricDerivNorm 0 g metric metric y ≤ 1 / 10) (a b : ThreeSpace) :
    riemannianEDistOf g a b ≠ ⊤ ∧
      (riemannianEDistOf g a b).toReal ≤ 11 / 10 * (riemannianEDistOf metric a b).toReal ∧
      (riemannianEDistOf metric a b).toReal ≤ 11 / 10 * (riemannianEDistOf g a b).toReal := by
  have hb (y : ThreeSpace) (v : TangentSpace I3 y) :=
    inner_bounds_of_metricDerivNorm_le metric g y (h0 y) v
  have hup := DifferentialGeometry.edistOf_le_of_quad metric g (c := 11 / 10) (by norm_num)
    (fun y v => by linarith [(hb y v).2]) a b
  have hlo := DifferentialGeometry.edistOf_le_of_quad g metric (c := 10 / 9) (by norm_num)
    (fun y v => by linarith [(hb y v).1]) a b
  have h0top := edist_ne_top a b
  have hfin : riemannianEDistOf g a b ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h0top) hup
  have hs1 : Real.sqrt (11 / 10) ≤ 11 / 10 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs2 : Real.sqrt (10 / 9) ≤ 11 / 10 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  refine ⟨hfin, ?_, ?_⟩
  · have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h0top) hup
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h
    exact h.trans (mul_le_mul_of_nonneg_right hs1 ENNReal.toReal_nonneg)
  · have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hlo
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h
    exact h.trans (mul_le_mul_of_nonneg_right hs2 ENNReal.toReal_nonneg)

private theorem metric_distance_bounds (a b : ThreeSpace) :
    ‖b‖ - ‖a‖ ≤ (riemannianEDistOf metric a b).toReal ∧
      (riemannianEDistOf metric a b).toReal ≤ ‖a‖ + ‖b‖ := by
  constructor
  · have h := radial_difference_le_edist a b
    rw [ENNReal.ofReal_le_iff_le_toReal (edist_ne_top a b)] at h
    exact (le_abs_self _).trans h
  · have h := ENNReal.toReal_mono (_root_.edist_ne_top a b) (edist_le_euclidean a b)
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg, dist_eq_norm] at h
    exact h.trans (norm_sub_le a b)

private theorem radial_image_eq {eps r : ℝ} (hr : 1 < r) (F : Cylinder → ThreeSpace)
    (hF : ∀ z : neckBuffer eps, F z.val = (r + z.val.2) • (z.val.1 : ThreeSpace))
    (heps : 0 < eps) {S : Set ℝ} (hS : S ⊆ Icc (-1) 1) :
    F '' (univ ×ˢ S) = {y | ‖y‖ - r ∈ S} := by
  have hbuf (q : Sphere 2) {a : ℝ} (ha : a ∈ S) : (q, a) ∈ neckBuffer eps := by
    have hi := inv_pos.mpr heps
    change -eps⁻¹ - 1 < a ∧ a < eps⁻¹ + 1
    constructor <;> linarith [(hS ha).1, (hS ha).2]
  ext y
  constructor
  · rintro ⟨⟨q, a⟩, ⟨_, ha⟩, rfl⟩
    have h := hF ⟨(q, a), hbuf q ha⟩
    change F (q, a) = (r + a) • (q : ThreeSpace) at h
    change ‖F (q, a)‖ - r ∈ S
    have hpos : 0 < r + a := by linarith [(hS ha).1]
    rw [h, norm_smul, norm_eq_of_mem_sphere q, mul_one, Real.norm_eq_abs, abs_of_pos hpos]
    simpa using ha
  · intro hy
    change ‖y‖ - r ∈ S at hy
    have hpos : 0 < ‖y‖ := by linarith [(hS hy).1]
    let q : Sphere 2 := ⟨‖y‖⁻¹ • y, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']⟩
    refine ⟨(q, ‖y‖ - r), ⟨mem_univ _, hy⟩, ?_⟩
    have h := hF ⟨(q, ‖y‖ - r), hbuf q hy⟩
    change F (q, ‖y‖ - r) = (r + (‖y‖ - r)) • (‖y‖⁻¹ • y) at h
    rw [h, add_sub_cancel, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

theorem exists_uniform_tip_spatialCanonicalWitness_of_metric_close
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (B K G : ℝ) :
    ∃ r C1 C2 : ℝ, transitionEnd + eps⁻¹ + 2 ≤ (r + 1) / 10 ∧ 1 ≤ C2 ∧
      ∀ g : SmoothRiemannianMetric I3 ThreeSpace,
        (∀ y, 1 ≤ metricScalarAt g y ∧ metricScalarAt g y ≤ B) →
        (∀ y, Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ K) →
        (∀ j ≤ ⌈eps⁻¹⌉₊, ∀ y, metricDerivNorm j g metric metric y ≤
          min (1 / 40000) (eps / 20000) / 2) →
        ∀ x : ThreeSpace, ‖x‖ ≤ (r + 1) / 10 →
        (∀ v : TangentSpace I3 x,
          |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) x v)| ≤
            G * Real.sqrt (g.inner x v v)) →
        ∃ W : SpatialCanonicalWitness g eps C1 C2 x, W.capTubeHasNeckChart eps := by
  obtain ⟨κ, hκ, hvol⟩ := exists_pos_le_spatialNeck_unit_slab_volume.{0}
  set V := κ * (2 * (K + B + 1))⁻¹ ^ 3 with hVdef
  set r := max 20000 (10 * (transitionEnd + eps⁻¹ + 2)) with hrdef
  have hr20 : 20000 ≤ r := le_max_left _ _
  have hrT : 10 * (transitionEnd + eps⁻¹ + 2) ≤ r := le_max_right _ _
  have hi : 0 < eps⁻¹ := inv_pos.mpr heps
  have hi11 : (11 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) heps).mpr (by linarith)
  have hT := transitionEnd_pos
  set ρ := 7 * (r + 1) / 10 with hρdef
  refine ⟨r, ρ * B, max 1 (max B (max K (max G V⁻¹))), by linarith, le_max_left _ _, ?_⟩
  intro g hR hRm hclose x hx hG
  set C := max 1 (max B (max K (max G V⁻¹))) with hCdef
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCB : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : K ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCG : G ≤ C := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hCV : V⁻¹ ≤ C := (((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans (le_max_right _ _)
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans (hRm x)
  have hB1 : 1 ≤ B := (hR x).1.trans (hR x).2
  have hV : 0 < V := by positivity
  have hCp : 0 < C := zero_lt_one.trans_le hC1
  set Q := metricScalarAt g x with hQdef
  have hQ1 : 1 ≤ Q := (hR x).1
  have hQ : 0 < Q := zero_lt_one.trans_le hQ1
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hroot1 : 1 ≤ Real.sqrt Q := Real.one_le_sqrt.mpr hQ1
  have hrootB : Real.sqrt Q ≤ B := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith [(hR x).2]
  have hQQ : 1 ≤ Q * Real.sqrt Q := one_le_mul_of_one_le_of_one_le hQ1 hroot1
  set η₀ := min (1 / 40000) (eps / 20000) with hη₀def
  have hη₀ : 0 < η₀ := lt_min (by norm_num) (by positivity)
  have hη₀small : η₀ ≤ 1 / 40000 := min_le_left _ _
  have hη₀eps : 20000 * η₀ ≤ eps := by
    have h := min_le_right (1 / 40000 : ℝ) (eps / 20000)
    linarith
  have hsup : metricDerivENormSupOn (endNeckMap r eps '' controlledCylinder eps) ⌈eps⁻¹⌉₊
      g metric metric < ENNReal.ofReal η₀ := by
    apply lt_of_le_of_lt _ ((ENNReal.ofReal_lt_ofReal_iff hη₀).mpr (half_lt_self hη₀))
    exact iSup_le fun j => iSup_le fun hj => iSup_le fun y => iSup_le fun _ =>
      ENNReal.ofReal_le_ofReal (hclose j hj y)
  have hrend : transitionEnd + eps⁻¹ + 1 < r := by linarith
  have hr1 : (1 : ℝ) < r := by linarith
  obtain ⟨nk1, hmap1, K1, hK1, _, _, _, _, _, _⟩ :=
    exists_spatial_cap_frontier_of_metric_close heps hsmall hrend (s := 1)
      ⟨by linarith, by linarith⟩ g hη₀ hη₀small hη₀eps hsup
  obtain ⟨_, _, K0, hK0, hcore0, _, _, _, _, _⟩ :=
    exists_spatial_cap_frontier_of_metric_close heps hsmall hrend (s := 0)
      ⟨by linarith, by linarith⟩ g hη₀ hη₀small hη₀eps hsup
  rw [add_zero] at hK0
  have himg := fun {S : Set ℝ} (hS : S ⊆ Icc (-1) 1) =>
    radial_image_eq hr1 nk1.map hmap1 heps hS
  have hIcc : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := Icc_subset_Icc (by norm_num) le_rfl
  have htubeeq := himg hIcc
  have hdomain : univ ×ˢ Icc (0 : ℝ) 1 ⊆ nk1.map.source := fun z hz =>
    nk1.domain ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hr0 : r ≠ 0 := by linarith
  have hr10 : r + 1 ≠ 0 := by linarith
  have hfront0 : frontier K0.carrier = Metric.sphere 0 r := by
    rw [hK0, frontier_closedBall _ hr0]
  have hfront1 : frontier K1.carrier = Metric.sphere 0 (r + 1) := by
    rw [hK1, frontier_closedBall _ hr10]
  have hsph (a : ℝ) (ha : a ∈ Icc (-1 : ℝ) 1) :
      nk1.map '' (univ ×ˢ ({a} : Set ℝ)) = Metric.sphere 0 (r + a) := by
    rw [himg (singleton_subset_iff.mpr ha)]
    ext y
    simp only [mem_ofPred_eq, mem_singleton_iff, mem_sphere_zero_iff_norm]
    constructor <;> intro h <;> linarith
  have hsph0 := hsph 0 ⟨by norm_num, by norm_num⟩
  have hsph1 := hsph 1 ⟨by norm_num, le_rfl⟩
  rw [add_zero] at hsph0
  have hclosedTube : IsClosed (nk1.map '' (univ ×ˢ Icc (0 : ℝ) 1)) := by
    rw [htubeeq]
    exact isClosed_Icc.preimage (continuous_norm.sub continuous_const)
  let chain : SpatialOrderedNeckChain g eps (nk1.map '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
    { count := 1
      count_pos := one_pos
      centers := fun _ => r • (spherePoint : ThreeSpace)
      necks := fun _ => nk1
      lo := fun _ => 0
      hi := fun _ => 1
      lo_lt_hi := fun _ => one_pos
      inside := fun _ => hdomain
      swept_eq := (iUnion_const _).symm
      transition_increasing := by
        intro i j hij
        have := i.isLt
        have := j.isLt
        omega }
  have hxr : ‖x‖ < r := by linarith
  let cap : SpatialLocalCap g eps x K1.carrier :=
    { core := K0
      core_inside := by
        rw [hK0, hK1, interior_closedBall _ hr10]
        exact Metric.closedBall_subset_ball (lt_add_one r)
      center_inside := by
        rw [hK0, interior_closedBall _ hr0, mem_ball_zero_iff]
        exact hxr
      coreModel := Classical.choice hcore0
      tube := nk1.map '' (univ ×ˢ Icc (0 : ℝ) 1)
      tubeMap := nk1.map
      tube_domain := hdomain
      tube_eq := rfl
      union_eq := by
        rw [hK1, hK0, htubeeq]
        ext y
        simp only [Metric.mem_closedBall, dist_zero_right, mem_union, mem_ofPred_eq, mem_Icc]
        constructor
        · intro h
          by_cases hy : ‖y‖ ≤ r
          · exact Or.inl hy
          · exact Or.inr ⟨by linarith, by linarith⟩
        · rintro (h | h)
          · linarith
          · linarith [h.2]
      overlap_eq := by
        rw [hfront0, hK0, htubeeq]
        ext y
        simp only [Metric.mem_closedBall, dist_zero_right, mem_inter_iff, mem_ofPred_eq, mem_Icc,
          mem_sphere_zero_iff_norm]
        constructor
        · rintro ⟨h1, h2, _⟩
          linarith
        · intro h
          exact ⟨h.le, by linarith, by linarith⟩
      inner_boundary := hsph0.trans hfront0.symm
      outer_boundary := hsph1.trans hfront1.symm
      boundary_eq := by
        rw [frontier_image_univ_prod_Icc zero_le_one nk1.map hdomain hclosedTube, hfront0,
          hfront1, ← hsph0, ← hsph1, ← image_union, ← prod_union]
        rfl
      boundaries_disjoint := by
        rw [hfront0, hfront1, Set.disjoint_left]
        intro y h1 h2
        rw [mem_sphere_zero_iff_norm] at h1 h2
        linarith
      chain := chain
      coreBoundaryMap := fun z => nk1.map (z, 0)
      core_boundary_eq := fun _ => rfl }
  have hh0 : ∀ y, metricDerivNorm 0 g metric metric y ≤ 1 / 10 := fun y =>
    (hclose 0 (Nat.zero_le _) y).trans (by linarith)
  have hcmp := edist_comparison_of_metric_close g hh0
  have hdepth : ∀ y ∈ cap.tube, 10000 / Real.sqrt Q ≤ metricDistance g x y := by
    intro y hy
    change y ∈ nk1.map '' (univ ×ˢ Icc (0 : ℝ) 1) at hy
    rw [htubeeq] at hy
    have hyr : r ≤ ‖y‖ := by linarith [hy.1]
    have h1 := (hcmp x y).2.2
    have h2 := (metric_distance_bounds x y).1
    have h3 : 10000 / Real.sqrt Q ≤ 10000 := div_le_self (by norm_num) hroot1
    change 10000 / Real.sqrt Q ≤ (riemannianEDistOf g x y).toReal
    nlinarith
  have hxin : x ∈ interior K1.carrier := by
    rw [hK1, interior_closedBall _ hr10, mem_ball_zero_iff]
    linarith
  have hball : riemannianBallOf g x ρ ⊆ K1.carrier := by
    intro y hy
    change riemannianEDistOf g x y < ENNReal.ofReal ρ at hy
    rw [ENNReal.lt_ofReal_iff_toReal_lt (hcmp x y).1] at hy
    rw [hK1, Metric.mem_closedBall, dist_zero_right]
    have h1 := (hcmp x y).2.2
    have h2 := (metric_distance_bounds x y).1
    nlinarith
  have hout : K1.carrier ⊆ riemannianBallOf g x (2 * ρ) := by
    intro y hy
    rw [hK1, Metric.mem_closedBall, dist_zero_right] at hy
    change riemannianEDistOf g x y < ENNReal.ofReal (2 * ρ)
    rw [ENNReal.lt_ofReal_iff_toReal_lt (hcmp x y).1]
    have h1 := (hcmp x y).2.1
    have h2 := (metric_distance_bounds x y).2
    nlinarith [norm_nonneg x]
  have hslab : nk1.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ⊆ K1.carrier := by
    rw [himg le_rfl, hK1]
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [hy.2]
  have hvolume := (hvol nk1 hB1 (hR _).2 (hRm _)).trans (MeasureTheory.measure_mono hslab)
  let W : SpatialCanonicalWitness g eps (ρ * B) C x :=
    { Q_pos := hQ
      eps_pos := heps
      eps_lt_one := hsmall.trans (by norm_num)
      domain := K1
      center_inside := hxin
      radius := ρ
      radius_lower := by
        have : (Real.sqrt Q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hroot1
        linarith
      radius_upper := by
        rw [le_div_iff₀ hroot]
        exact mul_le_mul_of_nonneg_left hrootB (by positivity)
      ball_inside := hball
      inside_ball := hout
      scalar_bounds := by
        intro y _
        have hQC : C⁻¹ * Q ≤ 1 := by
          rw [← div_eq_inv_mul, div_le_one hCp]
          exact (hR x).2.trans hCB
        exact ⟨hQC.trans (hR y).1, ((hR y).2.trans hCB).trans (le_mul_of_one_le_right hCp.le hQ1)⟩
      rm_bound := fun y _ => ((hRm y).trans hCK).trans (le_mul_of_one_le_right hCp.le hQ1)
      alternative := SpatialCanonicalAlternative.cap cap hdepth
      volume := by
        intro _
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvolume
        have h1 : C⁻¹ / (Q * Real.sqrt Q) ≤ C⁻¹ :=
          div_le_self (inv_nonneg.mpr hCp.le) hQQ
        have h2 : C⁻¹ ≤ V := by
          rw [inv_le_comm₀ hCp hV]
          exact hCV
        exact h1.trans h2
      gradient := by
        intro v
        apply (hG v).trans
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        have h := mul_le_mul hCG hQQ zero_le_one hCp.le
        rw [mul_one] at h
        simpa only [mul_assoc] using h }
  refine ⟨W, ?_⟩
  intro cap' depth' heq
  change SpatialCanonicalAlternative.cap cap hdepth = _ at heq
  cases heq
  exact ⟨_, nk1, fun _ => rfl⟩

theorem exists_uniform_spatialCanonicalWitness_of_metric_close
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (B K G : ℝ) :
    ∃ η C : ℝ, 0 < η ∧ 1 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I3 ThreeSpace,
        (∀ y, 1 ≤ metricScalarAt g y ∧ metricScalarAt g y ≤ B) →
        (∀ y, Real.sqrt (normSq0S g y 4 (metricRm04 g y)) ≤ K) →
        (∀ y (v : TangentSpace I3 y),
          |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt g) y v)| ≤
            G * Real.sqrt (g.inner y v v)) →
        (∀ j ≤ ⌈eps⁻¹⌉₊, ∀ y, metricDerivNorm j g metric metric y ≤ η) →
        ∀ x, ∃ W : SpatialCanonicalWitness g eps C C x, W.capTubeHasNeckChart eps := by
  obtain ⟨r, C1, C2, hr, hC2, htip⟩ :=
    exists_uniform_tip_spatialCanonicalWitness_of_metric_close heps hsmall B K G
  obtain ⟨Cn, hCn, hneck⟩ := exists_uniform_spatialNeck_canonicalWitness.{0} B K G
  set η₀ := min (1 / 40000) (eps / 20000) with hη₀def
  have hη₀ : 0 < η₀ := lt_min (by norm_num) (by positivity)
  have hη₀small : η₀ ≤ 1 / 40000 := min_le_left _ _
  have hη₀eps : 20000 * η₀ ≤ eps := by
    have h := min_le_right (1 / 40000 : ℝ) (eps / 20000)
    linarith
  set C := max 9 (max C1 (max C2 Cn)) with hCdef
  have h9 : (9 : ℝ) ≤ C := le_max_left _ _
  have hC1 : C1 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC2' : C2 ≤ C := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hCn' : Cn ≤ C := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨η₀ / 2, C, half_pos hη₀, by linarith, ?_⟩
  intro g hR hRm hG hclose x
  by_cases hx : ‖x‖ ≤ (r + 1) / 10
  · obtain ⟨W, hW⟩ := htip g hR hRm hclose x hx (hG x)
    exact ⟨W.enlargeConstants hC1 hC2', hW.enlarge_constants hC1 hC2'⟩
  · have hfar : transitionEnd + eps⁻¹ + 1 < ‖x‖ := by linarith
    obtain ⟨nk⟩ := nonempty_spatialNeck_of_metric_close_of_far heps hsmall g hη₀ hη₀small
      hη₀eps hclose hfar
    obtain ⟨W, hW⟩ := hneck nk hR hRm (hG x)
    exact ⟨W.enlargeConstants h9 hCn', hW.enlarge_constants h9 hCn'⟩

end DifferentialGeometry.PDE.RicciFlow.StandardCap

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

theorem StandardSolution.exists_initial_spatialCanonicalWitness_with_cap_neck_charts
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ τ C : ℝ, 0 < τ ∧ 1 ≤ C ∧ ∀ (S : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
      t ∈ Icc 0 τ →
        ∃ W : SpatialCanonicalWitness (S.val.metric t) eps C C x, W.capTubeHasNeckChart eps := by
  obtain ⟨α, hα, K, hK, hcurv⟩ := standard_uniform_initial_curvature_control
  have hhalf : ENNReal.ofReal (1 / 2) < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by norm_num)
  obtain ⟨Cd, hCd, hder⟩ :=
    uniformStandardLifetime_curvature_derivative_bounds_closed (1 / 2) (by norm_num) hhalf 1
  obtain ⟨η, C, hη, hC, hstatic⟩ :=
    StandardCap.exists_uniform_spatialCanonicalWitness_of_metric_close heps hsmall
      (9 * K) K (9 * Cd)
  obtain ⟨α₂, hα₂, _, _, _, L, _, hL, hstd⟩ := standard_uniform_fixed_cap_metric_bounds
  set k := ⌈eps⁻¹⌉₊ with hkdef
  set Lsum := ∑ j ∈ Finset.range (k + 1), L j with hLsum
  have hLsum0 : 0 ≤ Lsum := Finset.sum_nonneg fun j _ => hL j
  set τ := min α (min α₂ (min (1 / 2) (η / (Lsum + 1)))) with hτdef
  have hτ : 0 < τ := lt_min hα (lt_min hα₂ (lt_min (by norm_num) (by positivity)))
  have hτα : τ ≤ α := min_le_left _ _
  have hτα₂ : τ ≤ α₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hτhalf : τ ≤ 1 / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hτη : τ ≤ η / (Lsum + 1) :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨τ, C, hτ, hC, ?_⟩
  intro S x t ht
  have hlife : ENNReal.ofReal τ < S.val.lifetime := by
    rw [S.lifetime_eq_one, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr (by linarith)
  have hdom : t ∈ S.val.domain := by
    refine (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mpr ⟨ht.1, ?_⟩
    exact (ENNReal.ofReal_le_ofReal ht.2).trans_lt hlife
  have hRm : ∀ y, Real.sqrt (normSq0S (S.val.metric t) y 4 (metricRm04 (S.val.metric t) y)) ≤ K :=
    fun y => hcurv S.val τ hτ.le hτα hlife t ht y
  have hR : ∀ y, 1 ≤ metricScalarAt (S.val.metric t) y ∧
      metricScalarAt (S.val.metric t) y ≤ 9 * K := by
    intro y
    refine ⟨S.val.one_le_scalar t hdom y, ?_⟩
    have hrm := hRm y
    rw [metricRm04_apply] at hrm
    have habs := scalar_abs_le_rm (S.val.metric t) y
    have hdim : (Module.finrank ℝ (TangentSpace (𝓡 3) y) : ℝ) = 3 := by
      rw [show Module.finrank ℝ (TangentSpace (𝓡 3) y) = 3 from finrank_euclideanSpace_fin]
      norm_num
    rw [hdim] at habs
    have hle : (3 : ℝ) ^ 2 *
        Real.sqrt (normSq0S (S.val.metric t) y 4 (metricRm04At (S.val.metric t) y)) ≤ 9 * K := by
      nlinarith
    exact (le_abs_self _).trans (habs.trans hle)
  have hG : ∀ y (v : TangentSpace I3 y),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (S.val.metric t)) y v)| ≤
        9 * Cd * Real.sqrt ((S.val.metric t).inner y v v) := by
    intro y v
    have h := Perelman.CanonicalNeighborhood.abs_scalarDifferential_le S.val.toSolutionOn t y v
    have hd := hder S 1 le_rfl t ⟨ht.1, ht.2.trans hτhalf⟩ y
    have hdim : (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 = 9 := by
      rw [show Module.finrank ℝ ThreeSpace = 3 from finrank_euclideanSpace_fin]
      norm_num
    rw [hdim] at h
    refine h.trans ?_
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg _)) (by norm_num)
  have hclose : ∀ j ≤ k, ∀ y,
      metricDerivNorm j (S.val.metric t) StandardCap.metric StandardCap.metric y ≤ η := by
    intro j hj y
    have hm := (hstd S.val τ hτ.le hτα₂ hlife).2.2 j t ht 0 ⟨le_rfl, hτ.le⟩ y
    rw [S.val.initial, sub_zero, abs_of_nonneg ht.1] at hm
    have hLj : L j ≤ Lsum := Finset.single_le_sum (fun i _ => hL i)
      (Finset.mem_range.mpr (by omega))
    have ht' : t ≤ η / (Lsum + 1) := ht.2.trans hτη
    have h1 : L j * t ≤ Lsum * t := mul_le_mul_of_nonneg_right hLj ht.1
    have h2 : Lsum * t ≤ η := by
      rw [le_div_iff₀ (by linarith)] at ht'
      nlinarith
    linarith
  exact hstatic (S.val.metric t) hR hRm hG hclose x

end DifferentialGeometry.PDE.RicciFlow
