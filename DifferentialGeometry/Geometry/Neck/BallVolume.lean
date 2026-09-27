import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckSpatialBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.VolumeTransport
import DifferentialGeometry.Geometry.Measure.RoundCylinderBallVolume
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance

noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private theorem cylinder_metric_zero_eq_round (C : CylinderReference) :
    C.metric 0 = Geometry.Metric.roundCylinderMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  have hC := C.inner_eq 0 le_rfl z v w
  apply hC.trans
  rw [Geometry.Metric.roundCylinderMetric_inner]
  simp only [sub_zero, mul_one]
  rfl

theorem exists_pos_le_spatialNeck_normalized_ball_volume {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ v : ℝ, 0 < v ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M],
        ∀ {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
          (nk : SpatialNeck g eps p) (z : Cylinder),
          |z.2| + ρ < eps⁻¹ →
          ENNReal.ofReal v ≤ riemannianVolumeMeasure I3 M
            (scaleMetric (metricScalarAt g p) nk.Q_pos g)
            (riemannianBallOf (scaleMetric (metricScalarAt g p) nk.Q_pos g) (nk.map z) ρ) := by
  obtain ⟨v, hv, hvol⟩ := Geometry.Measure.exists_pos_le_riemannianVolumeMeasure_roundCylinder_ball
    (E := ThreeSpace) (n := 2) (by positivity : 0 < ρ / 4)
  refine ⟨v / 4, by positivity, ?_⟩
  intro M _ _ _ _ _ g eps p nk z hz
  let h := nk.cylinder.metric 0
  let gn := scaleMetric (metricScalarAt g p) nk.Q_pos g
  let U : Set Cylinder := univ ×ˢ Ioo (-eps⁻¹) eps⁻¹
  let K := riemannianClosedBallOf h z (ρ / 4)
  have hsub : riemannianClosedBallOf h z ρ ⊆ U := by
    intro y hy
    have hh := nk.cylinder.closedBall_subset_slab z hρ.le hy
    exact ⟨mem_univ _, by constructor <;> linarith [hh.2.1, hh.2.2, neg_abs_le z.2, le_abs_self z.2]⟩
  have hKsub : K ⊆ U := by
    intro y hy
    exact hsub (hy.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have hK : IsCompact K := nk.cylinder.isCompact_closedBall z (by positivity)
  have hge := MetricComparisonOn.volume_image_ge nk.map nk.comparison
    (by simp : (0 : ℝ) ∈ ({0} : Set ℝ)) nk.eps_pos.le (by linarith [nk.eps_small])
    (isOpen_univ.prod isOpen_Ioo) Subset.rfl nk.domain hK hKsub
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim] at hge
  have hreference : ENNReal.ofReal v ≤ riemannianVolumeMeasure IC Cylinder h K := by
    have hh := hvol z
    rw [← cylinder_metric_zero_eq_round nk.cylinder] at hh
    exact hh.trans (measure_mono (show riemannianBallOf (nk.cylinder.metric 0) z (ρ / 4) ⊆ K from
      by
        intro y hy
        change riemannianEDistOf (nk.cylinder.metric 0) z y ≤ ENNReal.ofReal (ρ / 4)
        exact hy.le))
  have hfactor : (1 / 4 : ℝ) ≤ Real.sqrt ((1-eps)^3) := by
    have heps : eps < 1 / 11 := nk.eps_small
    have he : 1 / 2 ≤ 1 - eps := by linarith
    have hs := Real.sq_sqrt (show 0 ≤ (1-eps)^3 by positivity)
    have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) he 3
    nlinarith [Real.sqrt_nonneg ((1-eps)^3)]
  have himage : nk.map '' K ⊆ riemannianBallOf gn (nk.map z) ρ := by
    rintro _ ⟨y, hy, rfl⟩
    have hupper : ∀ q ∈ riemannianClosedBallOf h z ρ, ∀ v : TangentSpace IC q,
        gn.inner (nk.map q) (mfderiv IC I3 nk.map q v) (mfderiv IC I3 nk.map q v) ≤
          (2 : ℝ)^2 * h.inner q v v := by
      intro q hq v
      have hh := (nk.comparison.equivalence 0 (by simp) q (hsub hq) v).2
      rw [nk.comparison.pullback_eq 0 q (hsub hq) (fun _ => v)] at hh
      have hnn : 0 ≤ h.inner q v v := by
        by_cases hv : v = 0
        · simp [hv]
        · exact (h.pos q v hv).le
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith [nk.eps_small]) hnn)
    have hd := KappaSolutions.edistOf_map_le_of_metric_upper_on_ball h gn nk.map z y
      hρ (by norm_num : (0 : ℝ) < 2) (hsub.trans nk.domain) hupper
      (hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr (by linarith)))
    apply hd.trans_lt
    calc ENNReal.ofReal 2 * riemannianEDistOf h z y
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal (ρ / 4) := mul_le_mul' le_rfl hy
      _ = ENNReal.ofReal (ρ / 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ < ENNReal.ofReal ρ := (ENNReal.ofReal_lt_ofReal_iff hρ).mpr (by linarith)
  calc ENNReal.ofReal (v / 4)
      = ENNReal.ofReal (1/4 : ℝ) * ENNReal.ofReal v := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (Real.sqrt ((1-eps)^3)) * riemannianVolumeMeasure IC Cylinder h K :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor) hreference
    _ ≤ riemannianVolumeMeasure I3 M gn (nk.map '' K) := hge
    _ ≤ riemannianVolumeMeasure I3 M gn (riemannianBallOf gn (nk.map z) ρ) :=
      measure_mono himage

theorem exists_pos_le_normalizedNeck_ball_volume {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ v : ℝ, 0 < v ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M],
        ∀ {g : SmoothRiemannianMetric I3 M} {δ eps : ℝ} {k : ℕ}
          (N : NormalizedNeck g δ k), δ ≤ eps → eps < 1 / 11 → ⌈eps⁻¹⌉₊ ≤ k →
          ∀ {a : ℝ}, 0 < a → 2*a + ρ < eps⁻¹ →
          ∀ x ∈ riemannianClosedBallOf (scaleMetric N.scale N.scale_pos g) N.center a,
            ENNReal.ofReal v ≤ riemannianVolumeMeasure I3 M
              (scaleMetric N.scale N.scale_pos g)
              (riemannianBallOf (scaleMetric N.scale N.scale_pos g) x ρ) := by
  obtain ⟨v,hv,hvol⟩ := exists_pos_le_spatialNeck_normalized_ball_volume.{u} hρ
  refine ⟨v,hv,?_⟩
  intro M _ _ _ _ _ g δ eps k N hδ heps hk a ha hfit x hx
  obtain ⟨nk,_,hmap⟩ := N.exists_spatialNeck hδ heps hk
  have hQ := Real.sqrt_pos.mpr N.scale_pos
  have hball := riemannianClosedBallOf_scaleMetric N.scale N.scale_pos g N.center
    (a / Real.sqrt N.scale)
  have hcancel : Real.sqrt N.scale * (a / Real.sqrt N.scale) = a := by field_simp
  rw [hcancel] at hball
  rw [hball] at hx
  have hsqrt : 1 / 2 < Real.sqrt (1-eps) := by
    have hh := Real.sq_sqrt (by linarith : 0 ≤ 1-eps)
    nlinarith [Real.sqrt_nonneg (1-eps)]
  have hsmall : 2*a < eps⁻¹ := by linarith
  have hcapture := nk.ball_subset_image_slab (by positivity : 0 < 2*a) hsmall
  have hin : x ∈ riemannianBallOf g N.center
      ((2*a)*Real.sqrt (1-eps)/Real.sqrt (metricScalarAt g N.center)) := by
    rw [← N.scale_scalar]
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (div_lt_div_of_pos_right (by nlinarith) hQ))
  obtain ⟨z,hz,rfl⟩ := hcapture hin
  have hh := hvol nk z (by
    have hzabs : |z.2| ≤ 2*a := abs_le.mpr hz.2
    linarith)
  simpa only [← N.scale_scalar] using hh

theorem exists_pos_mul_cube_le_spatialNeck_normalized_ball_volume :
    ∃ v : ℝ, 0 < v ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M],
        ∀ {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}
          (nk : SpatialNeck g eps p) (z : Cylinder) (r : ℝ),
          0 < r → r ≤ 1 → |z.2| + r < eps⁻¹ →
          ENNReal.ofReal (v * r ^ 3) ≤ riemannianVolumeMeasure I3 M
            (scaleMetric (metricScalarAt g p) nk.Q_pos g)
            (riemannianBallOf (scaleMetric (metricScalarAt g p) nk.Q_pos g) (nk.map z) r) := by
  obtain ⟨ν, hν, hvol⟩ :=
    Geometry.Measure.exists_pos_mul_cube_le_riemannianVolumeMeasure_roundCylinder_ball
      (E := ThreeSpace)
  refine ⟨ν / 256, by positivity, ?_⟩
  intro M _ _ _ _ _ g eps p nk z r hr hrone hz
  let h := nk.cylinder.metric 0
  let gn := scaleMetric (metricScalarAt g p) nk.Q_pos g
  let U : Set Cylinder := univ ×ˢ Ioo (-eps⁻¹) eps⁻¹
  let K := riemannianClosedBallOf h z (r / 4)
  have hsub : riemannianClosedBallOf h z r ⊆ U := by
    intro y hy
    have hh := nk.cylinder.closedBall_subset_slab z hr.le hy
    exact ⟨mem_univ _, by constructor <;> linarith [hh.2.1, hh.2.2, neg_abs_le z.2, le_abs_self z.2]⟩
  have hKsub : K ⊆ U := by
    intro y hy
    exact hsub (hy.trans (ENNReal.ofReal_le_ofReal (by linarith)))
  have hK : IsCompact K := nk.cylinder.isCompact_closedBall z (by positivity)
  have hge := MetricComparisonOn.volume_image_ge nk.map nk.comparison
    (by simp : (0 : ℝ) ∈ ({0} : Set ℝ)) nk.eps_pos.le (by linarith [nk.eps_small])
    (isOpen_univ.prod isOpen_Ioo) Subset.rfl nk.domain hK hKsub
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim] at hge
  have hreference : ENNReal.ofReal (ν * (r / 4) ^ 3) ≤ riemannianVolumeMeasure IC Cylinder h K := by
    have hh := hvol z (r / 4) (by positivity) (by linarith)
    rw [← cylinder_metric_zero_eq_round nk.cylinder] at hh
    exact hh.trans (measure_mono (show riemannianBallOf (nk.cylinder.metric 0) z (r / 4) ⊆ K from
      by
        intro y hy
        change riemannianEDistOf (nk.cylinder.metric 0) z y ≤ ENNReal.ofReal (r / 4)
        exact hy.le))
  have hfactor : (1 / 4 : ℝ) ≤ Real.sqrt ((1-eps)^3) := by
    have heps : eps < 1 / 11 := nk.eps_small
    have he : 1 / 2 ≤ 1 - eps := by linarith
    have hs := Real.sq_sqrt (show 0 ≤ (1-eps)^3 by positivity)
    have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) he 3
    nlinarith [Real.sqrt_nonneg ((1-eps)^3)]
  have himage : nk.map '' K ⊆ riemannianBallOf gn (nk.map z) r := by
    rintro _ ⟨y, hy, rfl⟩
    have hupper : ∀ q ∈ riemannianClosedBallOf h z r, ∀ v : TangentSpace IC q,
        gn.inner (nk.map q) (mfderiv IC I3 nk.map q v) (mfderiv IC I3 nk.map q v) ≤
          (2 : ℝ)^2 * h.inner q v v := by
      intro q hq v
      have hh := (nk.comparison.equivalence 0 (by simp) q (hsub hq) v).2
      rw [nk.comparison.pullback_eq 0 q (hsub hq) (fun _ => v)] at hh
      have hnn : 0 ≤ h.inner q v v := by
        by_cases hv : v = 0
        · simp [hv]
        · exact (h.pos q v hv).le
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith [nk.eps_small]) hnn)
    have hd := KappaSolutions.edistOf_map_le_of_metric_upper_on_ball h gn nk.map z y
      hr (by norm_num : (0 : ℝ) < 2) (hsub.trans nk.domain) hupper
      (hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith)))
    apply hd.trans_lt
    calc ENNReal.ofReal 2 * riemannianEDistOf h z y
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal (r / 4) := mul_le_mul' le_rfl hy
      _ = ENNReal.ofReal (r / 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith)
  calc ENNReal.ofReal ((ν / 256) * r ^ 3)
      = ENNReal.ofReal (1/4 : ℝ) * ENNReal.ofReal (ν * (r / 4) ^ 3) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (Real.sqrt ((1-eps)^3)) * riemannianVolumeMeasure IC Cylinder h K :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor) hreference
    _ ≤ riemannianVolumeMeasure I3 M gn (nk.map '' K) := hge
    _ ≤ riemannianVolumeMeasure I3 M gn (riemannianBallOf gn (nk.map z) r) :=
      measure_mono himage

theorem exists_pos_mul_cube_le_normalizedNeck_ball_volume :
    ∃ v : ℝ, 0 < v ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M],
        ∀ {g : SmoothRiemannianMetric I3 M} {δ eps : ℝ} {k : ℕ}
          (N : NormalizedNeck g δ k), δ ≤ eps → eps < 1 / 11 → ⌈eps⁻¹⌉₊ ≤ k →
          ∀ {a r : ℝ}, 0 < a → 0 < r → r ≤ 1 → 2*a + r < eps⁻¹ →
          ∀ x ∈ riemannianClosedBallOf (scaleMetric N.scale N.scale_pos g) N.center a,
            ENNReal.ofReal (v * r ^ 3) ≤ riemannianVolumeMeasure I3 M
              (scaleMetric N.scale N.scale_pos g)
              (riemannianBallOf (scaleMetric N.scale N.scale_pos g) x r) := by
  obtain ⟨v,hv,hvol⟩ := exists_pos_mul_cube_le_spatialNeck_normalized_ball_volume.{u}
  refine ⟨v,hv,?_⟩
  intro M _ _ _ _ _ g δ eps k N hδ heps hk a r ha hr hrone hfit x hx
  obtain ⟨nk,_,_⟩ := N.exists_spatialNeck hδ heps hk
  have hQ := Real.sqrt_pos.mpr N.scale_pos
  have hball := riemannianClosedBallOf_scaleMetric N.scale N.scale_pos g N.center
    (a / Real.sqrt N.scale)
  have hcancel : Real.sqrt N.scale * (a / Real.sqrt N.scale) = a := by field_simp
  rw [hcancel] at hball
  rw [hball] at hx
  have hsqrt : 1 / 2 < Real.sqrt (1-eps) := by
    have hh := Real.sq_sqrt (by linarith : 0 ≤ 1-eps)
    nlinarith [Real.sqrt_nonneg (1-eps)]
  have hsmall : 2*a < eps⁻¹ := by linarith
  have hcapture := nk.ball_subset_image_slab (by positivity : 0 < 2*a) hsmall
  have hin : x ∈ riemannianBallOf g N.center
      ((2*a)*Real.sqrt (1-eps)/Real.sqrt (metricScalarAt g N.center)) := by
    rw [← N.scale_scalar]
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (div_lt_div_of_pos_right (by nlinarith) hQ))
  obtain ⟨z,hz,rfl⟩ := hcapture hin
  have hh := hvol nk z r hr hrone (by
    have hzabs : |z.2| ≤ 2*a := abs_le.mpr hz.2
    linarith)
  simpa only [← N.scale_scalar] using hh


open DifferentialGeometry.Tensor0SBundle

private theorem sqrt_mul_radius_le_three_of_curvature_bound
    {R A r : ℝ} (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hscalar : R ≤ 9 * Real.sqrt A) (hcurv : r ^ 4 * A ≤ 1) :
    Real.sqrt R * r ≤ 3 := by
  have hsA : (r ^ 2 * Real.sqrt A) ^ 2 ≤ 1 := by
    rw [mul_pow, ← pow_mul, Real.sq_sqrt hA]
    exact hcurv
  have hsmall : r ^ 2 * Real.sqrt A ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg r) (Real.sqrt_nonneg A)]
  have hscaled := mul_le_mul_of_nonneg_right hscalar (sq_nonneg r)
  have hsR : (Real.sqrt R * r) ^ 2 ≤ 9 := by
    rw [mul_pow, Real.sq_sqrt hR]
    nlinarith
  nlinarith

theorem exists_pos_mul_cube_le_spatialNeck_ball_volume_of_curvature_bound :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M],
        ∀ {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M},
          SpatialNeck g eps p → ∀ r : ℝ, 0 < r →
          r ^ 4 * normSq0S g p 4 (metricRm04At g p) ≤ 1 →
          ENNReal.ofReal (κ * r ^ 3) ≤ riemannianVolumeMeasure I3 M g (riemannianBallOf g p r) := by
  obtain ⟨ν, hν, hvol⟩ := exists_pos_mul_cube_le_spatialNeck_normalized_ball_volume.{u}
  refine ⟨ν / 27, by positivity, ?_⟩
  intro M _ _ _ _ _ g eps p nk r hr htest
  let Q := metricScalarAt g p
  let ρ := Real.sqrt Q * r
  let gn := scaleMetric Q nk.Q_pos g
  have hρ : 0 < ρ := mul_pos (Real.sqrt_pos.mpr nk.Q_pos) hr
  have hscalar : Q ≤ 9 * Real.sqrt (normSq0S g p 4 (metricRm04At g p)) := by
    have hh := (le_abs_self (metricScalarAt g p)).trans (scalar_abs_le_rm g p)
    change Q ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * _ at hh
    norm_num [ThreeSpace] at hh
    exact hh
  have hρ3 : ρ ≤ 3 := sqrt_mul_radius_le_three_of_curvature_bound nk.Q_pos.le
    (normSq0S_nonneg _ _ _ _) hscalar htest
  have hmargin : (3 : ℝ) < eps⁻¹ := by
    apply (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
    linarith [nk.eps_small]
  have hnormalized : ENNReal.ofReal ((ν / 27) * ρ ^ 3) ≤
      riemannianVolumeMeasure I3 M gn (riemannianBallOf gn p ρ) := by
    by_cases hρ1 : ρ ≤ 1
    · have h0 := hvol nk (nk.center, 0) ρ hρ hρ1 (by simp only [abs_zero, zero_add]; exact hρ3.trans_lt hmargin)
      rw [nk.center_eq] at h0
      exact (ENNReal.ofReal_le_ofReal (by nlinarith [pow_pos hρ 3])).trans h0
    · have h0 := hvol nk (nk.center, 0) 1 (by norm_num) le_rfl (by
        simp only [abs_zero, zero_add]
        linarith)
      rw [nk.center_eq] at h0
      have hpow : ρ ^ 3 ≤ 27 := by
        have hh := pow_le_pow_left₀ hρ.le hρ3 3
        norm_num at hh
        exact hh
      calc
        ENNReal.ofReal ((ν / 27) * ρ ^ 3) ≤ ENNReal.ofReal ν :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
        _ ≤ riemannianVolumeMeasure I3 M gn (riemannianBallOf gn p 1) := by simpa only [one_pow, mul_one] using h0
        _ ≤ _ := measure_mono (riemannianBallOf_mono gn p (lt_of_not_ge hρ1).le)
  have hball : riemannianBallOf gn p ρ = riemannianBallOf g p r :=
    riemannianBallOf_scaleMetric Q nk.Q_pos g p r
  rw [hball, volume_scale_apply] at hnormalized
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hnormalized
  have hcoef : ENNReal.ofReal ((ν / 27) * ρ ^ 3) =
      ENNReal.ofReal (Real.sqrt Q) ^ 3 * ENNReal.ofReal ((ν / 27) * r ^ 3) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg Q),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg Q) _)]
    congr 1
    dsimp only [ρ]
    ring
  rw [hcoef] at hnormalized
  exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero 3 (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr nk.Q_pos)).ne')
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp hnormalized

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
