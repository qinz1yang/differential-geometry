import DifferentialGeometry.Analysis.Convex.Closure
import DifferentialGeometry.Geometry.Geodesic.EquationGerm
import DifferentialGeometry.Geometry.Geodesic.Minimizing.MetricSegmentRegularity
import DifferentialGeometry.Geometry.Comparison.Toponogov.LimitingRadialAngle
import DifferentialGeometry.Geometry.Metric.Distance.Completion
import DifferentialGeometry.Geometry.Comparison.Toponogov.SquaredDistanceDefectConvexity
import DifferentialGeometry.Geometry.Curve.Reparametrization

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Toponogov
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem smooth_geodesic_rescale
    (g : SmoothRiemannianMetric I M) (gamma : ℝ → M)
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hgeo : IsGeodesicOn g gamma (Icc (0 : ℝ) 1))
    {L : ℝ} (hL : 0 < L)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) = L ^ 2) :
    let eta : ℝ → M := fun t => gamma (L⁻¹ * t + 0)
    ContMDiff 𝓘(ℝ, ℝ) I ∞ eta ∧ IsGeodesicOn g eta (Icc 0 L) ∧
      ∀ t ∈ Icc 0 L, g.inner (eta t) (mfderiv 𝓘(ℝ, ℝ) I eta t 1)
        (mfderiv 𝓘(ℝ, ℝ) I eta t 1) = 1 := by
  have harg {t : ℝ} (ht : t ∈ Icc 0 L) : L⁻¹ * t + 0 ∈ Icc (0 : ℝ) 1 := by
    rw [add_zero, inv_mul_eq_div]
    exact ⟨div_nonneg ht.1 hL.le, (div_le_one hL).mpr ht.2⟩
  refine ⟨hsmooth.comp ((contDiff_const.mul contDiff_id).add contDiff_const).contMDiff,
    fun t ht => isGeodesicOn_comp_affine (c := L⁻¹) (d := 0) hgeo t (harg ht), ?_⟩
  intro t ht
  have hd := mfderiv_comp_affine_apply_one t L⁻¹ 0
    (hsmooth.mdifferentiable (by decide)).mdifferentiableAt
  have hd' : mfderiv 𝓘(ℝ, ℝ) I (fun u => gamma (L⁻¹ * u + 0)) t 1 =
      L⁻¹ • mfderiv 𝓘(ℝ, ℝ) I gamma (L⁻¹ * t + 0) 1 := hd
  change g.inner (gamma (L⁻¹ * t + 0))
    (mfderiv 𝓘(ℝ, ℝ) I (fun u => gamma (L⁻¹ * u + 0)) t 1)
    (mfderiv 𝓘(ℝ, ℝ) I (fun u => gamma (L⁻¹ * u + 0)) t 1) = 1
  rw [hd', gInner_smul_self, hspeed _ (harg ht), ← mul_pow, inv_mul_cancel₀ hL.ne', one_pow]

private theorem unitSpeedGeodesicOn_Ioo_of_smooth_geodesic [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {beta : ℝ → M} {L : ℝ}
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ beta)
    (hgeo : IsGeodesicOn g beta (Icc 0 L))
    (hunit : ∀ t ∈ Icc 0 L, g.inner (beta t) (mfderiv 𝓘(ℝ, ℝ) I beta t 1)
      (mfderiv 𝓘(ℝ, ℝ) I beta t 1) = 1) :
    UnitSpeedGeodesicOn g beta (Ioo 0 L) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine ⟨hsmooth.continuous.continuousOn, hsmooth.contMDiffOn, ?_,
    fun t ht => hunit t ⟨ht.1.le, ht.2.le⟩⟩
  intro t ht
  have h := isGeodesicAt_of_isGeodesicOn g (Icc_mem_nhds ht.1 ht.2) hgeo
    hsmooth.continuous.continuousOn
  simpa only [sub_self, add_comm] using isGeodesicAt_comp_add h t

private theorem nonempty_connector_of_constant_speed_geodesic
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {p q : M} (gamma : ℝ → M) (hstart : gamma 0 = p) (hend : gamma 1 = q)
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hgeo : IsGeodesicOn g gamma (Icc (0 : ℝ) 1))
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) = dist p q ^ 2) :
    Nonempty (RealizedMinimizingConnector g p q) := by
  by_cases heq : p = q
  · rcases heq with rfl
    refine ⟨⟨fun _ => p, 0, le_rfl, rfl, rfl, contMDiffOn_const,
      (isGeodesic_const g p).isGeodesicOn _, ?_, ?_⟩⟩
    · intro t ht
      exact False.elim (lt_asymm ht.1 ht.2)
    · rw [riemannianEDistOf_self, ENNReal.ofReal_zero]
  let L := dist p q
  have hL : 0 < L := dist_pos.mpr heq
  let eta (t : ℝ) := gamma (L⁻¹ * t + 0)
  obtain ⟨heta, hge, hue⟩ := smooth_geodesic_rescale g gamma hsmooth hgeo hL hspeed
  refine ⟨⟨eta, L, hL.le, ?_, ?_, (heta.of_le (by decide)).contMDiffOn,
    hge, fun t ht => hue t ⟨ht.1.le, ht.2.le⟩, ?_⟩⟩
  · simpa only [eta, mul_zero, add_zero] using hstart
  · simpa only [eta, inv_mul_cancel₀ hL.ne', add_zero] using hend
  · exact (hmetric p q).symm.trans (edist_dist p q)

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]

theorem nonempty_realizedMinimizingConnector_of_completion_point_avoidance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {z : UniformSpace.Completion M} (hz : z ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ z)
    {p q : M} (hp : dist (p : UniformSpace.Completion M) z < r / 3)
    (hq : dist (q : UniformSpace.Completion M) z < r / 3) :
    Nonempty (RealizedMinimizingConnector g p q) := by
  obtain ⟨gamma, hstart, hend, hsmooth, _, _, _, hgeo, hspeed⟩ :=
    exists_smooth_geodesic_minimizer_of_completion_point_avoidance
      g hmetric hz hcompact hcover havoid hp hq
  exact nonempty_connector_of_constant_speed_geodesic g hmetric gamma hstart hend hsmooth hgeo hspeed

theorem convexOn_squared_distance_defect_of_completion_point_avoidance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {z : UniformSpace.Completion M} (hz : z ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ z)
    {p : M} (hp : dist (p : UniformSpace.Completion M) z < r / 3)
    {beta : ℝ → M} {J : Set ℝ} (hJ : Convex ℝ J)
    (hbeta : UnitSpeedGeodesicOn g beta J)
    (hsmall : ∀ t ∈ J, dist (beta t : UniformSpace.Completion M) z < r / 3) :
    ConvexOn ℝ J (fun t => t ^ 2 - dist p (beta t) ^ 2) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hconnectors : RealizedConnectors g p beta J := fun t ht =>
    nonempty_realizedMinimizingConnector_of_completion_point_avoidance
      g hmetric hz hcompact hcover havoid hp (hsmall t ht)
  have hdist (x y : M) : riemannianDistance g x y = dist x y := by
    unfold riemannianDistance
    rw [← hmetric, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
  have h := squaredDistanceDefect_convexOn_of_realizedConnectors g hsec p beta J hJ hbeta hconnectors
  change ConvexOn ℝ J (fun t => t ^ 2 - riemannianDistance g p (beta t) ^ 2) at h
  simpa only [hdist] using h

theorem convexOn_squared_distance_defect_at_missing_completion_point
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {z : UniformSpace.Completion M} (hz : z ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hr : 0 < r) (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ z)
    {beta : ℝ → M} {J : Set ℝ} (hJ : Convex ℝ J)
    (hbeta : UnitSpeedGeodesicOn g beta J)
    (hsmall : ∀ t ∈ J, dist (beta t : UniformSpace.Completion M) z < r / 3) :
    ConvexOn ℝ J (fun t => t ^ 2 - dist z (beta t : UniformSpace.Completion M) ^ 2) := by
  let l : Filter M := comap (fun p : M => (p : UniformSpace.Completion M)) (𝓝 z)
  let _ : l.NeBot := UniformSpace.Completion.isDenseInducing_coe.comap_nhds_neBot z
  have hpT : Tendsto (fun p : M => (p : UniformSpace.Completion M)) l (𝓝 z) := tendsto_comap
  have hnear : ∀ᶠ p : M in l, dist (p : UniformSpace.Completion M) z < r / 3 := by
    have h := (hpT.dist (tendsto_const_nhds (x := z))).eventually
      (gt_mem_nhds (show dist z z < r / 3 by rw [dist_self]; positivity))
    exact h
  have hF (t : ℝ) : Tendsto (fun p : M => t ^ 2 - dist p (beta t) ^ 2) l
      (𝓝 (t ^ 2 - dist z (beta t : UniformSpace.Completion M) ^ 2)) := by
    have hd := hpT.dist (tendsto_const_nhds (x := (beta t : UniformSpace.Completion M)))
    simpa only [UniformSpace.Completion.dist_eq] using tendsto_const_nhds.sub (hd.pow 2)
  refine ⟨hJ, ?_⟩
  intro s hs t ht a b ha hb hab
  simp only [smul_eq_mul]
  apply le_of_tendsto_of_tendsto (hF (a * s + b * t))
    (((hF s).const_mul a).add ((hF t).const_mul b))
  filter_upwards [hnear] with p hp
  have hconv := convexOn_squared_distance_defect_of_completion_point_avoidance
    g hmetric hsec hz hcompact hcover havoid hp hJ hbeta hsmall
  exact hconv.2 hs ht ha hb hab

theorem dist_sq_ge_interpolation_at_missing_completion_point
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {z : UniformSpace.Completion M} (hz : z ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hr : 0 < r) (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ z)
    {beta : ℝ → M} {L : ℝ} (hL : 0 ≤ L)
    (hbeta : UnitSpeedGeodesicOn g beta (Icc 0 L))
    (hsmall : ∀ t ∈ Icc 0 L, dist (beta t : UniformSpace.Completion M) z < r / 3)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (1 - u) * dist z (beta 0 : UniformSpace.Completion M) ^ 2 +
      u * dist z (beta L : UniformSpace.Completion M) ^ 2 - u * (1 - u) * L ^ 2 ≤
        dist z (beta (u * L) : UniformSpace.Completion M) ^ 2 := by
  have hconv := convexOn_squared_distance_defect_at_missing_completion_point
    g hmetric hsec hz hr hcompact hcover havoid (convex_Icc 0 L) hbeta hsmall
  have h := hconv.2 (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL⟩)
    (show L ∈ Icc 0 L from ⟨hL, le_rfl⟩)
    (sub_nonneg.mpr hu.2) hu.1 (show 1 - u + u = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  nlinarith only [h]

theorem exists_minimizing_geodesic_with_completion_comparison
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {z : UniformSpace.Completion M} (hz : z ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ z)
    {p q : M} (hpq : p ≠ q)
    (hp : dist (p : UniformSpace.Completion M) z < r / 10)
    (hq : dist (q : UniformSpace.Completion M) z < r / 10) :
    ∃ beta : ℝ → M, beta 0 = p ∧ beta (dist p q) = q ∧
      ContMDiff 𝓘(ℝ, ℝ) I ∞ beta ∧
      UnitSpeedGeodesicOn g beta (Ioo 0 (dist p q)) ∧
      (∀ s ∈ Icc 0 (dist p q), ∀ t ∈ Icc 0 (dist p q), dist (beta s) (beta t) = |s - t|) ∧
      (∀ t ∈ Icc 0 (dist p q), dist (beta t : UniformSpace.Completion M) z < r / 3) ∧
      ConvexOn ℝ (Icc 0 (dist p q))
        (fun t => t ^ 2 - dist z (beta t : UniformSpace.Completion M) ^ 2) := by
  have hr : 0 < r := by linarith only [hp, dist_nonneg (x := (p : UniformSpace.Completion M)) (y := z)]
  obtain ⟨gamma, hstart, hend, hsmooth, _, _, hsub, hgeo, hspeed⟩ :=
    exists_smooth_geodesic_minimizer_of_completion_point_avoidance g hmetric hz hcompact hcover havoid (p := p) (q := q)
      (by linarith only [hp, hr]) (by linarith only [hq, hr])
  let L := dist p q
  have hL : 0 < L := dist_pos.mpr hpq
  let Lnn : ℝ≥0 := ⟨L, hL.le⟩
  have hLip : LipschitzOnWith Lnn gamma (Icc (0 : ℝ) 1) :=
    lipschitzOnWith_of_subinterval_lengths g hmetric
      (hsmooth.of_le (by decide)).contMDiffOn dist_nonneg le_rfl hsub
  have hfLip : LipschitzWith Lnn (fun t : Icc (0 : ℝ) 1 => gamma t) :=
    LipschitzWith.of_dist_le_mul (fun t u => hLip.dist_le_mul t t.property u u.property)
  have hnorm := Metric.dist_eq_mul_of_lipschitz_interval
    (fun t : Icc (0 : ℝ) 1 => gamma t) hfLip
    (show dist (gamma 0) (gamma 1) = Lnn by rw [hstart, hend]; rfl)
  have hsmallGamma (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (gamma t : UniformSpace.Completion M) z < r / 3 := by
    have hb := hLip.dist_le_mul t ht 0 (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    rw [hstart, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] at hb
    change dist (gamma t) p ≤ L * t at hb
    have hb' := hb.trans (mul_le_of_le_one_right hL.le ht.2)
    have htri := dist_triangle (gamma t : UniformSpace.Completion M) (p : UniformSpace.Completion M) z
    rw [UniformSpace.Completion.dist_eq] at htri
    have hpqBound := dist_triangle (p : UniformSpace.Completion M) z (q : UniformSpace.Completion M)
    rw [UniformSpace.Completion.dist_eq, dist_comm z] at hpqBound
    change L ≤ dist (p : UniformSpace.Completion M) z + dist (q : UniformSpace.Completion M) z at hpqBound
    linarith only [htri, hb', hpqBound, hp, hq, hr]
  let beta (t : ℝ) := gamma (L⁻¹ * t + 0)
  obtain ⟨hsmoothBeta, hgeoBeta, hunitBeta⟩ := smooth_geodesic_rescale g gamma hsmooth hgeo hL hspeed
  have harg {t : ℝ} (ht : t ∈ Icc 0 L) : L⁻¹ * t + 0 ∈ Icc (0 : ℝ) 1 := by
    rw [add_zero, inv_mul_eq_div]
    exact ⟨div_nonneg ht.1 hL.le, (div_le_one hL).mpr ht.2⟩
  have hsmallBeta (t : ℝ) (ht : t ∈ Icc 0 L) :
      dist (beta t : UniformSpace.Completion M) z < r / 3 := hsmallGamma _ (harg ht)
  have hunit : UnitSpeedGeodesicOn g beta (Ioo 0 L) :=
    unitSpeedGeodesicOn_Ioo_of_smooth_geodesic g hsmoothBeta hgeoBeta hunitBeta
  have hconv := convexOn_squared_distance_defect_at_missing_completion_point
    g hmetric hsec hz hr hcompact hcover havoid (convex_Ioo 0 L) hunit
    (fun t ht => hsmallBeta t ⟨ht.1.le, ht.2.le⟩)
  have hcont : Continuous (fun t => t ^ 2 - dist z (beta t : UniformSpace.Completion M) ^ 2) :=
    (continuous_id.pow 2).sub ((continuous_const.dist
      ((UniformSpace.Completion.continuous_coe M).comp hsmoothBeta.continuous)).pow 2)
  have hclosed := hconv.closure_of_continuousOn hcont.continuousOn
  rw [closure_Ioo hL.ne] at hclosed
  refine ⟨beta, ?_, ?_, hsmoothBeta, hunit, ?_, hsmallBeta, hclosed⟩
  · simpa only [beta, mul_zero, add_zero] using hstart
  · change gamma (L⁻¹ * L + 0) = q
    simpa only [inv_mul_cancel₀ hL.ne', add_zero] using hend
  · intro t ht u hu
    have hd := hnorm ⟨L⁻¹ * t + 0, harg ht⟩ ⟨L⁻¹ * u + 0, harg hu⟩
    change dist (beta t) (beta u) = L * |(L⁻¹ * t + 0) - (L⁻¹ * u + 0)| at hd
    rw [add_zero, add_zero, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hL),
      ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul] at hd
    exact hd

private theorem unitSpeedGeodesicOn_of_dist_eq
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    {beta : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hdist : ∀ s ∈ J, ∀ t ∈ J, dist (beta s) (beta t) = |s - t|) :
    UnitSpeedGeodesicOn g beta J := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hpoint (t : ℝ) (ht : t ∈ J) :
      ContMDiffAt 𝓘(ℝ, ℝ) I ∞ beta t ∧ HasGeodesicEquationAt g beta t ∧
      g.inner (beta t) (mfderiv 𝓘(ℝ, ℝ) I beta t 1) (mfderiv 𝓘(ℝ, ℝ) I beta t 1) = 1 := by
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds ht)
    have hmem (s : ℝ) (hs : s ∈ Icc (-(r / 2)) (r / 2)) : t + s ∈ J := by
      apply hball
      change |t + s - t| < r
      rw [add_sub_cancel_left]
      exact (abs_le.mpr hs).trans_lt (half_lt_self hr)
    apply contMDiffAt_and_geodesicEquationAt_of_metric_segment g hmetric beta t (half_pos hr)
    intro s hs v hv
    rw [hdist _ (hmem s hs) _ (hmem v hv)]
    congr 1
    ring
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ beta J :=
    fun t ht => (hpoint t ht).1.contMDiffWithinAt
  have hgeo : IsGeodesicOn g beta J := fun t ht => (hpoint t ht).2.1
  refine ⟨hsmooth.continuousOn, hsmooth.mono interior_subset, ?_, fun t ht => (hpoint t ht).2.2⟩
  intro t ht
  have h := isGeodesicAt_of_isGeodesicOn g (hJ.mem_nhds ht) hgeo hsmooth.continuousOn
  simpa only [sub_self, add_comm] using isGeodesicAt_comp_add h t

private theorem convexOn_squared_distance_defect_along_completion_segment_regular_center
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {z : UniformSpace.Completion M} (hz : z ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ z)
    {p : M} (hp : dist (p : UniformSpace.Completion M) z < r / 3)
    {gamma : ℝ → UniformSpace.Completion M} {L : ℝ} (hL : 0 < L) (hLr : L < r / 3)
    (hzero : gamma 0 = z)
    (hdist : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, dist (gamma s) (gamma t) = |s - t|) :
    ConvexOn ℝ (Icc 0 L) (fun t => t ^ 2 - dist (p : UniformSpace.Completion M) (gamma t) ^ 2) := by
  classical
  have hrad (t : ℝ) (ht : t ∈ Icc 0 L) : dist (gamma t) z = t := by
    simpa only [hzero, sub_zero, abs_of_nonneg ht.1] using hdist t ht 0 ⟨le_rfl, hL.le⟩
  have hregular (t : ℝ) (ht : t ∈ Ioc 0 L) : ∃ x : M, (x : UniformSpace.Completion M) = gamma t := by
    have hball : gamma t ∈ Metric.closedBall z r := by
      change dist (gamma t) z ≤ r
      rw [hrad t ⟨ht.1.le, ht.2⟩]
      linarith only [ht.2, hLr, hL]
    rcases hcover hball with heq | hreg
    · have h := hrad t ⟨ht.1.le, ht.2⟩
      rw [heq, dist_self] at h
      exact False.elim (ht.1.ne' h.symm)
    · exact hreg
  let beta (t : ℝ) : M := if ht : t ∈ Ioc 0 L then (hregular t ht).choose else p
  have hbeta (t : ℝ) (ht : t ∈ Ioc 0 L) : (beta t : UniformSpace.Completion M) = gamma t := by
    dsimp only [beta]
    rw [dite_eq_left ht]
    exact (hregular t ht).choose_spec
  have hunit : UnitSpeedGeodesicOn g beta (Ioo 0 L) := by
    apply unitSpeedGeodesicOn_of_dist_eq g hmetric isOpen_Ioo
    intro s hs t ht
    rw [← UniformSpace.Completion.dist_eq, hbeta s ⟨hs.1, hs.2.le⟩, hbeta t ⟨ht.1, ht.2.le⟩]
    exact hdist s ⟨hs.1.le, hs.2.le⟩ t ⟨ht.1.le, ht.2.le⟩
  have hsmall (t : ℝ) (ht : t ∈ Ioo 0 L) : dist (beta t : UniformSpace.Completion M) z < r / 3 := by
    rw [hbeta t ⟨ht.1, ht.2.le⟩, hrad t ⟨ht.1.le, ht.2.le⟩]
    exact ht.2.trans hLr
  have hconv := convexOn_squared_distance_defect_of_completion_point_avoidance
    g hmetric hsec hz hcompact hcover havoid hp (convex_Ioo 0 L) hunit hsmall
  have hconv' : ConvexOn ℝ (Ioo 0 L)
      (fun t => t ^ 2 - dist (p : UniformSpace.Completion M) (gamma t) ^ 2) := by
    apply hconv.congr
    intro t ht
    dsimp only
    rw [← hbeta t ⟨ht.1, ht.2.le⟩, UniformSpace.Completion.dist_eq]
  have hLip : LipschitzOnWith 1 gamma (Icc 0 L) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [hdist s hs t ht, Real.dist_eq, NNReal.coe_one, one_mul]
  have hcont : ContinuousOn (fun t => t ^ 2 - dist (p : UniformSpace.Completion M) (gamma t) ^ 2)
      (closure (Ioo 0 L)) := by
    rw [closure_Ioo hL.ne]
    have hd : ContinuousOn (fun t => dist (p : UniformSpace.Completion M) (gamma t)) (Icc 0 L) :=
      fun t ht => tendsto_const_nhds.dist (hLip.continuousOn t ht)
    exact (continuousOn_id.pow 2).sub (hd.pow 2)
  simpa only [closure_Ioo hL.ne] using hconv'.closure_of_continuousOn hcont

theorem convexOn_squared_distance_defect_along_completion_segment
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {z : UniformSpace.Completion M} (hz : z ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ z)
    {p : UniformSpace.Completion M} (hp : dist p z < r / 3)
    {gamma : ℝ → UniformSpace.Completion M} {L : ℝ} (hL : 0 < L) (hLr : L < r / 3)
    (hzero : gamma 0 = z)
    (hdist : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, dist (gamma s) (gamma t) = |s - t|) :
    ConvexOn ℝ (Icc 0 L) (fun t => t ^ 2 - dist p (gamma t) ^ 2) := by
  by_cases hpz : p = z
  · subst p
    apply (convexOn_const (0 : ℝ) (convex_Icc 0 L)).congr
    intro t ht
    have hd := hdist 0 ⟨le_rfl, hL.le⟩ t ht
    rw [hzero, zero_sub, abs_neg, abs_of_nonneg ht.1] at hd
    dsimp only
    rw [hd, sub_self]
  · have hpball : p ∈ Metric.closedBall z r := by
      change dist p z ≤ r
      linarith only [hp, hLr, hL]
    rcases hcover hpball with heq | ⟨q, hq⟩
    · exact False.elim (hpz heq)
    · subst p
      exact convexOn_squared_distance_defect_along_completion_segment_regular_center
        g hmetric hsec hz hcompact hcover havoid hp hL hLr hzero hdist

private theorem comparisonAngle_shorten_first_of_completion_segment
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {z : UniformSpace.Completion M} (hz : z ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ z)
    {p : UniformSpace.Completion M} {b : ℝ} (hb : 0 < b) (hbr : b < r / 3) (hp : dist p z = b)
    {gamma : ℝ → UniformSpace.Completion M} {L : ℝ} (hL : 0 < L) (hLr : L < r / 3)
    (hzero : gamma 0 = z)
    (hdist : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, dist (gamma s) (gamma t) = |s - t|)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₁₂ : a₁ ≤ a₂) (ha₂ : a₂ ≤ L) :
    comparisonAngle a₂ b (dist (gamma a₂) p) ≤ comparisonAngle a₁ b (dist (gamma a₁) p) := by
  let F : ℝ → ℝ := fun s => s ^ 2 + b ^ 2 - dist (gamma s) p ^ 2
  have hbase := convexOn_squared_distance_defect_along_completion_segment g hmetric hsec
    hz hcompact hcover havoid (hp.trans_lt hbr) hL hLr hzero hdist
  have hF : ConvexOn ℝ (Icc 0 L) F := by
    convert! hbase.add_const (b ^ 2) using 1
    funext s
    dsimp only [F, Pi.add_apply]
    rw [dist_comm p]
    ring
  have hzeroF : F 0 = 0 := by
    dsimp only [F]
    rw [hzero, dist_comm z, hp]
    ring
  have hratio := Geometry.Comparison.Toponogov.convex_quotient_mono hF hzeroF ha₁ ha₁₂ ha₂
  have hdiv := div_le_div_of_nonneg_right hratio (by positivity : 0 ≤ 2 * b)
  dsimp only [comparisonAngle]
  apply Real.arccos_le_arccos
  convert! hdiv using 1 <;> dsimp only [F, comparisonCosine] <;> ring

theorem radialComparisonAngle_nonincreasing_of_completion_segments
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (hsec : HasNonnegativeSectionalCurvature g)
    {z : UniformSpace.Completion M} (hz : z ∉ range (fun x : M => (x : UniformSpace.Completion M)))
    {r : ℝ} (hcompact : IsCompact (Metric.closedBall z r))
    (hcover : Metric.closedBall z r ⊆ insert z (range (fun x : M => (x : UniformSpace.Completion M))))
    (havoid : ∀ (beta : ℝ → UniformSpace.Completion M) (u v w : ℝ), u < v → v < w →
      (∀ s ∈ Icc u w, ∀ t ∈ Icc u w, dist (beta s) (beta t) = |s - t|) → beta v ≠ z)
    {ι : Type*} {L : ι → ℝ} {gamma : ι → ℝ → UniformSpace.Completion M}
    (hL : ∀ i, 0 < L i) (hLr : ∀ i, L i < r / 3) (hzero : ∀ i, gamma i 0 = z)
    (hdist : ∀ i, ∀ s ∈ Icc 0 (L i), ∀ t ∈ Icc 0 (L i), dist (gamma i s) (gamma i t) = |s - t|)
    (i j : ι) :
    CoordinatewiseNonincreasingOn (L i) (L j) (radialComparisonAngle gamma i j) := by
  have hrad (k : ι) (t : ℝ) (ht : t ∈ Ioc 0 (L k)) : dist (gamma k t) z = t := by
    simpa only [hzero k, sub_zero, abs_of_pos ht.1] using
      hdist k t ⟨ht.1.le, ht.2⟩ 0 ⟨le_rfl, (hL k).le⟩
  constructor
  · intro s₁ s₂ t hs₁ hs₂ ht hs
    exact comparisonAngle_shorten_first_of_completion_segment g hmetric hsec hz hcompact hcover havoid
      ht.1 (ht.2.trans_lt (hLr j)) (hrad j t ht) (hL i) (hLr i) (hzero i) (hdist i) hs₁.1 hs hs₂.2
  · intro s t₁ t₂ hs ht₁ ht₂ ht
    have h := comparisonAngle_shorten_first_of_completion_segment g hmetric hsec hz hcompact hcover havoid
      hs.1 (hs.2.trans_lt (hLr i)) (hrad i s hs) (hL j) (hLr j) (hzero j) (hdist j) ht₁.1 ht ht₂.2
    simpa only [radialComparisonAngle, comparisonAngle_comm, dist_comm] using h


end DifferentialGeometry.Toponogov
