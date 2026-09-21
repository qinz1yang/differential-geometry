import DifferentialGeometry.Analysis.Convex.Closure
import DifferentialGeometry.Geometry.Geodesic.EquationGerm
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

end DifferentialGeometry.Toponogov
