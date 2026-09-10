import DifferentialGeometry.Geometry.Comparison.Soul.SbrFlowCalibration
import DifferentialGeometry.Geometry.Comparison.Soul.SbrMetricVelocity
import DifferentialGeometry.Geometry.Comparison.Soul.SbrRightTangent

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
theorem hasMFDerivWithinAt_of_normalChart_right_limit
    (g : SmoothRiemannianMetric I M) (eta : ℝ → M)
    (V : TangentSpace I (eta 0))
    (heta : ContinuousWithinAt eta (Ici 0) 0)
    (hlimit : Tendsto (fun h : ℝ => h⁻¹ •
      NormalCoordinates.normalChartAt (I := I) g (eta 0) (eta h))
      (𝓝[>] (0 : ℝ)) (𝓝 (V : E))) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (Ici 0) 0
      (ContinuousLinearMap.toSpanSingleton ℝ V) := by
  let chart := NormalCoordinates.normalChartAt (I := I) g (eta 0)
  let xi : ℝ → E := fun h => chart (eta h)
  have hxi0 : xi 0 = 0 := NormalCoordinates.normalChartAt_centre g (eta 0)
  have hxider : HasDerivWithinAt xi (V : E) (Ioi 0) 0 := by
    apply (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mpr
    change Tendsto (fun h => slope xi 0 h) (𝓝[>] (0 : ℝ)) (𝓝 (V : E))
    simpa only [slope_def_module, hxi0, sub_zero] using hlimit
  have hzero : (0 : E) ∈ chart.target :=
    NormalCoordinates.zero_mem_normalChartAt_target g (eta 0)
  have he : HasMFDerivAt 𝓘(ℝ, E) I chart.symm (0 : E)
      (ContinuousLinearMap.id ℝ E) := by
    have hd := ((chart.contMDiffOn_invFun.mdifferentiableOn one_ne_zero)
      0 hzero).mdifferentiableAt (chart.open_target.mem_nhds hzero)
    apply hd.hasMFDerivAt.congr_mfderiv
    exact NormalCoordinates.mfderiv_normalChartAt_symm_zero g (eta 0)
  have he' : HasMFDerivAt 𝓘(ℝ, E) I chart.symm (xi 0)
      (ContinuousLinearMap.id ℝ E) := by rw [hxi0]; exact he
  have hxiMF : HasMFDerivWithinAt (M := ℝ) (M' := E) 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      xi (Ici 0) 0 (ContinuousLinearMap.toSpanSingleton ℝ (V : E)) :=
    (hxider.Ici_of_Ioi.hasFDerivWithinAt (F := E)).hasMFDerivWithinAt (E := ℝ) (E' := E)
  have hcomp := he'.comp_hasMFDerivWithinAt 0 hxiMF
  have hcomp' : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun h => chart.symm (xi h)) (Ici 0) 0
      (ContinuousLinearMap.toSpanSingleton ℝ V) := by
    convert! hcomp using 1
  have hsource : eta 0 ∈ chart.source :=
    NormalCoordinates.normalChartAt_source g (eta 0)
  have hmem : ∀ᶠ h in 𝓝[≥] (0 : ℝ), eta h ∈ chart.source :=
    heta.tendsto.eventually (chart.open_source.mem_nhds hsource)
  apply hcomp'.congr_of_eventuallyEq
  · exact hmem.mono fun h hh => (chart.left_inv hh).symm
  · exact (chart.left_inv hsource).symm

set_option backward.isDefEq.respectTransparency false in
theorem eventually_dist_div_le_of_right_velocity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (eta : ℝ → M) (V : TangentSpace I (eta 0))
    (hvelocity : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (Ici 0) 0
      (ContinuousLinearMap.toSpanSingleton ℝ V)) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ h in 𝓝[>] (0 : ℝ),
      dist (eta 0) (eta h) / h ≤ Real.sqrt (g.inner (eta 0) V V) + epsilon := by
  let beta := intrinsicGeodesic g hEnorm (eta 0) V
  have hbeta : MDifferentiableAt 𝓘(ℝ, ℝ) I beta (0 : ℝ) :=
    (intrinsicGeodesic_contMDiff g hEnorm (eta 0) V).contMDiffAt
      |>.mdifferentiableAt (by simp)
  have hagree : Tendsto (fun h => dist (eta h) (beta h) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_dist_div_sub_of_same_right_velocity hvelocity
      hbeta.hasMFDerivAt.hasMFDerivWithinAt (by simp [beta]) (by
        change (1 : ℝ) • (V : E) = (mfderiv 𝓘(ℝ, ℝ) I beta 0 1 : E)
        rw [one_smul]
        exact (intrinsicGeodesic_mfderiv_zero g hEnorm (eta 0) V).symm)
    simpa only [sub_zero] using h
  have hgeod (h : ℝ) (hh : 0 < h) :
      dist (eta 0) (beta h) / h ≤ Real.sqrt (g.inner (eta 0) V V) := by
    have hd := intrinsicGeodesic_riemannianEDist_le g hEnorm (eta 0) V hh.le
    rw [← IsRiemannianManifold.out (I := I), edist_dist] at hd
    have hd' := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hh.le))).mp hd
    apply (div_le_iff₀ hh).mpr
    simpa only [beta, intrinsicGeodesic_zero, sub_zero] using hd'
  intro epsilon hepsilon
  filter_upwards [hagree.eventually (gt_mem_nhds hepsilon), self_mem_nhdsWithin]
    with h herror hh
  change 0 < h at hh
  calc
    dist (eta 0) (eta h) / h ≤
        (dist (eta 0) (beta h) + dist (beta h) (eta h)) / h :=
      div_le_div_of_nonneg_right (dist_triangle _ _ _) hh.le
    _ = dist (eta 0) (beta h) / h + dist (eta h) (beta h) / h := by
      rw [add_div, dist_comm (beta h)]
    _ ≤ Real.sqrt (g.inner (eta 0) V V) + dist (eta h) (beta h) / h :=
      add_le_add (hgeod h hh) le_rfl
    _ ≤ Real.sqrt (g.inner (eta 0) V V) + epsilon :=
      add_le_add le_rfl herror.le

variable [T2Space (TangentBundle I M)]

set_option backward.isDefEq.respectTransparency false in
theorem exists_normalized_ascent_minimizing_exp_secants
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (eta : ℝ → M) {T : ℝ} (hT : 0 < T)
    (heta : ContinuousOn eta (Icc 0 T))
    (hvelocity : ∀ t ∈ Ico 0 T,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta t)
      G ≠ 0 ∧ HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (eta t) G G)⁻¹ • G))) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta 0)
    ∃ xi : ℝ → TangentSpace I (eta 0), xi 0 = 0 ∧
      (∀ h : ℝ, expMapIntrinsic g hEnorm (eta 0) (xi h) = eta h ∧
        Real.sqrt (g.inner (eta 0) (xi h) (xi h)) = dist (eta 0) (eta h)) ∧
      Tendsto (fun h => h⁻¹ • xi h) (𝓝[>] (0 : ℝ))
        (𝓝 ((g.inner (eta 0) G G)⁻¹ • G)) := by
  let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta 0)
  obtain ⟨hG, hder⟩ := hvelocity 0 ⟨le_rfl, hT⟩
  have hspec := intrinsicGeneralizedGradient_spec g hEnorm hF hconc (eta 0)
  have hcal := normalized_ascent_level_increment g hEnorm hF hconc eta heta hvelocity
  have hlevel : ∀ᶠ h in 𝓝[>] (0 : ℝ), F (eta h) = F (eta 0) + h := by
    filter_upwards [Ioo_mem_nhdsGT hT] with h hh
    simpa only [sub_zero] using hcal h ⟨hh.1.le, hh.2.le⟩
  have hnorm : 0 < g.inner (eta 0) G G := g.pos (eta 0) G hG
  have hlength : Real.sqrt (g.inner (eta 0)
      ((g.inner (eta 0) G G)⁻¹ • G) ((g.inner (eta 0) G G)⁻¹ • G)) =
        (Real.sqrt (g.inner (eta 0) G G))⁻¹ := by
    rw [sqrt_gInner_smul_self g (eta 0) (inv_nonneg.mpr hnorm.le)]
    have hsquare := Real.sq_sqrt hnorm.le
    have hroot : 0 < Real.sqrt (g.inner (eta 0) G G) := Real.sqrt_pos.mpr hnorm
    field_simp [hnorm.ne', hroot.ne']
    nlinarith [hsquare]
  have hspeed := eventually_dist_div_le_of_right_velocity g hEnorm eta
    ((g.inner (eta 0) G G)⁻¹ • G) hder
  rw [hlength] at hspeed
  exact exists_minimizing_exp_velocity_of_metric_speed g hEnorm F hconc eta G
    hspec.1 hspec.2 hG hlevel hspeed

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_normalChart_normalized_ascent
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (eta : ℝ → M) {T : ℝ} (hT : 0 < T)
    (heta : ContinuousOn eta (Icc 0 T))
    (hvelocity : ∀ t ∈ Ico 0 T,
      let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta t)
      G ≠ 0 ∧ HasMFDerivWithinAt 𝓘(ℝ, ℝ) I eta (Ici t) t
        (ContinuousLinearMap.toSpanSingleton ℝ ((g.inner (eta t) G G)⁻¹ • G))) :
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta 0)
    Tendsto (fun h : ℝ => h⁻¹ •
      NormalCoordinates.normalChartAt (I := I) g (eta 0) (eta h))
      (𝓝[>] (0 : ℝ)) (𝓝 (((g.inner (eta 0) G G)⁻¹ • G : TangentSpace I (eta 0)) : E)) := by
  obtain ⟨xi, _hxi0, hxi, hlim⟩ :=
    exists_normalized_ascent_minimizing_exp_secants g hEnorm hF hconc eta hT heta hvelocity
  have hcont : Tendsto eta (𝓝[>] (0 : ℝ)) (𝓝 (eta 0)) :=
    (hvelocity 0 ⟨le_rfl, hT⟩).2.continuousWithinAt.tendsto.mono_left
      (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      dist (eta 0) (eta h) < expDiffeoRadius g hEnorm (eta 0) := by
    have h := hcont.eventually
      (Metric.ball_mem_nhds (eta 0) (expDiffeoRadius_pos g hEnorm (eta 0)))
    simpa only [Metric.mem_ball, dist_comm] using h
  have heq : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      NormalCoordinates.normalChartAt (I := I) g (eta 0) (eta h) = (xi h : E) := by
    filter_upwards [hsmall] with h hh
    have hlen : Real.sqrt (g.inner (eta 0) (xi h) (xi h)) <
        expDiffeoRadius g hEnorm (eta 0) := by
      rw [(hxi h).2]
      exact hh
    have hsrc := expDiffeo_mem_of_lt g hEnorm (eta 0) hlen
    have hexp : NormalCoordinates.expMapDiffeo (I := I) g (eta 0) (xi h : E) = eta h :=
      (expDiffeo_eq_intr g hEnorm (eta 0) hlen).trans (hxi h).1
    have hleft := (NormalCoordinates.expMapDiffeo (I := I) g (eta 0)).left_inv hsrc
    rw [hexp] at hleft
    exact hleft
  convert! hlim.congr' (heq.mono (fun h hh => congrArg (fun v : E => h⁻¹ • v) hh.symm)) using 1

end DifferentialGeometry.Geometry.Topology

end
