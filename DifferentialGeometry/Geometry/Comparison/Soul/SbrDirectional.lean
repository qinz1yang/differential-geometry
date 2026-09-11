import DifferentialGeometry.Geometry.Comparison.Soul.SoulConvexCore
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

def intrinsicRightDerivative
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) (v : TangentSpace I p) : ℝ :=
  derivWithin (fun t => F (intrinsicGeodesic g hEnorm p v t)) (Ioi 0) 0

theorem hasDerivWithinAt_intrinsicRightDerivative
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) (v : TangentSpace I p)
    (hconc : ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t))) :
    HasDerivWithinAt (fun t => F (intrinsicGeodesic g hEnorm p v t))
      (intrinsicRightDerivative g hEnorm F p v) (Ioi 0) 0 := by
  have h := (hconc.neg.differentiableWithinAt_Ioi_of_mem_interior
    (by simp : (0 : ℝ) ∈ interior (univ : Set ℝ))).neg
  simpa only [Pi.neg_apply, neg_neg, intrinsicRightDerivative] using h.hasDerivWithinAt

theorem tendsto_intrinsicRightDerivative
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) (v : TangentSpace I p)
    (hconc : ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t))) :
    Tendsto (fun t => (F (intrinsicGeodesic g hEnorm p v t) - F p) / t)
      (𝓝[>] 0) (𝓝 (intrinsicRightDerivative g hEnorm F p v)) := by
  have h := (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp
    (hasDerivWithinAt_intrinsicRightDerivative g hEnorm F p v hconc)
  change Tendsto (fun t => slope (fun s => F (intrinsicGeodesic g hEnorm p v s)) 0 t)
    (𝓝[>] 0) (𝓝 (intrinsicRightDerivative g hEnorm F p v)) at h
  simpa only [slope_def_field, intrinsicGeodesic_zero, sub_zero] using h


@[simp] theorem intrinsicRightDerivative_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) :
    intrinsicRightDerivative g hEnorm F p 0 = 0 := by
  have hconstant (t : ℝ) : intrinsicGeodesic g hEnorm p 0 t = p := by
    rw [← intrinsicGeodesic_smul, smul_zero, ← expMapIntrinsic_def,
      expMapIntrinsic_zero]
  simp [intrinsicRightDerivative, hconstant]

theorem intrinsicRightDerivative_smul
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) (v : TangentSpace I p)
    (hconc : ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    {a : ℝ} (ha : 0 ≤ a) :
    intrinsicRightDerivative g hEnorm F p (a • v) =
      a * intrinsicRightDerivative g hEnorm F p v := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp
  have hscale : HasDerivWithinAt (fun t : ℝ => a * t) a (Ioi 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).hasDerivWithinAt
  have h := (hasDerivWithinAt_intrinsicRightDerivative
    g hEnorm F p v hconc).comp_of_eq 0 hscale
      (fun t ht => mul_pos ha ht) (by simp)
  have heq : (fun t => F (intrinsicGeodesic g hEnorm p (a • v) t)) =
      (fun t => F (intrinsicGeodesic g hEnorm p v (a * t))) := by
    funext t
    exact congrArg F (intrinsicGeo_smul_apply g hEnorm p v a t)
  rw [intrinsicRightDerivative, heq]
  simpa only [Function.comp_def, mul_comm] using
    h.derivWithin (uniqueDiffWithinAt_Ioi 0)

theorem slope_le_intrinsicRightDerivative
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) (v : TangentSpace I p)
    (hconc : ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    {t : ℝ} (ht : 0 < t) :
    (F (intrinsicGeodesic g hEnorm p v t) - F p) / t ≤
      intrinsicRightDerivative g hEnorm F p v := by
  have h := hconc.slope_le_of_hasDerivWithinAt_Ioi (mem_univ 0) (mem_univ t)
    ht (hasDerivWithinAt_intrinsicRightDerivative g hEnorm F p v hconc)
  simpa only [slope_def_field, intrinsicGeodesic_zero, sub_zero] using h

theorem isLUB_intrinsicRightDerivative
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) (v : TangentSpace I p)
    (hconc : ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t))) :
    IsLUB ((fun t => (F (intrinsicGeodesic g hEnorm p v t) - F p) / t) '' Ioi 0)
      (intrinsicRightDerivative g hEnorm F p v) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact slope_le_intrinsicRightDerivative g hEnorm F p v hconc ht
  · intro a ha
    apply le_of_tendsto (tendsto_intrinsicRightDerivative g hEnorm F p v hconc)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ha (mem_image_of_mem _ ht)


theorem intrinsicRightDerivative_eq_sSup
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) (v : TangentSpace I p)
    (hconc : ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t))) :
    intrinsicRightDerivative g hEnorm F p v =
      sSup ((fun t => (F (intrinsicGeodesic g hEnorm p v t) - F p) / t) '' Ioi 0) :=
  ((isLUB_intrinsicRightDerivative g hEnorm F p v hconc).csSup_eq
    ⟨_, mem_image_of_mem _ (show (1 : ℝ) ∈ Ioi 0 by norm_num)⟩).symm

theorem abs_intrinsicRightDerivative_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (p : M) (v : TangentSpace I p)
    (hconc : ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t))) :
    |intrinsicRightDerivative g hEnorm F p v| ≤
      L * Real.sqrt (g.inner p v v) := by
  apply le_of_tendsto (tendsto_intrinsicRightDerivative g hEnorm F p v hconc).abs
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have hdist := intrinsicGeodesic_riemannianEDist_le g hEnorm p v ht.le
  have hd := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg,
    ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr ht.le)),
    intrinsicGeodesic_zero, sub_zero] at hd
  have hLip := hF.dist_le_mul (intrinsicGeodesic g hEnorm p v t) p
  rw [Real.dist_eq] at hLip
  rw [abs_div, abs_of_pos htpos]
  apply (div_le_iff₀ htpos).2
  have hbound := hLip.trans (mul_le_mul_of_nonneg_left
    (by simpa only [dist_comm] using hd) L.coe_nonneg)
  simpa only [mul_assoc] using hbound

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [CompleteSpace M] [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem continuous_scale_tangent (a : ℝ) :
    Continuous (fun z : TangentBundle I M =>
      (⟨z.proj, a • z.snd⟩ : TangentBundle I M)) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hz := (FiberBundle.continuousAt_totalSpace E _).mp
    (continuousAt_id : ContinuousAt (fun z : TangentBundle I M => z) z)
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hz.1, ?_⟩
  let e := trivializationAt E (TangentSpace I) z.proj
  have he : ∀ᶠ w in 𝓝 z, w.proj ∈ e.baseSet :=
    hz.1.preimage_mem_nhds (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E _ _))
  apply ((continuousAt_const (y := a)).smul hz.2).congr_of_eventuallyEq
  filter_upwards [he] with w hw
  exact (e.linear ℝ hw).map_smul a w.snd

theorem continuous_intrinsicGeodesic_fixed_time
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g) (t : ℝ) :
    Continuous (fun z : TangentBundle I M =>
      intrinsicGeodesic g hEnorm z.proj z.snd t) := by
  have h := (intrinsicExp_smooth g hEnorm).continuous.comp
    (continuous_scale_tangent (I := I) (M := M) t)
  simpa only [Function.comp_def, expMapIntrinsic_def, intrinsicGeodesic_smul] using h

theorem lowerSemicontinuous_intrinsicRightDerivative
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} (hF : Continuous F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t))) :
    LowerSemicontinuous (fun z : TangentBundle I M =>
      intrinsicRightDerivative g hEnorm F z.proj z.snd) := by
  intro z a ha
  have hlim := tendsto_intrinsicRightDerivative g hEnorm F z.proj z.snd
    (hconc z.proj z.snd)
  have hboth : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧
      a < (F (intrinsicGeodesic g hEnorm z.proj z.snd t) - F z.proj) / t := by
    filter_upwards [self_mem_nhdsWithin, hlim.eventually (lt_mem_nhds ha)] with t ht hat
    exact ⟨ht, hat⟩
  obtain ⟨t, ht, hat⟩ := hboth.exists
  have hcont : Continuous (fun w : TangentBundle I M =>
      (F (intrinsicGeodesic g hEnorm w.proj w.snd t) - F w.proj) / t) := by
    exact ((hF.comp (continuous_intrinsicGeodesic_fixed_time g hEnorm t)).sub
      (hF.comp (FiberBundle.continuous_proj E (TangentSpace I)))).div_const t
  filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hat)] with w hw
  exact hw.trans_le (slope_le_intrinsicRightDerivative g hEnorm F w.proj w.snd
    (hconc w.proj w.snd) ht)

end DifferentialGeometry.Geometry.Topology
