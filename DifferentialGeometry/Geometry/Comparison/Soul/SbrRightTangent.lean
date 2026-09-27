import DifferentialGeometry.Geometry.Comparison.Soul.SbrDirectional
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

noncomputable section

open Asymptotics Bundle Filter Manifold MeasureTheory Set
open scoped Topology ContDiff Manifold NNReal ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

section ChartDistance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

set_option backward.isDefEq.respectTransparency false in
theorem exists_lipschitzOnWith_extChartAt_symm (p : M) :
    ∃ C : ℝ≥0, 0 < C ∧ ∃ r : ℝ, 0 < r ∧
      Metric.ball (extChartAt I p p) r ⊆ (extChartAt I p).target ∧
      LipschitzOnWith C (extChartAt I p).symm
        (Metric.ball (extChartAt I p p) r) := by
  obtain ⟨C, hCpos, hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt I p
  have hC' : ∀ᶠ y in 𝓝 (extChartAt I p p),
      ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) y‖ₑ < C := by
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ, nhdsWithin_univ] using hC
  have htarget : (extChartAt I p).target ∈ 𝓝 (extChartAt I p p) := by
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ, nhdsWithin_univ] using
      extChartAt_target_mem_nhdsWithin (I := I) p
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hC')
  refine ⟨C, hCpos, r, hr, fun z hz => (hball hz).1, ?_⟩
  intro u hu v hv
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ : ℝ → M := (extChartAt I p).symm ∘ η
  have hη : ∀ t ∈ Icc (0 : ℝ) 1,
      η t ∈ (extChartAt I p).target ∧
      ‖mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) (η t)‖ₑ < C := by
    intro t ht
    apply hball
    exact (convex_ball (extChartAt I p p) r).lineMap_mem hu hv ht
  have hηsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc 0 1) := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hlength : riemannianEDist I ((extChartAt I p).symm u)
      ((extChartAt I p).symm v) ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm p).comp hηsmooth (fun t ht => (hη t ht).1)
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  rw [IsRiemannianManifold.out (I := I)]
  apply hlength.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
  have hchain : mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc 0 1) t =
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) (η t)).comp
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η (Icc 0 1) t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη t ht).1
    · exact hηsmooth.mdifferentiableOn one_ne_zero t ht
    · exact fun t ht => extChartAt_target_subset_range p (hη t ht).1
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have happly : mfderivWithin 𝓘(ℝ, ℝ) I γ (Icc 0 1) t (1 : ℝ) =
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) (η t))
        (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, E) η (Icc 0 1) t (1 : ℝ)) :=
    congrArg (fun A => A (1 : ℝ)) hchain
  rw [happly]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη t ht).2.le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

theorem exists_dist_le_extChartAt (p : M) :
    ∃ C : ℝ≥0, 0 < C ∧ ∃ U : Set M, U ∈ 𝓝 p ∧
      ∀ x ∈ U, ∀ y ∈ U,
        dist x y ≤ C * ‖extChartAt I p x - extChartAt I p y‖ := by
  obtain ⟨C, hC, r, hr, _, hLip⟩ := exists_lipschitzOnWith_extChartAt_symm (I := I) p
  let U := (extChartAt I p).source ∩
    (extChartAt I p) ⁻¹' Metric.ball (extChartAt I p p) r
  have hU : U ∈ 𝓝 p := inter_mem (extChartAt_source_mem_nhds (I := I) p)
    ((continuousAt_extChartAt (I := I) p).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  refine ⟨C, hC, U, hU, ?_⟩
  intro x hx y hy
  have h := hLip.dist_le_mul _ hx.2 _ hy.2
  rw [(extChartAt I p).left_inv hx.1, (extChartAt I p).left_inv hy.1,
    dist_eq_norm] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem tendsto_dist_div_sub_of_same_right_velocity
    {α β : ℝ → M} {t₀ : ℝ}
    {A : TangentSpace 𝓘(ℝ, ℝ) t₀ →L[ℝ] TangentSpace I (α t₀)}
    {B : TangentSpace 𝓘(ℝ, ℝ) t₀ →L[ℝ] TangentSpace I (β t₀)}
    (hα : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I α (Ici t₀) t₀ A)
    (hβ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I β (Ici t₀) t₀ B)
    (hab : α t₀ = β t₀) (hvel : (A (1 : ℝ) : E) = (B (1 : ℝ) : E)) :
    Tendsto (fun t => dist (α t) (β t) / (t - t₀)) (𝓝[>] t₀) (𝓝 0) := by
  let p := α t₀
  let φ := extChartAt I p
  have hφa : MDifferentiableAt I 𝓘(ℝ, E) φ (α t₀) :=
    mdifferentiableAt_extChartAt (mem_chart_source H p)
  have hφb : MDifferentiableAt I 𝓘(ℝ, E) φ (β t₀) := by
    rw [← hab]
    exact hφa
  have hca := ((hφa.hasMFDerivAt.comp_hasMFDerivWithinAt t₀ hα).hasFDerivWithinAt
    (E := ℝ) (E' := E)).hasDerivWithinAt (F := E)
  have hcb := ((hφb.hasMFDerivAt.comp_hasMFDerivWithinAt t₀ hβ).hasFDerivWithinAt
    (E := ℝ) (E' := E)).hasDerivWithinAt (F := E)
  have hchartB : mfderiv I 𝓘(ℝ, E) (extChartAt I (α t₀)) (β t₀) =
      ContinuousLinearMap.id ℝ E := by
    rw [← hab]
    exact mfderiv_extChartAt_self
  have ha : HasDerivWithinAt (φ ∘ α) (show E from A (1 : ℝ)) (Ici t₀) t₀ := by
    convert! hca using 1
    simp only [φ, p, mfderiv_extChartAt_self]
    rfl
  have hb : HasDerivWithinAt (φ ∘ β) (show E from B (1 : ℝ)) (Ici t₀) t₀ := by
    convert! hcb using 1
    simp only [φ, p, hchartB]
    rfl
  have hzero : (fun t => φ (α t) - φ (β t)) =o[𝓝[Ici t₀] t₀] fun t => t - t₀ := by
    have h := (ha.sub hb).isLittleO
    simpa only [Pi.sub_apply, Function.comp_apply, hab, hvel, sub_self, smul_zero, sub_zero]
      using h
  obtain ⟨C, _, U, hU, hbound⟩ := exists_dist_le_extChartAt (I := I) p
  have hαU := hα.continuousWithinAt.preimage_mem_nhdsWithin hU
  have hUβ : U ∈ 𝓝 (β t₀) := by simpa only [p, hab] using hU
  have hβU := hβ.continuousWithinAt.preimage_mem_nhdsWithin hUβ
  have hO : (fun t => dist (α t) (β t)) =O[𝓝[Ici t₀] t₀]
      (fun t => φ (α t) - φ (β t)) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hαU, hβU] with t htα htβ
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hbound _ htα _ htβ
  exact ((hO.trans_isLittleO hzero).mono
    (nhdsWithin_mono _ Ioi_subset_Ici_self)).tendsto_div_nhds_zero

end ChartDistance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem tendsto_intrinsicRightDerivative_of_right_velocity
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    {γ : ℝ → M}
    {A : TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) →L[ℝ] TangentSpace I (γ 0)}
    (hγ : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I γ (Ici 0) 0 A)
    (hconc : ConcaveOn ℝ univ (fun t =>
      F (intrinsicGeodesic g hEnorm (γ 0) (A (1 : ℝ)) t))) :
    Tendsto (fun t => (F (γ t) - F (γ 0)) / t) (𝓝[>] 0)
      (𝓝 (intrinsicRightDerivative g hEnorm F (γ 0) (A (1 : ℝ)))) := by
  let η := intrinsicGeodesic g hEnorm (γ 0) (A (1 : ℝ))
  have hη : MDifferentiableAt 𝓘(ℝ, ℝ) I η (0 : ℝ) :=
    (intrinsicGeodesic_contMDiff g hEnorm (γ 0) (A (1 : ℝ))).contMDiffAt
      |>.mdifferentiableAt (by simp)
  have hdist : Tendsto (fun t => dist (γ t) (η t) / t) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_dist_div_sub_of_same_right_velocity hγ
      hη.hasMFDerivAt.hasMFDerivWithinAt
      (by simp [η]) (intrinsicGeodesic_mfderiv_zero g hEnorm (γ 0) (A (1 : ℝ))).symm
    simpa only [sub_zero] using h
  have herr : Tendsto (fun t => (F (γ t) - F (η t)) / t) (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hupper := (tendsto_const_nhds.mul hdist :
      Tendsto (fun t => (L : ℝ) * (dist (γ t) (η t) / t)) (𝓝[>] 0) (𝓝 ((L : ℝ) * 0)))
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa only [mul_zero] using hupper)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have h := hF.dist_le_mul (γ t) (η t)
    rw [Real.dist_eq] at h
    simpa only [Real.norm_eq_abs, abs_div, abs_of_pos htpos, mul_div_assoc] using
      div_le_div_of_nonneg_right h htpos.le
  have hlim := tendsto_intrinsicRightDerivative g hEnorm F (γ 0) (A (1 : ℝ)) hconc
  have h := herr.add hlim
  simp only [zero_add] at h
  apply h.congr'
  exact Eventually.of_forall fun t => by dsimp only [η]; ring

end DifferentialGeometry.Geometry.Topology
