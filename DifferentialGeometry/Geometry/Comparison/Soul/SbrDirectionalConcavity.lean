import DifferentialGeometry.Geometry.Comparison.Soul.SbrRightTangent
import DifferentialGeometry.Geometry.Comparison.Soul.NormalExpDerivative
import DifferentialGeometry.Geometry.Geodesic.Reparametrization.Affine

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

section CurveCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [I.Boundaryless] in
private theorem contMDiffAt_scaled_tangent_curve
    {ζ : ℝ → TangentBundle I M} {t : ℝ}
    (hζ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 ζ t) (a : ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨(ζ s).proj, a • (ζ s).snd⟩ : TangentBundle I M)) t := by
  have hs := Bundle.contMDiffAt_totalSpace.mp hζ
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hs.1, ?_⟩
  have hcoord : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (fun s => a • (trivializationAt E (TangentSpace I) (ζ t).proj (ζ s)).2) t := by
    rw [contMDiffAt_iff_contDiffAt]
    exact (contMDiffAt_iff_contDiffAt.mp hs.2).const_smul a
  apply hcoord.congr_of_eventuallyEq
  have hsrc : ∀ᶠ s in 𝓝 t, (ζ s).proj ∈ (chartAt H (ζ t).proj).source :=
    hs.1.continuousAt.preimage_mem_nhds
      ((chartAt H (ζ t).proj).open_source.mem_nhds (mem_chart_source H (ζ t).proj))
  filter_upwards [hsrc] with s hs
  exact chartFiberCoord_fiberScale (I := I) (ζ t).proj a hs

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
private theorem hasDerivAt_fixedChart_curve
    {γ : ℝ → M} {p : M} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0)
    (hγ0 : γ 0 = p) :
    HasDerivAt (fun t => extChartAt I p (γ t))
      (show E from mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) 0 := by
  have hchart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) (γ 0) := by
    rw [hγ0]
    exact mdifferentiableAt_extChartAt (mem_chart_source H p)
  have h := ((hchart.hasMFDerivAt.comp 0 hγ.hasMFDerivAt).hasFDerivAt
    (E := ℝ) (E' := E)).hasDerivAt (F := E)
  have hchartId : mfderiv I 𝓘(ℝ, E) (extChartAt I p) (γ 0) =
      ContinuousLinearMap.id ℝ E := by
    rw [hγ0]
    exact mfderiv_extChartAt_self
  convert! h using 1
  rw [hchartId]
  rfl

end CurveCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

set_option backward.isDefEq.respectTransparency false in
theorem exists_intrinsicGeodesic_interpolation_at_zero
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (v w : TangentSpace I p) (a : ℝ) :
    ∃ γ : ℝ → M, γ 0 = p ∧ ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ 0 ∧
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (1 - a) • v + a • w ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), ∃ q : M, ∃ u : TangentSpace I q,
        intrinsicGeodesic g hEnorm q u 0 = intrinsicGeodesic g hEnorm p v t ∧
        intrinsicGeodesic g hEnorm q u 1 = intrinsicGeodesic g hEnorm p w t ∧
        γ t = intrinsicGeodesic g hEnorm q u a := by
  let α := intrinsicGeodesic g hEnorm p v
  let β := intrinsicGeodesic g hEnorm p w
  let τ : ℝ → M × M := fun t => (α t, β t)
  let ζ : ℝ → TangentBundle I M := fun t => diagExpInv g hEnorm p (τ t)
  let p₀ : TangentBundle I M := ⟨p, (0 : E)⟩
  let z : ℝ → E × E := fun t => extChartAt I.tangent p₀ (ζ t)
  let Θ : ℝ → ℝ → M := fun c t =>
    expMapIntrinsic g hEnorm (ζ t).proj (c • (ζ t).snd)
  have hα0 : α 0 = p := intrinsicGeodesic_zero g hEnorm p v
  have hβ0 : β 0 = p := intrinsicGeodesic_zero g hEnorm p w
  have hτ0 : τ 0 = (p, p) := Prod.ext hα0 hβ0
  have hα : ContMDiffAt 𝓘(ℝ, ℝ) I 1 α 0 :=
    ((intrinsicGeodesic_contMDiff g hEnorm p v).of_le (by simp)).contMDiffAt
  have hβ : ContMDiffAt 𝓘(ℝ, ℝ) I 1 β 0 :=
    ((intrinsicGeodesic_contMDiff g hEnorm p w).of_le (by simp)).contMDiffAt
  have hτ : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod I) 1 τ 0 := hα.prodMk hβ
  have hζ0 : ζ 0 = p₀ := by
    dsimp only [ζ]
    rw [hτ0]
    exact diagExpInv_center g hEnorm p
  have hζ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1 ζ 0 := by
    have hInv : ContMDiffAt (I.prod I) I.tangent 1 (diagExpInv g hEnorm p) (τ 0) := by
      rw [hτ0]
      exact diagExpInv_contMDiffAt g hEnorm p
    exact hInv.comp 0 hτ
  have hz0 : z 0 = (extChartAt I p p, 0) := by
    dsimp only [z]
    rw [hζ0]
    rw [TangentBundle.extChartAt_tangent_zero_apply_chartFiber (I := I) p
      (p := p₀) (mem_chart_source H p)]
    exact Prod.ext rfl (TangentBundle.chartFiberCoord_self_zero (I := I) p)
  have hz : ContDiffAt ℝ 1 z 0 := by
    have hchart : ContMDiffAt I.tangent 𝓘(ℝ, E × E) 1
        (extChartAt I.tangent p₀) (ζ 0) := by
      rw [hζ0]
      exact contMDiffAt_extChartAt
    exact contMDiffAt_iff_contDiffAt.mp (hchart.comp 0 hζ)
  let z' : E × E := deriv z 0
  have hzd : HasDerivAt z z' 0 := (hz.differentiableAt one_ne_zero).hasDerivAt
  have hzd₁ : HasDerivAt (fun t => (z t).1) z'.1 0 :=
    (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := E) (p := z 0)).comp_hasDerivAt 0 hzd
  have hzd₂ : HasDerivAt (fun t => (z t).2) z'.2 0 :=
    (hasFDerivAt_snd (𝕜 := ℝ) (E := E) (F := E) (p := z 0)).comp_hasDerivAt 0 hzd
  have hscale (c : ℝ) : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun t => (⟨(ζ t).proj, c • (ζ t).snd⟩ : TangentBundle I M)) 0 :=
    contMDiffAt_scaled_tangent_curve hζ c
  have hΘ (c : ℝ) : ContMDiffAt 𝓘(ℝ, ℝ) I 1 (Θ c) 0 :=
    ((intrinsicExp_smooth g hEnorm).of_le (by simp)).contMDiffAt.comp 0 (hscale c)
  have hΘ0 (c : ℝ) : Θ c 0 = p := by
    dsimp only [Θ]
    rw [hζ0]
    change expMapIntrinsic g hEnorm p (c • (0 : TangentSpace I p)) = p
    rw [smul_zero, expMapIntrinsic_zero]
  have hbase : ∀ᶠ t in 𝓝 (0 : ℝ), (ζ t).proj ∈ (chartAt H p).source := by
    have hproj := (Bundle.contMDiffAt_totalSpace.mp hζ).1.continuousAt
    apply hproj.preimage_mem_nhds
    simpa only [hζ0, p₀] using
      (chartAt H p).open_source.mem_nhds (mem_chart_source H p)
  have hΘd (c : ℝ) : HasDerivAt (fun t => extChartAt I p (Θ c t))
      (z'.1 + c • z'.2) 0 := by
    have hsource : ∀ᶠ t in 𝓝 (0 : ℝ),
        (⟨(ζ t).proj, c • (ζ t).snd⟩ : TangentBundle I M) ∈
          (extChartAt I.tangent p₀).source := by
      apply (hscale c).continuousAt.preimage_mem_nhds
      rw [hζ0]
      simpa only [p₀, smul_zero] using
        extChartAt_source_mem_nhds (I := I.tangent) p₀
    have hgerm : (fun t => extChartAt I p (Θ c t)) =ᶠ[𝓝 (0 : ℝ)]
        (fun t => tangentChartExp g hEnorm p ((z t).1, c • (z t).2)) := by
      filter_upwards [hbase, hsource] with t ht hs
      have hrescale :
          extChartAt I.tangent p₀
              (⟨(ζ t).proj, c • (ζ t).snd⟩ : TangentBundle I M) =
            ((z t).1, c • (z t).2) :=
        extChartAt_tangent_zero_fiberScale (I := I) p c ht
      rw [← hrescale, tangentChartExp_apply,
        (extChartAt I.tangent p₀).left_inv hs]
    have he : HasFDerivAt (tangentChartExp g hEnorm p)
        (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E)
        ((z 0).1, c • (z 0).2) := by
      rw [hz0]
      simpa only [smul_zero] using tangentChartExp_hasFDerivAt_zero g hEnorm p
    have hd := he.comp_hasDerivAt 0 (hzd₁.prodMk (hzd₂.const_smul c))
    change HasDerivAt
      (fun t => tangentChartExp g hEnorm p ((z t).1, c • (z t).2))
      (z'.1 + c • z'.2) 0 at hd
    exact hd.congr_of_eventuallyEq hgerm
  have hproj : ∀ᶠ t in 𝓝 (0 : ℝ), (ζ t).proj = α t := by
    have ht : Tendsto τ (𝓝 (0 : ℝ)) (𝓝 (p, p)) := by
      simpa only [ContinuousAt, hτ0] using hτ.continuousAt
    exact ht.eventually (diagExpInv_proj g hEnorm p)
  have hend : ∀ᶠ t in 𝓝 (0 : ℝ),
      expMapIntrinsic g hEnorm (ζ t).proj (ζ t).snd = β t := by
    have ht : Tendsto τ (𝓝 (0 : ℝ)) (𝓝 (p, p)) := by
      simpa only [ContinuousAt, hτ0] using hτ.continuousAt
    exact ht.eventually (expIntr_diagExpInv g hEnorm p)
  have hΘzero : Θ 0 =ᶠ[𝓝 (0 : ℝ)] α := by
    filter_upwards [hproj] with t ht
    simpa only [Θ, zero_smul, expMapIntrinsic_zero] using ht
  have hΘone : Θ 1 =ᶠ[𝓝 (0 : ℝ)] β := by
    filter_upwards [hend] with t ht
    simpa only [Θ, one_smul] using ht
  have hαd : HasDerivAt (fun t => extChartAt I p (α t)) v 0 := by
    simpa only [α, intrinsicGeodesic_mfderiv_zero] using
      hasDerivAt_fixedChart_curve (hα.mdifferentiableAt one_ne_zero) hα0
  have hβd : HasDerivAt (fun t => extChartAt I p (β t)) w 0 := by
    simpa only [β, intrinsicGeodesic_mfderiv_zero] using
      hasDerivAt_fixedChart_curve (hβ.mdifferentiableAt one_ne_zero) hβ0
  have ha : z'.1 = v := by
    have hd := (hΘd 0).congr_of_eventuallyEq (hΘzero.symm.fun_comp (extChartAt I p))
    simpa only [zero_smul, add_zero] using hd.unique hαd
  have hab : z'.1 + z'.2 = w := by
    have hd := (hΘd 1).congr_of_eventuallyEq (hΘone.symm.fun_comp (extChartAt I p))
    simpa only [one_smul] using hd.unique hβd
  have hb : z'.2 = w - v := by
    rw [ha] at hab
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using hab
  refine ⟨Θ a, hΘ0 a, hΘ a, ?_, ?_⟩
  · have hv := (hΘd a).unique
      (hasDerivAt_fixedChart_curve ((hΘ a).mdifferentiableAt one_ne_zero) (hΘ0 a))
    rw [ha, hb] at hv
    calc
      (mfderiv 𝓘(ℝ, ℝ) I (Θ a) 0 (1 : ℝ) : E) = v + a • (w - v) := hv.symm
      _ = (1 - a) • v + a • w := by
        rw [smul_sub, sub_smul, one_smul]
        abel
  · filter_upwards [hproj, hend] with t ht he
    refine ⟨(ζ t).proj, (ζ t).snd, ?_, ?_, ?_⟩
    · simpa only [intrinsicGeodesic_zero] using ht
    · simpa only [expMapIntrinsic_def] using he
    · exact intrinsicGeodesic_smul g hEnorm (ζ t).proj (ζ t).snd a

set_option backward.isDefEq.respectTransparency false in
theorem concaveOn_intrinsicRightDerivative
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) : ConcaveOn ℝ univ (intrinsicRightDerivative g hEnorm F p) := by
  refine ⟨convex_univ, ?_⟩
  intro v _ w _ a b ha hb hab
  obtain ⟨γ, hγ0, hγ, hvel, hsegments⟩ :=
    exists_intrinsicGeodesic_interpolation_at_zero g hEnorm p v w b
  have hvel' : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = a • v + b • w := by
    simpa only [show 1 - b = a by linarith] using hvel
  have hright := tendsto_intrinsicRightDerivative_of_right_velocity g hEnorm hF
    (hγ.mdifferentiableAt one_ne_zero).hasMFDerivAt.hasMFDerivWithinAt (hconc _ _)
  have hright' : Tendsto (fun t => (F (γ t) - F p) / t) (𝓝[>] 0)
      (𝓝 (intrinsicRightDerivative g hEnorm F p (a • v + b • w))) := by
    rw [hvel'] at hright
    rw [hγ0] at hright
    exact hright
  have hv := tendsto_intrinsicRightDerivative g hEnorm F p v (hconc p v)
  have hw := tendsto_intrinsicRightDerivative g hEnorm F p w (hconc p w)
  have hleft : Tendsto
      (fun t => a * ((F (intrinsicGeodesic g hEnorm p v t) - F p) / t) +
        b * ((F (intrinsicGeodesic g hEnorm p w t) - F p) / t)) (𝓝[>] 0)
      (𝓝 (a * intrinsicRightDerivative g hEnorm F p v +
        b * intrinsicRightDerivative g hEnorm F p w)) :=
    (tendsto_const_nhds.mul hv).add (tendsto_const_nhds.mul hw)
  change a * intrinsicRightDerivative g hEnorm F p v +
    b * intrinsicRightDerivative g hEnorm F p w ≤
      intrinsicRightDerivative g hEnorm F p (a • v + b • w)
  apply le_of_tendsto_of_tendsto hleft hright'
  filter_upwards [hsegments.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with t ht htpos
  obtain ⟨q, u, hu0, hu1, hub⟩ := ht
  have hpoint := (hconc q u).2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at hpoint
  rw [hu0, hu1, ← hub] at hpoint
  have hsum : a * F p + b * F p = F p := by rw [← add_mul, hab, one_mul]
  have hnum : a * (F (intrinsicGeodesic g hEnorm p v t) - F p) +
      b * (F (intrinsicGeodesic g hEnorm p w t) - F p) ≤ F (γ t) - F p := by
    nlinarith [hpoint, hsum]
  simpa only [add_div, mul_div_assoc] using div_le_div_of_nonneg_right hnum htpos.le

theorem intrinsicRightDerivative_superadditive
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) (v w : TangentSpace I p) :
    intrinsicRightDerivative g hEnorm F p v + intrinsicRightDerivative g hEnorm F p w ≤
      intrinsicRightDerivative g hEnorm F p (v + w) := by
  have hc := concaveOn_intrinsicRightDerivative g hEnorm hF hconc p
  have hm : (1 / 2 : ℝ) • intrinsicRightDerivative g hEnorm F p v +
      (1 / 2 : ℝ) • intrinsicRightDerivative g hEnorm F p w ≤
        intrinsicRightDerivative g hEnorm F p ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) :=
    hc.2 (mem_univ v) (mem_univ w) (by norm_num) (by norm_num) (by norm_num)
  have hh := intrinsicRightDerivative_smul g hEnorm F p
    ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) (hconc p _) (a := 2) (by norm_num)
  have hdouble : (2 : ℝ) • ((1 / 2 : ℝ) • v + (1 / 2 : ℝ) • w) = v + w := by
    simp only [smul_add, smul_smul]
    norm_num
  rw [hdouble] at hh
  simp only [smul_eq_mul] at hm
  linarith

theorem abs_intrinsicRightDerivative_sub_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (p : M) (v w : TangentSpace I p) :
    |intrinsicRightDerivative g hEnorm F p v - intrinsicRightDerivative g hEnorm F p w| ≤
      L * Real.sqrt (g.inner p (v - w) (v - w)) := by
  have hv := intrinsicRightDerivative_superadditive g hEnorm hF hconc p w (v - w)
  have hw := intrinsicRightDerivative_superadditive g hEnorm hF hconc p v (w - v)
  rw [show w + (v - w) = v by abel] at hv
  rw [show v + (w - v) = w by abel] at hw
  have hnv := abs_intrinsicRightDerivative_le g hEnorm hF p (v - w) (hconc p _)
  have hnw := abs_intrinsicRightDerivative_le g hEnorm hF p (w - v) (hconc p _)
  have hinner : g.inner p (w - v) (w - v) = g.inner p (v - w) (v - w) := by
    rw [show w - v = -(v - w) by abel]
    simp only [map_neg, neg_apply, neg_neg]
  rw [hinner] at hnw
  apply abs_le.mpr
  constructor
  · have hlow := (abs_le.mp hnv).1
    linarith
  · have hlow := (abs_le.mp hnw).1
    linarith

end DifferentialGeometry.Geometry.Topology
