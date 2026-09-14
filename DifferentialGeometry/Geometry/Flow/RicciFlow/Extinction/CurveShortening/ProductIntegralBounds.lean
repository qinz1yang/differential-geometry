import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductBackground
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.IntegralBounds
import DifferentialGeometry.Analysis.Integration.Periodic

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
    {D : RealTimeInterval} {a b s u : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
theorem arcLength_le_length (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (p q t : ℝ) (hqp : q ≤ p + 1) (ht : t ∈ J) :
    c.arcLength g lambda p q t ≤ c.length g lambda t := by
  have hspd := (c.speed_contDiff_of_immersedOn g lambda hlambda hc hi t ht).continuous
  have h := (c.speed_periodic g lambda hc t ht).intervalIntegral_le_period
    (a := 0) (by simpa only [zero_add] using hspd.intervalIntegrable (μ := volume) 0 1)
    (fun x => c.speed_nonneg g lambda x t) hqp
  simpa only [zero_add, ProductCurve.arcLength, ProductCurve.length, ProductCurve.integral, one_mul]
    using h

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem arcTotalCurvature_le_totalCurvature (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (p q t : ℝ) (hqp : q ≤ p + 1) (ht : t ∈ J) :
    c.arcTotalCurvature g lambda p q t ≤ c.totalCurvature g lambda t := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  let ghat := fun τ => quotientProductMetric A (g τ) lambda hlambda
  have hs := c.smoothOn_map A hc
  have him := (c.map_immersedOn_iff A hc).mpr hi
  have hsq : Continuous (fun x => c.curvatureSq g lambda x t) := by
    simpa only [ghat, c.map_curvatureSq_eq A g lambda hlambda hc hi _ t ht] using
      (c.map.curvatureSq_contDiff ghat J hs him t ht).continuous
  have hsp := (c.speed_contDiff_of_immersedOn g lambda hlambda hc hi t ht).continuous
  have hper : Function.Periodic (fun x => c.curvatureSq g lambda x t) 1 := by
    intro x
    have h := c.map.curvatureSq_speed_periodic ghat J hs him t ht x
    simp only [ghat, c.map_curvatureSq_eq A g lambda hlambda hc hi _ t ht,
      c.map_speed_eq A g lambda hlambda hc _ t ht, c.speed_add_period g lambda hc t ht x] at h
    exact mul_right_cancel₀ (ne_of_gt (c.speed_pos_of_immersedOn g lambda hlambda hi x t ht)) h
  have hper' : Function.Periodic (fun x => c.curvature g lambda x t * c.speed g lambda x t) 1 := by
    intro x
    simp only [ProductCurve.curvature, hper x, c.speed_add_period g lambda hc t ht x]
  have h := hper'.intervalIntegral_le_period (a := 0)
    ((show Continuous (fun x => c.curvature g lambda x t * c.speed g lambda x t) from
      hsq.sqrt.mul hsp).intervalIntegrable 0 (0 + 1))
    (fun x => mul_nonneg (Real.sqrt_nonneg _) (c.speed_nonneg g lambda x t)) hqp
  simpa only [zero_add, ProductCurve.arcTotalCurvature, ProductCurve.totalCurvature,
    ProductCurve.integral] using h

theorem totalCurvature_add_length_le_exp
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hc : c.IsSolutionOn B.family.metric lambda J)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (hinterval : Icc s u ⊆ J)
    (r t : ℝ) (hr : r ∈ Icc s u) (ht : t ∈ Icc r u) :
    c.totalCurvature B.family.metric lambda t + c.length B.family.metric lambda t ≤
      Real.exp ((B.C + B.B₀) * (t - r)) *
        (c.totalCurvature B.family.metric lambda r + c.length B.family.metric lambda r) := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, h0, _, _, hC⟩ := hB lambda hlambda
  have hm : Bhat.family.metric = fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc s u) := by
    rw [hm]
    exact (c.isSolutionOn_map A B.family.metric lambda hlambda hJ hc).mono hinterval
      (fun t ht => ((uniqueDiffOn_Icc hsu) t ht).uniqueMDiffWithinAt)
  have hbound := (rfs_csf_integral_bounds Bhat hsu hwindow c.map hsol).2.2.2.2 r hr t ht
  have htt : t ∈ J := hinterval ⟨hr.1.trans ht.1, ht.2⟩
  have hrr : r ∈ J := hinterval hr
  simpa only [hm, h0, hC,
    c.map_totalCurvature_eq A B.family.metric lambda hlambda hc.smooth hc.immersed t htt,
    c.map_length_eq A B.family.metric lambda hlambda hc.smooth t htt,
    c.map_totalCurvature_eq A B.family.metric lambda hlambda hc.smooth hc.immersed r hrr,
    c.map_length_eq A B.family.metric lambda hlambda hc.smooth r hrr] using hbound.2.2.2

theorem length_and_totalCurvature_le_initial
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hc : c.IsSolutionOn B.family.metric lambda J)
    (hau : a < u) (hub : u ≤ b) (hinterval : Icc a u ⊆ J)
    {L₀ Θ₀ : ℝ} (hL₀ : c.length B.family.metric lambda a ≤ L₀)
    (hΘ₀ : c.totalCurvature B.family.metric lambda a ≤ Θ₀)
    (t : ℝ) (ht : t ∈ Icc a u) :
    c.length B.family.metric lambda t ≤ Real.exp ((B.C + B.B₀) * (b - a)) * (Θ₀ + L₀) ∧
      c.totalCurvature B.family.metric lambda t ≤
        Real.exp ((B.C + B.B₀) * (b - a)) * (Θ₀ + L₀) := by
  have hL (v : ℝ) : 0 ≤ c.length B.family.metric lambda v :=
    intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun x _ => mul_nonneg zero_le_one (c.speed_nonneg B.family.metric lambda x v))
  have hΘ (v : ℝ) : 0 ≤ c.totalCurvature B.family.metric lambda v :=
    intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun x _ => mul_nonneg (Real.sqrt_nonneg _) (c.speed_nonneg B.family.metric lambda x v))
  have hK : 0 ≤ B.C + B.B₀ := by
    rw [RicciBackground.C]
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hbound := c.totalCurvature_add_length_le_exp B lambda hlambda hJ hc hau
    (Icc_subset_Icc le_rfl hub) hinterval a t ⟨le_rfl, hau.le⟩ ht
  have hexp : Real.exp ((B.C + B.B₀) * (t - a)) ≤
      Real.exp ((B.C + B.B₀) * (b - a)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right (ht.2.trans hub) a) hK)
  have hmul := mul_le_mul hexp (add_le_add hΘ₀ hL₀)
    (add_nonneg (hΘ a) (hL a)) (Real.exp_pos ((B.C + B.B₀) * (b - a))).le
  constructor <;> linarith [hL t, hΘ t]

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
