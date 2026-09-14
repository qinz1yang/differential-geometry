import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductBackground
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CurvatureConcentration
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
theorem exists_centered_arcLength_eq (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) {r : ℝ} (hr : 0 < r) (hlen : r ≤ c.length g lambda t) :
    ∃ p q : ℝ, p < x ∧ x < q ∧ q ≤ p + 1 ∧
      c.arcLength g lambda p x t = r / 2 ∧ c.arcLength g lambda x q t = r / 2 ∧
        c.arcLength g lambda p q t = r := by
  have hsp := (c.speed_contDiff_of_immersedOn g lambda hlambda hc hi t ht).continuous
  have hperiod := c.speed_periodic g lambda hc t ht
  have hlen' : r ≤ ∫ y in (0 : ℝ)..0 + 1, c.speed g lambda y t := by
    simpa only [ProductCurve.length, ProductCurve.integral, one_mul, zero_add] using hlen
  obtain ⟨p, q, hpx, hxq, hqp, hleft, hright, hall⟩ :=
    hperiod.exists_centered_intervalIntegral_eq hsp zero_le_one hr.le hlen' x
  have hpx' : p < x := by
    by_contra h
    have heq : p = x := le_antisymm hpx (le_of_not_gt h)
    subst p
    rw [intervalIntegral.integral_same] at hleft
    linarith
  have hxq' : x < q := by
    by_contra h
    have heq : q = x := le_antisymm (le_of_not_gt h) hxq
    subst q
    rw [intervalIntegral.integral_same] at hright
    linarith
  exact ⟨p, q, hpx', hxq', hqp, hleft, hright, hall⟩


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

theorem weighted_total_curvature_le_of_initial_and_sqrt_cutoff_bound
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : ProductCurve M) (lambda : ℝ) (hlambda : 0 < lambda)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hc : c.IsSolutionOn B.family.metric lambda J)
    (has : a ≤ s) (hsu : s < u) (hub : u ≤ b) (hinterval : Icc a u ⊆ J)
    {L₀ Θ₀ δ p q t : ℝ}
    (hL₀ : c.length B.family.metric lambda a ≤ L₀)
    (hΘ₀ : c.totalCurvature B.family.metric lambda a ≤ Θ₀)
    (hpq : p ≤ q) (hqp : q ≤ p + 1) (ht : t ∈ Icc s u)
    (hsmall : c.arcTotalCurvature B.family.metric lambda p q s ≤ δ)
    {φ φt : ℝ → ℝ → ℝ} {α β : ℝ}
    (hφc : ContinuousOn (fun z : ℝ × ℝ => φ z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφtc : ContinuousOn (fun z : ℝ × ℝ => φt z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφt : ∀ x ∈ Icc p q, ∀ τ ∈ Icc s u,
      HasDerivWithinAt (fun σ => φ x σ) (φt x τ) (Icc s u) τ)
    (hφxx : ∀ τ ∈ Ioo s t, ∀ x ∈ Icc p q, ContDiffAt ℝ 2 (fun y => φ y τ) x)
    (hφrange : ∀ τ ∈ Icc s t, ∀ x ∈ Icc p q, φ x τ ∈ Icc 0 1)
    (hφboundary : ∀ τ ∈ Ioo s t, φ p τ = 0 ∧ φ q τ = 0 ∧
      deriv (fun y => φ y τ) p = 0 ∧ deriv (fun y => φ y τ) q = 0)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hcut : ∀ τ ∈ Ioo s t, ∀ x ∈ Icc p q,
      φt x τ + c.ds B.family.metric lambda (c.ds B.family.metric lambda φ) x τ ≤
        α / Real.sqrt (τ - s) + β) :
    (∫ x in p..q, φ x t * c.curvature B.family.metric lambda x t * c.speed B.family.metric lambda x t) ≤
      δ + Real.exp ((B.C + B.B₀) * (b - a)) * (Θ₀ + L₀) *
        (2 * α * Real.sqrt (t - s) + (β + (B.C + B.B₀)) * (t - s)) +
      B.C * (Real.exp ((B.C + B.B₀) * (b - a)) * (Θ₀ + L₀)) * (t - s) := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, h0, _, _, hC⟩ := hB lambda hlambda
  have hm : Bhat.family.metric = fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  have hsub : Icc s u ⊆ J := (Icc_subset_Icc has le_rfl).trans hinterval
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc s u) := by
    rw [hm]
    exact (c.isSolutionOn_map A B.family.metric lambda hlambda hJ hc).mono hsub
      (fun τ hτ => ((uniqueDiffOn_Icc hsu) τ hτ).uniqueMDiffWithinAt)
  have hspeed (x τ : ℝ) (hτ : τ ∈ Icc s u) :
      c.map.speed Bhat.family.metric x τ = c.speed B.family.metric lambda x τ := by
    rw [hm]
    exact c.map_speed_eq A B.family.metric lambda hlambda hc.smooth x τ (hsub hτ)
  have hcurv (x τ : ℝ) (hτ : τ ∈ Icc s u) :
      c.map.curvature Bhat.family.metric x τ = c.curvature B.family.metric lambda x τ := by
    dsimp only [CurveMap.curvature, ProductCurve.curvature]
    rw [hm, c.map_curvatureSq_eq A B.family.metric lambda hlambda hc.smooth hc.immersed x τ (hsub hτ)]
  have hds (f : ℝ → ℝ → ℝ) (x τ : ℝ) (hτ : τ ∈ Icc s u) :
      c.map.ds Bhat.family.metric f x τ = c.ds B.family.metric lambda f x τ := by
    rw [hm]
    exact c.map_ds_eq A B.family.metric lambda hlambda hc.smooth f x τ (hsub hτ)
  let Q := Real.exp ((B.C + B.B₀) * (b - a)) * (Θ₀ + L₀)
  have hglobal (τ : ℝ) (hτ : τ ∈ Icc s u) :
      c.length B.family.metric lambda τ ≤ Q ∧ c.totalCurvature B.family.metric lambda τ ≤ Q :=
    c.length_and_totalCurvature_le_initial B lambda hlambda hJ hc (has.trans_lt hsu) hub
      hinterval hL₀ hΘ₀ τ ⟨has.trans hτ.1, hτ.2⟩
  have hL : ∀ τ ∈ Icc s t, (∫ x in p..q, c.map.speed Bhat.family.metric x τ) ≤ Q := by
    intro τ hτ
    have hτu : τ ∈ Icc s u := ⟨hτ.1, hτ.2.trans ht.2⟩
    have he : (∫ x in p..q, c.map.speed Bhat.family.metric x τ) =
        c.arcLength B.family.metric lambda p q τ :=
      intervalIntegral.integral_congr (fun x _ => hspeed x τ hτu)
    rw [he]
    exact (c.arcLength_le_length B.family.metric lambda hlambda hc.smooth hc.immersed p q τ hqp
      (hsub hτu)).trans (hglobal τ hτu).1
  have hΘ : ∀ τ ∈ Ioo s t,
      (∫ x in p..q, c.map.curvature Bhat.family.metric x τ * c.map.speed Bhat.family.metric x τ) ≤ Q := by
    intro τ hτ
    have hτu : τ ∈ Icc s u := ⟨hτ.1.le, hτ.2.le.trans ht.2⟩
    have he : (∫ x in p..q, c.map.curvature Bhat.family.metric x τ * c.map.speed Bhat.family.metric x τ) =
        c.arcTotalCurvature B.family.metric lambda p q τ := by
      apply intervalIntegral.integral_congr
      intro x _
      exact congrArg₂ (fun v w : ℝ => v * w) (hcurv x τ hτu) (hspeed x τ hτu)
    rw [he]
    exact (c.arcTotalCurvature_le_totalCurvature B.family.metric lambda hlambda hc.smooth hc.immersed
      p q τ hqp (hsub hτu)).trans (hglobal τ hτu).2
  have hcutmap : ∀ τ ∈ Ioo s t, ∀ x ∈ Icc p q,
      φt x τ + c.map.ds Bhat.family.metric (c.map.ds Bhat.family.metric φ) x τ ≤
        α / Real.sqrt (τ - s) + β := by
    intro τ hτ x hx
    have hτu : τ ∈ Icc s u := ⟨hτ.1.le, hτ.2.le.trans ht.2⟩
    rw [hds (c.map.ds Bhat.family.metric φ) x τ hτu]
    have he : (fun y => c.map.ds Bhat.family.metric φ y τ) =
        (fun y => c.ds B.family.metric lambda φ y τ) := funext (fun y => hds φ y τ hτu)
    change φt x τ + (c.speed B.family.metric lambda x τ)⁻¹ *
      deriv (fun y => c.map.ds Bhat.family.metric φ y τ) x ≤ _
    rw [he]
    exact hcut τ hτ x hx
  have hbound := CurveShortening.weighted_total_curvature_le_of_sqrt_cutoff_bound Bhat hsu
    (Icc_subset_Icc has hub) c.map hsol hpq ht hφc hφtc hφt hφxx hφrange hφboundary hα hβ hcutmap hL hΘ
  have hs : s ∈ Icc s u := ⟨le_rfl, hsu.le⟩
  have hE (τ : ℝ) (hτ : τ ∈ Icc s u) :
      (∫ x in p..q, φ x τ * c.map.curvature Bhat.family.metric x τ * c.map.speed Bhat.family.metric x τ) =
        ∫ x in p..q, φ x τ * c.curvature B.family.metric lambda x τ * c.speed B.family.metric lambda x τ := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg₂ (fun v w : ℝ => φ x τ * v * w) (hcurv x τ hτ) (hspeed x τ hτ)
  have hstart : (∫ x in p..q, φ x s * c.map.curvature Bhat.family.metric x s * c.map.speed Bhat.family.metric x s) ≤ δ := by
    have hsp := (c.map.speed_contDiff Bhat.family.metric (Icc s u) hsol.smooth hsol.immersed s hs).continuous
    have hk := (c.map.curvatureSq_contDiff Bhat.family.metric (Icc s u) hsol.smooth hsol.immersed s hs).continuous.sqrt
    have hφs : ContinuousOn (fun x => φ x s) (Icc p q) := hφc.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, hs⟩)
    have hweighted : ContinuousOn (fun x => φ x s * c.map.curvature Bhat.family.metric x s *
        c.map.speed Bhat.family.metric x s) (Icc p q) := (hφs.mul hk.continuousOn).mul hsp.continuousOn
    have hintegral := intervalIntegral.integral_mono_on (μ := volume) hpq
      (hweighted.intervalIntegrable_of_Icc hpq)
      ((show Continuous (fun x => c.map.curvature Bhat.family.metric x s * c.map.speed Bhat.family.metric x s) from
        hk.mul hsp).intervalIntegrable p q)
      (fun x hx => by
        have hφle := (hφrange s ⟨le_rfl, ht.1⟩ x hx).2
        have hnn : 0 ≤ c.map.curvature Bhat.family.metric x s * c.map.speed Bhat.family.metric x s :=
          mul_nonneg (Real.sqrt_nonneg _) (c.map.speed_nonneg Bhat.family.metric x s)
        simpa only [mul_assoc, one_mul] using mul_le_mul_of_nonneg_right hφle hnn)
    have he : (∫ x in p..q, c.map.curvature Bhat.family.metric x s * c.map.speed Bhat.family.metric x s) =
        c.arcTotalCurvature B.family.metric lambda p q s := by
      apply intervalIntegral.integral_congr
      intro x _
      exact congrArg₂ (fun v w : ℝ => v * w) (hcurv x s hs) (hspeed x s hs)
    exact hintegral.trans (he.le.trans hsmall)
  rw [hE t ht, h0, hC] at hbound
  dsimp only [Q] at hbound
  linarith


omit [SigmaCompactSpace M] in
theorem exists_uniform_curvature_concentration [CompactSpace M]
    (B : RicciBackground (I := I) (M := M) D a b) :
    ∃ C : ℝ, B.C ≤ C ∧ ∀ lambda : ℝ, 0 < lambda → ∀ c : ProductCurve M,
      ∀ J : Set ℝ, UniqueDiffOn ℝ J → c.IsSolutionOn B.family.metric lambda J →
      ∀ s u K : ℝ, s < u → Icc s u ⊆ Icc a b → Icc s u ⊆ J → 1 ≤ K → u - s ≤ 1 →
      (∀ x t, t ∈ Ioc s u → c.curvatureSq B.family.metric lambda x t ≤ K / (t - s)) →
      ∀ p q : ℝ, p ≤ q →
      1 / (64 * (1 + 64 * (1 + C)) * Real.sqrt (K / (u - s))) ≤ c.arcLength B.family.metric lambda p q u →
      K / (2 * (u - s)) ≤ c.curvatureSq B.family.metric lambda p u →
      ∃ v ∈ Icc p q,
        c.arcLength B.family.metric lambda p v u = 1 / (64 * (1 + 64 * (1 + C)) * Real.sqrt (K / (u - s))) ∧
        1 / (128 * (1 + 64 * (1 + C))) ≤ c.arcTotalCurvature B.family.metric lambda p v u := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  obtain ⟨C, hC, _, _, hprod⟩ := B.exists_uniform_product_curvature_derivative_bounds A
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda c J hJ hc s u K hsu hwindow hinterval hK hlen hk p q hpq harc hpeak
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hBG⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hfamily, _, _, _, hBC⟩ := hBG lambda hlambda
  have hm : Bhat.family.metric = fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun G => G.metric) hfamily
  have hsol : c.map.IsSolutionOn Bhat.family.metric (Icc s u) := by
    rw [hm]
    exact (c.isSolutionOn_map A B.family.metric lambda hlambda hJ hc).mono hinterval
      (fun t ht => (uniqueDiffOn_Icc hsu t ht).uniqueMDiffWithinAt)
  have hsq (x t : ℝ) (ht : t ∈ Icc s u) :
      c.map.curvatureSq Bhat.family.metric x t = c.curvatureSq B.family.metric lambda x t := by
    rw [hm]
    exact c.map_curvatureSq_eq A B.family.metric lambda hlambda hc.smooth hc.immersed x t (hinterval ht)
  have hlenEq (p q : ℝ) : c.map.arcLength Bhat.family.metric p q u = c.arcLength B.family.metric lambda p q u := by
    change (∫ x in p..q, c.map.speed Bhat.family.metric x u) = ∫ x in p..q, c.speed B.family.metric lambda x u
    apply intervalIntegral.integral_congr
    intro x hx
    rw [hm]
    exact c.map_speed_eq A B.family.metric lambda hlambda hc.smooth x u (hinterval ⟨hsu.le, le_rfl⟩)
  have htcEq (p q : ℝ) : c.map.arcTotalCurvature Bhat.family.metric p q u = c.arcTotalCurvature B.family.metric lambda p q u := by
    change (∫ x in p..q, c.map.curvature Bhat.family.metric x u * c.map.speed Bhat.family.metric x u) =
      ∫ x in p..q, c.curvature B.family.metric lambda x u * c.speed B.family.metric lambda x u
    apply intervalIntegral.integral_congr
    intro x hx
    change Real.sqrt (c.map.curvatureSq Bhat.family.metric x u) * _ = _
    rw [hsq x u ⟨hsu.le, le_rfl⟩, hm,
      c.map_speed_eq A B.family.metric lambda hlambda hc.smooth x u (hinterval ⟨hsu.le, le_rfl⟩)]
    rfl
  have hC' : Bhat.C ≤ C := hBC.trans_le hC
  have hDR (x t : ℝ) (ht : t ∈ Icc s u) :
      DifferentialGeometry.Tensor0SBundle.normSq0S (Bhat.family.metric t) (c.map.lift x t) 5
        (DifferentialGeometry.Tensor0SBundle.totalNabla0SFun 4 (Bhat.family.connection t) (Bhat.family.rm04 t) (c.map.lift x t)) ≤ C ^ 2 := by
    rw [hfamily]
    exact (hprod lambda hlambda t (hwindow ht) (c.map.lift x t)).1
  have hDDRic (x t : ℝ) (ht : t ∈ Icc s u) :
      DifferentialGeometry.Tensor0SBundle.normSq0S (Bhat.family.metric t) (c.map.lift x t) 4
        (DifferentialGeometry.Tensor0SBundle.totalNabla0SFun 3 (Bhat.family.connection t)
          (DifferentialGeometry.CheegerGromovCompactness.covStep (Bhat.family.metric t) 2 (Bhat.family.ricci t)) (c.map.lift x t)) ≤ C ^ 2 := by
    rw [hfamily]
    exact (hprod lambda hlambda t (hwindow ht) (c.map.lift x t)).2
  obtain ⟨v, hv, heq, htc⟩ := c.map.exists_arcTotalCurvature_ge_of_curvatureSq_le_div Bhat hsu hwindow
    hsol C K hC' hK hlen (fun x t ht => by rw [hsq x t ⟨ht.1.le, ht.2⟩]; exact hk x t ht)
    hDR hDDRic hpq (by rwa [hlenEq]) (by rwa [hsq p u ⟨hsu.le, le_rfl⟩])
  exact ⟨v, hv, (hlenEq p v).symm.trans heq, (htcEq p v).symm ▸ htc⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
