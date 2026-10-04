import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShapeTwo
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicSubmanifold
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.StrictConvexBall
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections

/-!
# The arc layer of the finite surface soul (S-SOUL2, arc case of S-SHAPE2)

If the last flag set `C` of the finite soul construction is an injective unit geodesic arc
`γ '' [0, ℓ]` (S-SHAPE2, arc case), the soul is its midpoint (review of the finite soul design, §3:
"the arc layer uses its unique direction to the midpoint"). This file proves:
* `exists_pos_eq_of_proj_geodesicFlow_eq_arc`: near any arc parameter `t_e ∈ [0, ℓ]`, the only arc
  parameter with the same point is `t_e` itself (local injectivity from a normal chart plus a
  compactness separation); hence `exists_pos_proj_geodesicFlow_notMem_arc` (A1): the geodesic
  leaves the arc immediately past either end;
* `arc_geodesic_eq` (A2): a geodesic starting at `γ t₀` that stays in `C` on `[0, T]`, `T > 0`, is
  `t ↦ γ (t₀ + c t)` with all parameters in `[0, ℓ]` (local collinearity of CMS-S + A1 + IVT);
* `finiteMinimizingDirectionsTo_arc` (A3): the minimizing direction from `γ t₀` to `γ t₁` is unique,
  `± γ'(t₀)` with the sign of `t₁ - t₀`;
* `isTotallyConvexFinite_singleton_arc` (A4): every point of the arc is a totally convex set;
* `exists_unit_strict_outward_arc` (A5): strict outward unit vectors off the chosen point.
No curvature hypothesis is used.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [NeZero (Module.finrank ℝ E)] in
/-- `γ (t₀ + s) = exp_{γ t₀} (s γ'(t₀))` along a geodesic of a complete metric. -/
theorem proj_geodesicFlow_add_eq_expMap_of_complete
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) (t₀ s : ℝ) :
    (g.geodesicFlow p (t₀ + s)).proj =
      g.expMap (⟨(g.geodesicFlow p t₀).proj, (s • ((g.geodesicFlow p t₀).snd : E) : E)⟩ :
        TangentBundle I M) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have h1 := g.expMap_smul_eq_proj_geodesicFlow hr1 (g.geodesicFlow p t₀).proj
    (g.geodesicFlow p t₀).snd s (by rw [hD]; exact mem_univ _)
  rw [g.geodesicFlow_add hr1 (by rw [hD]; exact mem_univ _) (by rw [hD]; exact mem_univ _)]
  exact h1.symm

omit [NeZero (Module.finrank ℝ E)] in
/-- **Local injectivity of a unit geodesic** (normal chart at `γ t₀`). -/
theorem exists_pos_injOn_proj_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} (hunit : g.inner p.proj p.snd p.snd = 1) (t₀ : ℝ) :
    ∃ ρ > 0, InjOn (fun t => (g.geodesicFlow p t).proj) (Ioo (t₀ - ρ) (t₀ + ρ)) := by
  obtain ⟨ρ, hρ, hch⟩ := g.exists_uniform_normal_charts hr hnorm
    (isCompact_singleton (x := (g.geodesicFlow p t₀).proj))
  obtain ⟨e, hsrc, -, hexp, -, -, -⟩ := hch _ rfl
  set x := (g.geodesicFlow p t₀).proj with hx
  set V : E := (g.geodesicFlow p t₀).snd with hV
  have hV1 : g.inner x V V = 1 := inner_snd_geodesicFlow_eq_one g hr hnorm hunit t₀
  have hV0 : (V : E) ≠ 0 := ne_zero_of_inner_self_eq_one g hV1
  have hmemS : ∀ t ∈ Ioo (t₀ - ρ) (t₀ + ρ), (t - t₀) • (V : E) ∈ e.source := by
    intro t ht
    rw [hsrc]
    change g.inner x ((t - t₀) • V) ((t - t₀) • V) < ρ ^ 2
    rw [inner_smul_smul_self_finite, hV1, mul_one]
    have h1 : |t - t₀| < ρ := abs_sub_lt_iff.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
    calc (t - t₀) ^ 2 = |t - t₀| ^ 2 := (sq_abs _).symm
      _ < ρ ^ 2 := by gcongr
  have heq : ∀ t ∈ Ioo (t₀ - ρ) (t₀ + ρ), (g.geodesicFlow p t).proj = e ((t - t₀) • (V : E)) := by
    intro t ht
    rw [(hexp _ (hmemS t ht)).2]
    have h := proj_geodesicFlow_add_eq_expMap_of_complete g hr hnorm p t₀ (t - t₀)
    rw [add_sub_cancel] at h
    exact h
  refine ⟨ρ, hρ, ?_⟩
  intro s hs t ht hst
  have h2 : e ((s - t₀) • (V : E)) = e ((t - t₀) • (V : E)) := by
    rw [← heq s hs, ← heq t ht]; exact hst
  have h3 := e.injOn (hmemS s hs) (hmemS t ht) h2
  have h4 : s - t₀ = t - t₀ := smul_left_injective ℝ hV0 h3
  linarith

omit [NeZero (Module.finrank ℝ E)] in
/-- Near an arc parameter `t_e ∈ [0, ℓ]` the only arc parameter with the same point is `t_e`'s
neighbour itself: `γ τ = γ θ`, `|τ - t_e| < ρ`, `θ ∈ [0, ℓ]` force `τ = θ`. -/
theorem exists_pos_eq_of_proj_geodesicFlow_eq_arc
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} (hunit : g.inner p.proj p.snd p.snd = 1)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Icc 0 ℓ)) {tₑ : ℝ} (htₑ : tₑ ∈ Icc 0 ℓ) :
    ∃ ρ > 0, ∀ τ, |τ - tₑ| < ρ → ∀ θ ∈ Icc 0 ℓ,
      (g.geodesicFlow p τ).proj = (g.geodesicFlow p θ).proj → τ = θ := by
  set γ : ℝ → M := fun t => (g.geodesicFlow p t).proj with hγ
  have hγc : Continuous γ := continuous_proj_geodesicFlow_of_unit g hr hnorm hunit
  obtain ⟨ρ₀, hρ₀, hloc⟩ := exists_pos_injOn_proj_geodesicFlow g hr hnorm hunit tₑ
  set K : Set ℝ := Icc 0 ℓ \ Ioo (tₑ - ρ₀ / 2) (tₑ + ρ₀ / 2) with hK
  have hKc : IsCompact (γ '' K) := (isCompact_Icc.diff isOpen_Ioo).image hγc
  have hnot : γ tₑ ∉ γ '' K := by
    rintro ⟨θ, hθ, hθe⟩
    have := hinj hθ.1 htₑ hθe
    exact hθ.2 ⟨by linarith, by linarith⟩
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.1 (hKc.isClosed.isOpen_compl.mem_nhds hnot)
  refine ⟨min η (ρ₀ / 2), lt_min hη (half_pos hρ₀), fun τ hτ θ hθ hτθ => ?_⟩
  have hτη : |τ - tₑ| < η := hτ.trans_le (min_le_left _ _)
  have hτρ : |τ - tₑ| < ρ₀ / 2 := hτ.trans_le (min_le_right _ _)
  have hdist : dist (γ θ) (γ tₑ) < η := by
    rw [show γ θ = γ τ from hτθ.symm]
    exact (dist_proj_geodesicFlow_le_of_unit g hr hnorm hunit τ tₑ).trans_lt
      (by rw [abs_sub_comm]; exact hτη)
  have hθK : θ ∉ K := fun hθK => hball hdist ⟨θ, hθK, rfl⟩
  have hθI : θ ∈ Ioo (tₑ - ρ₀ / 2) (tₑ + ρ₀ / 2) := by
    by_contra hc
    exact hθK ⟨hθ, hc⟩
  have hτI : τ ∈ Ioo (tₑ - ρ₀) (tₑ + ρ₀) := by
    have := abs_sub_lt_iff.1 hτρ
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  exact hloc hτI ⟨by linarith [hθI.1], by linarith [hθI.2]⟩ hτθ

omit [NeZero (Module.finrank ℝ E)] in
/-- **A1 (no extension).** An injective unit geodesic arc `γ '' [0, ℓ]` is left immediately past
either end. -/
theorem exists_pos_proj_geodesicFlow_notMem_arc
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hunit : g.inner p.proj p.snd p.snd = 1)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Icc 0 ℓ)) :
    ∃ ρ > 0, ∀ τ, (τ ∈ Ioo (-ρ) 0 ∨ τ ∈ Ioo ℓ (ℓ + ρ)) →
      (g.geodesicFlow p τ).proj ∉ (fun t => (g.geodesicFlow p t).proj) '' Icc 0 ℓ := by
  obtain ⟨ρ₁, hρ₁, h₁⟩ := exists_pos_eq_of_proj_geodesicFlow_eq_arc g hr hnorm hunit hinj
    (tₑ := 0) ⟨le_rfl, hℓ⟩
  obtain ⟨ρ₂, hρ₂, h₂⟩ := exists_pos_eq_of_proj_geodesicFlow_eq_arc g hr hnorm hunit hinj
    (tₑ := ℓ) ⟨hℓ, le_rfl⟩
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun τ hτ => ?_⟩
  rintro ⟨θ, hθ, hθτ⟩
  rcases hτ with hτ | hτ
  · have hab : |τ - 0| < ρ₁ := by
      rw [sub_zero, abs_of_neg hτ.2]; linarith [hτ.1, min_le_left ρ₁ ρ₂]
    have := h₁ τ hab θ hθ hθτ.symm
    linarith [hθ.1, hτ.2]
  · have hab : |τ - ℓ| < ρ₂ := by
      rw [abs_of_pos (by linarith [hτ.1])]; linarith [hτ.2, min_le_right ρ₁ ρ₂]
    have := h₂ τ hab θ hθ hθτ.symm
    linarith [hθ.2, hτ.1]

/-- **A2.** A geodesic starting at the arc point `γ t₀` and staying in the arc `C = γ '' [0, ℓ]`
(compact, totally convex, empty interior, in a surface) on `[0, T]`, `T > 0`, runs along the arc:
`ξ = c • γ'(t₀)` and `t ↦ γ (t₀ + c t)` with every parameter in `[0, ℓ]`. -/
theorem arc_geodesic_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCc : IsCompact C)
    (hconv : IsTotallyConvexFinite g C) (hint : interior C = ∅) {p : TangentBundle I M} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hunit : g.inner p.proj p.snd p.snd = 1)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Icc 0 ℓ))
    (hC : C = (fun t => (g.geodesicFlow p t).proj) '' Icc 0 ℓ) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 ℓ)
    (ξ : E) {T : ℝ} (hT : 0 < T)
    (hmem : ∀ t ∈ Icc 0 T,
      (g.geodesicFlow (⟨(g.geodesicFlow p t₀).proj, ξ⟩ : TangentBundle I M) t).proj ∈ C) :
    ∃ c : ℝ, ξ = c • ((g.geodesicFlow p t₀).snd : E) ∧ ∀ t ∈ Icc 0 T,
      t₀ + c * t ∈ Icc 0 ℓ ∧
        (g.geodesicFlow (⟨(g.geodesicFlow p t₀).proj, ξ⟩ : TangentBundle I M) t).proj =
          (g.geodesicFlow p (t₀ + c * t)).proj := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  set z := (g.geodesicFlow p t₀).proj with hz
  set V : E := (g.geodesicFlow p t₀).snd with hV
  have hV1 : g.inner z V V = 1 := inner_snd_geodesicFlow_eq_one g hr hnorm hunit t₀
  have hV0 : (V : E) ≠ 0 := ne_zero_of_inner_self_eq_one g hV1
  have hzC : z ∈ C := by rw [hC]; exact ⟨t₀, ht₀, rfl⟩
  have hflowE : ∀ (y : M) (v : E) (τ : ℝ), g.expMap (⟨y, τ • v⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨y, v⟩ : TangentBundle I M) τ).proj :=
    fun y v τ => g.expMap_smul_eq_proj_geodesicFlow hr1 y v τ (by rw [hD]; exact mem_univ _)
  -- Step 1: `ξ` is a multiple of `γ'(t₀)`.
  have hξ : ∃ c : ℝ, ξ = c • (V : E) := by
    rcases eq_or_ne ξ 0 with h0 | h0
    · exact ⟨0, by rw [h0, zero_smul]⟩
    obtain ⟨ρ, hρ, hch⟩ := exists_radius_not_linearIndependent_dim_two g hr hnorm hdim hCc hconv hint
    obtain ⟨e, hsrc, -, hexp, -, hlin⟩ := hch z hzC
    set N := g.inner z ξ ξ with hN
    have hN0 : 0 ≤ N := (g.pos z ξ h0).le
    set s₁ : ℝ := min T (ρ / (N + 1)) with hs₁
    have hs₁pos : 0 < s₁ := lt_min hT (div_pos hρ (by linarith))
    have hs₁T : s₁ ≤ T := min_le_left _ _
    have hs₁ρ : s₁ * (N + 1) ≤ ρ := by
      have := min_le_right T (ρ / (N + 1))
      rw [le_div_iff₀ (by linarith)] at this; exact this
    have hvS : s₁ • ξ ∈ e.source := by
      rw [hsrc]
      change g.inner z (s₁ • ξ) (s₁ • ξ) < ρ ^ 2
      rw [inner_smul_smul_self_finite]
      have h2 : s₁ ^ 2 * N < (s₁ * (N + 1)) ^ 2 := by nlinarith
      calc s₁ ^ 2 * N < (s₁ * (N + 1)) ^ 2 := h2
        _ ≤ ρ ^ 2 := by gcongr
    have hvC : e (s₁ • ξ) ∈ C := by
      rw [(hexp _ hvS).2, hflowE]
      exact hmem s₁ ⟨hs₁pos.le, hs₁T⟩
    obtain ⟨s₂, hs₂0, hs₂ρ, hs₂I⟩ : ∃ s₂ : ℝ, s₂ ≠ 0 ∧ s₂ ^ 2 < ρ ^ 2 ∧ t₀ + s₂ ∈ Icc 0 ℓ := by
      set a : ℝ := min (ρ / 2) (ℓ / 2) with ha
      have ha0 : 0 < a := lt_min (half_pos hρ) (half_pos hℓ)
      have haρ : a ^ 2 < ρ ^ 2 := by
        have : a ≤ ρ / 2 := min_le_left _ _
        nlinarith
      have haℓ : a ≤ ℓ / 2 := min_le_right _ _
      rcases le_or_gt t₀ (ℓ / 2) with h | h
      · exact ⟨a, ha0.ne', haρ, ⟨by linarith [ht₀.1], by linarith⟩⟩
      · exact ⟨-a, by linarith, by rw [neg_sq]; exact haρ, ⟨by linarith, by linarith [ht₀.2]⟩⟩
    have hwS : s₂ • (V : E) ∈ e.source := by
      rw [hsrc]
      change g.inner z (s₂ • V) (s₂ • V) < ρ ^ 2
      rw [inner_smul_smul_self_finite, hV1, mul_one]; exact hs₂ρ
    have hwC : e (s₂ • (V : E)) ∈ C := by
      have h := proj_geodesicFlow_add_eq_expMap_of_complete g hr hnorm p t₀ s₂
      have h' : g.expMap (⟨z, s₂ • V⟩ : TangentBundle I M) = (g.geodesicFlow p (t₀ + s₂)).proj :=
        h.symm
      rw [(hexp _ hwS).2, h', hC]
      exact ⟨t₀ + s₂, hs₂I, rfl⟩
    have hnli := hlin _ hvS _ hwS hvC hwC
    have hv0 : s₁ • ξ ≠ 0 := smul_ne_zero hs₁pos.ne' h0
    rw [LinearIndependent.pair_iff' hv0] at hnli
    simp only [not_forall, not_not] at hnli
    obtain ⟨a, ha⟩ := hnli
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact smul_ne_zero hs₂0 hV0 ha.symm
    refine ⟨a⁻¹ * s₂ / s₁, ?_⟩
    have h3 : ξ = s₁⁻¹ • a⁻¹ • (a • s₁ • ξ) := by
      rw [smul_smul a, smul_smul a⁻¹, smul_smul s₁⁻¹]
      field_simp
      rw [one_smul]
    rw [h3, ha, smul_smul, smul_smul]
    congr 1
    field_simp
  obtain ⟨c, hc⟩ := hξ
  -- Step 2: the geodesic runs along `γ`.
  have hflow : ∀ t, (g.geodesicFlow (⟨z, ξ⟩ : TangentBundle I M) t).proj =
      (g.geodesicFlow p (t₀ + c * t)).proj := by
    intro t
    rw [hc]
    exact proj_geodesicFlow_smul_snd g hr hnorm p t₀ c t
  refine ⟨c, hc, fun t ht => ⟨?_, hflow t⟩⟩
  -- Step 3: the parameters stay in `[0, ℓ]`.
  obtain ⟨ρ, hρ, hout⟩ := exists_pos_proj_geodesicFlow_notMem_arc g hr hnorm hℓ.le hunit hinj
  have hcont : ContinuousOn (fun s : ℝ => t₀ + c * s) (Icc 0 t) := by fun_prop
  have hmemT : ∀ s ∈ Icc 0 t, (g.geodesicFlow p (t₀ + c * s)).proj ∈
      (fun t => (g.geodesicFlow p t).proj) '' Icc 0 ℓ := fun s hs => by
    rw [← hC, ← hflow s]
    exact hmem s ⟨hs.1, hs.2.trans ht.2⟩
  constructor
  · by_contra hlow'
    have hlow := lt_of_not_ge hlow'
    set y : ℝ := max (t₀ + c * t) (-(ρ / 2)) with hy
    have hyI : y ∈ Icc (t₀ + c * t) (t₀ + c * 0) := by
      refine ⟨le_max_left _ _, ?_⟩
      rw [mul_zero, add_zero]
      exact max_le (by linarith [ht₀.1]) (by linarith [ht₀.1])
    obtain ⟨s, hs, hsy⟩ := intermediate_value_Icc' ht.1 hcont hyI
    have hyI' : y ∈ Ioo (-ρ) 0 :=
      ⟨by have := le_max_right (t₀ + c * t) (-(ρ / 2)); linarith, max_lt hlow (by linarith)⟩
    have h := hmemT s hs
    simp only at hsy
    rw [hsy] at h
    exact hout y (Or.inl hyI') h
  · by_contra hhigh'
    have hhigh := lt_of_not_ge hhigh'
    set y : ℝ := min (t₀ + c * t) (ℓ + ρ / 2) with hy
    have hyI : y ∈ Icc (t₀ + c * 0) (t₀ + c * t) := by
      refine ⟨?_, min_le_left _ _⟩
      rw [mul_zero, add_zero]
      exact le_min (by linarith [ht₀.2]) (by linarith [ht₀.2])
    obtain ⟨s, hs, hsy⟩ := intermediate_value_Icc ht.1 hcont hyI
    have hyI' : y ∈ Ioo ℓ (ℓ + ρ) :=
      ⟨lt_min hhigh (by linarith), by have := min_le_right (t₀ + c * t) (ℓ + ρ / 2); linarith⟩
    have h := hmemT s hs
    simp only at hsy
    rw [hsy] at h
    exact hout y (Or.inr hyI') h

/-- **A3 (unique direction).** The minimizing directions from the arc point `γ t₀` to the arc
point `γ t₁ ≠ γ t₀` consist of the single vector `± γ'(t₀)`, with the sign of `t₁ - t₀`. -/
theorem finiteMinimizingDirectionsTo_arc
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCc : IsCompact C)
    (hconv : IsTotallyConvexFinite g C) (hint : interior C = ∅) {p : TangentBundle I M} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hunit : g.inner p.proj p.snd p.snd = 1)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Icc 0 ℓ))
    (hC : C = (fun t => (g.geodesicFlow p t).proj) '' Icc 0 ℓ) {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Icc 0 ℓ)
    (ht₁ : t₁ ∈ Icc 0 ℓ) (hne : t₀ ≠ t₁) :
    ∀ u ∈ g.finiteMinimizingDirectionsTo {(g.geodesicFlow p t₁).proj} (g.geodesicFlow p t₀).proj,
      (u : E) = (if t₀ < t₁ then (1 : ℝ) else -1) • ((g.geodesicFlow p t₀).snd : E) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hflowE : ∀ (y : M) (v : E) (τ : ℝ), g.expMap (⟨y, τ • v⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨y, v⟩ : TangentBundle I M) τ).proj :=
    fun y v τ => g.expMap_smul_eq_proj_geodesicFlow hr1 y v τ (by rw [hD]; exact mem_univ _)
  set z := (g.geodesicFlow p t₀).proj with hz
  set V : E := (g.geodesicFlow p t₀).snd with hV
  intro u hu
  obtain ⟨hu1, hend⟩ := hu
  have hV1 : g.inner z V V = 1 := inner_snd_geodesicFlow_eq_one g hr hnorm hunit t₀
  have hzC : z ∈ C := by rw [hC]; exact ⟨t₀, ht₀, rfl⟩
  have hz1 : (g.geodesicFlow p t₁).proj ∈ C := by rw [hC]; exact ⟨t₁, ht₁, rfl⟩
  rw [infDist_singleton] at hend
  set d := dist z (g.geodesicFlow p t₁).proj with hd
  have hd0 : 0 < d := dist_pos.2 fun h => hne (hinj ht₀ ht₁ h)
  have hendEq : g.expMap (⟨z, d • (u : E)⟩ : TangentBundle I M) = (g.geodesicFlow p t₁).proj := hend
  have hseg := hconv.expMap_mem (u := (u : E)) hr hnorm hd0.le hzC
    (by have h := hz1; rw [← hendEq] at h; exact h)
  obtain ⟨c, hc, hpar⟩ := arc_geodesic_eq g hr hnorm hdim hCc hconv hint hℓ hunit hinj hC ht₀ (u : E)
    hd0 fun t ht => (congrArg (· ∈ C) (hflowE z u t)).mp (hseg t ht)
  rw [← hV] at hc
  obtain ⟨hdI, hdeq⟩ := hpar d ⟨hd0.le, le_rfl⟩
  have h1 : (g.geodesicFlow p (t₀ + c * d)).proj = (g.geodesicFlow p t₁).proj := by
    rw [← hdeq]; exact (hflowE z u d).symm.trans hendEq
  have h2 : t₀ + c * d = t₁ := hinj hdI ht₁ h1
  have hc2 : c ^ 2 = 1 := by
    have h3 : g.inner z (u : E) (u : E) = 1 := hu1
    rw [hc] at h3
    have h5 : c ^ 2 * g.inner z V V = 1 := (inner_smul_smul_self_finite g z c V).symm.trans h3
    rwa [hV1, mul_one] at h5
  rw [hc]
  congr 1
  split_ifs with hlt
  · have hcpos : 0 < c := by
      by_contra hcn
      have : c * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hcn) hd0.le
      linarith
    nlinarith
  · have hlt' : t₁ < t₀ := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    have hcneg : c < 0 := by
      by_contra hcn
      have : 0 ≤ c * d := mul_nonneg (le_of_not_gt hcn) hd0.le
      linarith
    nlinarith

/-- **A4.** Every point of the arc is a totally convex set: a geodesic arc from `γ t₀` back to
`γ t₀` inside the arc is constant. -/
theorem isTotallyConvexFinite_singleton_arc
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCc : IsCompact C)
    (hconv : IsTotallyConvexFinite g C) (hint : interior C = ∅) {p : TangentBundle I M} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hunit : g.inner p.proj p.snd p.snd = 1)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Icc 0 ℓ))
    (hC : C = (fun t => (g.geodesicFlow p t).proj) '' Icc 0 ℓ) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 ℓ) :
    IsTotallyConvexFinite g {(g.geodesicFlow p t₀).proj} := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hzC : (g.geodesicFlow p t₀).proj ∈ C := by rw [hC]; exact ⟨t₀, ht₀, rfl⟩
  intro P L hL hP0 hPL t ht
  rcases hL.eq_or_lt with hL0 | hLpos
  · subst hL0
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    rw [ht0, g.geodesicFlow_zero hr1]
    exact hP0
  obtain ⟨x, ξ⟩ := P
  have hx : x = (g.geodesicFlow p t₀).proj := hP0
  subst hx
  have hmem : ∀ τ ∈ Icc 0 L,
      (g.geodesicFlow (⟨(g.geodesicFlow p t₀).proj, ξ⟩ : TangentBundle I M) τ).proj ∈ C :=
    hconv _ L hL hzC (by rw [mem_singleton_iff.1 hPL]; exact hzC)
  obtain ⟨c, -, hpar⟩ := arc_geodesic_eq g hr hnorm hdim hCc hconv hint hℓ hunit hinj hC ht₀ ξ
    hLpos hmem
  obtain ⟨hLI, hLeq⟩ := hpar L ⟨hL, le_rfl⟩
  have h1 : (g.geodesicFlow p (t₀ + c * L)).proj = (g.geodesicFlow p t₀).proj := by
    rw [← hLeq]; exact hPL
  have h2 : t₀ + c * L = t₀ := hinj hLI ht₀ h1
  have hc0 : c = 0 := by
    have : c * L = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hLpos.ne'
  rw [(hpar t ht).2, hc0, zero_mul, add_zero]
  exact mem_singleton _

/-- **A5 (strict outward on the arc).** At an arc point `γ t₀ ≠ γ t₁`, the vector `∓ γ'(t₀)`
pointing away from `γ t₁` is a unit vector with negative pairing against every minimizing
direction to `γ t₁`. -/
theorem exists_unit_strict_outward_arc
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCc : IsCompact C)
    (hconv : IsTotallyConvexFinite g C) (hint : interior C = ∅) {p : TangentBundle I M} {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hunit : g.inner p.proj p.snd p.snd = 1)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Icc 0 ℓ))
    (hC : C = (fun t => (g.geodesicFlow p t).proj) '' Icc 0 ℓ) {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Icc 0 ℓ)
    (ht₁ : t₁ ∈ Icc 0 ℓ) (hne : t₀ ≠ t₁) :
    ∃ v : E, g.inner (g.geodesicFlow p t₀).proj v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo {(g.geodesicFlow p t₁).proj} (g.geodesicFlow p t₀).proj,
        g.inner (g.geodesicFlow p t₀).proj v u < 0 := by
  set z := (g.geodesicFlow p t₀).proj with hz
  set V : E := (g.geodesicFlow p t₀).snd with hV
  have hV1 : g.inner z V V = 1 := inner_snd_geodesicFlow_eq_one g hr hnorm hunit t₀
  set ε : ℝ := if t₀ < t₁ then (1 : ℝ) else -1 with hε
  have hε2 : ε ^ 2 = 1 := by rw [hε]; split_ifs <;> norm_num
  have hdir := finiteMinimizingDirectionsTo_arc g hr hnorm hdim hCc hconv hint hℓ hunit hinj hC
    ht₀ ht₁ hne
  have hneg : ∀ w : E, g.inner z (-w) w = -g.inner z w w := fun w => by
    have h1 : g.inner z (-w) = -g.inner z w := (g.inner z).map_neg w
    rw [h1]
    rfl
  refine ⟨(-ε) • V, ?_, fun u hu => ?_⟩
  · have h5 := inner_smul_smul_self_finite g z (-ε) V
    rw [hV1, mul_one, neg_sq, hε2] at h5
    exact h5
  · have hu' : (u : E) = ε • V := hdir u hu
    have h6 : g.inner z ((-ε) • V) (ε • V) = -1 := by
      have h7 : (-ε) • V = -(ε • V) := neg_smul ε V
      rw [h7]
      have h8 := (hneg (ε • V)).trans (congrArg Neg.neg (inner_smul_smul_self_finite g z ε V))
      rw [hV1, mul_one, hε2] at h8
      exact h8
    rw [hu']
    exact lt_of_eq_of_lt h6 (by norm_num)

end DifferentialGeometry.Geometry.FiniteSoul
