import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.ChartDistanceDini

/-!
# Local smoothing of a distance function with a Lipschitz difference (LC28, tier T2)

`exists_local_distance_approximation`: let `Y` be closed and nonempty, `U` open and disjoint from
`Y`, and suppose the minimizing directions `V_q(Y)` have chordal diameter `< θ` at every `q ∈ U`.
For every `L > 2θ` and every `b ∈ U` there is an open, relatively compact `W ∋ b` inside `U` such
that for every `η > 0` some `f'`, smooth on `W`, satisfies `|f' - d_Y| ≤ η` on `W` and
`|(f' - d_Y) x - (f' - d_Y) x'| ≤ L dist x x'` for `x, x' ∈ W`.

Proof: in the chart `φ` at `b`, with `ℓ = -g_b(u₀, ·)` for a fixed `u₀ ∈ V_b(Y)`, the function
`h = d_Y ∘ φ.symm - ℓ` has right directional increments below `a N_b(w)` for any `a > θ`
(upper supports + upper semicontinuity of `V(Y)`), hence is `a`-Lipschitz for `N_b` on a
coordinate ball (tier T1). Mollify `h` (tier T1) and return `f' = (h' + ℓ) ∘ φ`; the chart
Lipschitz bound converts `2a N_b` into `2aκ · dist = L · dist`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Local smoothing of the distance to a closed set with a Lipschitz difference. -/
theorem exists_local_distance_approximation (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Y U : Set M} (hY : IsClosed Y) (hYne : Y.Nonempty)
    (hU : IsOpen U) (hUY : Disjoint U Y) {θ L : ℝ} (hθL : 2 * θ < L)
    (hdiam : ∀ q ∈ U, ∀ u ∈ minimizingDirectionsTo g hEnorm Y q,
      ∀ u' ∈ minimizingDirectionsTo g hEnorm Y q, Real.sqrt (g.inner q (u - u') (u - u')) < θ)
    {b : M} (hb : b ∈ U) :
    ∃ W : Set M, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ η > 0, ∃ f' : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f' W ∧
        (∀ x ∈ W, |f' x - Metric.infDist x Y| ≤ η) ∧
        ∀ x ∈ W, ∀ x' ∈ W, |(f' x - Metric.infDist x Y) - (f' x' - Metric.infDist x' Y)| ≤
          L * dist x x' := by
  have : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  have hpos : ∀ q ∈ U, 0 < Metric.infDist q Y := fun q hq =>
    (hY.notMem_iff_infDist_pos hYne).1 (Set.disjoint_left.mp hUY hq)
  obtain ⟨-, u₀, -, -, -, hu₀, -⟩ :=
    infDist_upper_support_of_isClosed g hEnorm hY hYne (hpos b hb)
  have hθpos : 0 < θ := by
    have := hdiam b hb u₀ hu₀ u₀ hu₀
    simpa using this
  set a : ℝ := (2 * θ + L) / 4 with ha
  have hθa : θ < a := by rw [ha]; linarith
  have hapos : 0 < a := hθpos.trans hθa
  set κ : ℝ := L / (2 * a) with hκ
  have hκ1 : 1 < κ := by
    rw [hκ, one_lt_div (by positivity)]
    rw [ha]; linarith
  have h2aκ : 2 * a * κ = L := by rw [hκ]; field_simp
  set N := metricSeminormAt g b with hN
  set φ := extChartAt I b with hφ
  set ℓ : E →L[ℝ] ℝ := -metricFormAt g b u₀ with hℓ
  -- upper semicontinuity of the minimizing directions at `b`
  have husc := eventually_minimizingDirectionsTo_chart_close g hEnorm hY b (u₀ := u₀) (a := a)
    (fun u hu => (hdiam b hb u hu u₀ hu₀).trans hθa)
  -- chart Lipschitz bound
  obtain ⟨r₁, hr₁, hr₁src, hchart⟩ := exists_ball_metricSeminormAt_chart_sub_le g hEnorm b hκ1
  -- the good set
  set A : Set M := {z | z ∈ U ∧ z ∈ (chartAt H b).source ∧
    ∀ u ∈ minimizingDirectionsTo g hEnorm Y z, ∀ w : E,
      |g.inner z u ((trivializationAt E (TangentSpace I) b).symmL ℝ z w) -
          metricFormAt g b u₀ w| ≤ a * N w} with hA
  have hAnhds : A ∈ 𝓝 b := by
    filter_upwards [hU.mem_nhds hb, (chartAt H b).open_source.mem_nhds (mem_chart_source H b),
      husc] with z h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hpre : φ.target ∩ φ.symm ⁻¹' A ∈ 𝓝 (φ b) :=
    inter_mem (extChartAt_target_mem_nhds b)
      ((continuousAt_extChartAt_symm b).preimage_mem_nhds (by rwa [extChartAt_to_inv]))
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhds_iff.mp hpre
  set B : Set E := Metric.ball (φ b) ρ₀ with hB
  let h : E → ℝ := fun y => Metric.infDist (φ.symm y) Y - ℓ y
  have hcont : ContinuousOn h B := by
    refine ContinuousOn.sub ?_ ℓ.continuous.continuousOn
    exact ((Metric.continuous_infDist_pt Y).comp_continuousOn (continuousOn_extChartAt_symm b)).mono
      (fun y hy => (hball hy).1)
  have hdini : ∀ y ∈ B, ∀ w : E, ∀ c, a * N w < c →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), h (y + t • w) - h y ≤ t * c := by
    intro y hy w c hc
    obtain ⟨hyt, hyA⟩ := hball hy
    set z := φ.symm y with hz
    have hφz : φ z = y := φ.right_inv hyt
    have hzsrc : z ∈ (chartAt H b).source := hyA.2.1
    have hev := eventually_infDist_chart_increment_le g hEnorm hY hYne b hzsrc (hpos z hyA.1) w
      (c := c + ℓ w) (by
        intro u hu
        have h1 := hyA.2.2 u hu w
        have h2 : ℓ w = -metricFormAt g b u₀ w := rfl
        rw [h2]
        have h3 := (abs_le.mp h1).1
        linarith)
    filter_upwards [hev] with t ht
    rw [hφz] at ht
    simp only [h, map_add, map_smul, smul_eq_mul]
    linarith
  have hlip := abs_sub_le_seminorm_of_eventually_increment_le N (convex_ball _ _) hcont hdini
  refine ⟨(chartAt H b).source ∩ φ ⁻¹' Metric.ball (φ b) (ρ₀ / 2) ∩ Metric.ball b r₁,
    ((isOpen_extChartAt_preimage b Metric.isOpen_ball).inter Metric.isOpen_ball),
    ⟨⟨mem_chart_source H b, Metric.mem_ball_self (by positivity)⟩, Metric.mem_ball_self hr₁⟩,
    ?_, ?_, ?_⟩
  · intro x hx
    have hxs : x ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx.1.1
    have hmem : φ x ∈ B := Metric.ball_subset_ball (by linarith) hx.1.2
    have := (hball hmem).2
    rw [Set.mem_preimage, φ.left_inv hxs] at this
    exact this.1
  · exact (isCompact_closedBall b r₁).of_isClosed_subset isClosed_closure
      ((closure_mono inter_subset_right).trans Metric.closure_ball_subset_closedBall)
  · intro η hη
    set C : ℝ := Real.sqrt ‖metricFormAt g b‖ with hC
    have hC0 : 0 ≤ C := Real.sqrt_nonneg _
    set r : ℝ := min (ρ₀ / 2) (η / (a * C + 1)) with hr
    have hrpos : 0 < r := lt_min (by positivity) (by positivity)
    have hδ : ∀ z : E, ‖z‖ ≤ r → N z ≤ C * r := fun z hz =>
      (metricSeminormAt_le_mul_norm g b z).trans (mul_le_mul_of_nonneg_left hz hC0)
    obtain ⟨h', hsmooth, hl, hv⟩ := exists_contDiff_seminorm_lipschitz_approx N
      (metricSeminormAt_le_mul_norm g b) hapos.le hlip hrpos hδ
    have haδ : a * (C * r) ≤ η := by
      have hr2 : r ≤ η / (a * C + 1) := min_le_right _ _
      have h1 : a * C * r ≤ a * C * (η / (a * C + 1)) :=
        mul_le_mul_of_nonneg_left hr2 (by positivity)
      have h2 : a * C * (η / (a * C + 1)) ≤ η := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith
    have hsub : ∀ x ∈ (chartAt H b).source ∩ φ ⁻¹' Metric.ball (φ b) (ρ₀ / 2) ∩
        Metric.ball b r₁, Metric.closedBall (φ x) r ⊆ B := by
      intro x hx y hy
      rw [Metric.mem_closedBall] at hy
      have h1 : dist (φ x) (φ b) < ρ₀ / 2 := hx.1.2
      have h2 : r ≤ ρ₀ / 2 := min_le_left _ _
      rw [hB, Metric.mem_ball]
      linarith [dist_triangle y (φ x) (φ b)]
    have hhx : ∀ x ∈ (chartAt H b).source, h (φ x) = Metric.infDist x Y - ℓ (φ x) := by
      intro x hx
      have hxs : x ∈ φ.source := by rw [hφ, extChartAt_source]; exact hx
      simp only [h, φ.left_inv hxs]
    refine ⟨fun x => h' (φ x) + ℓ (φ x), ?_, ?_, ?_⟩
    · have hs : ContDiff ℝ ∞ (fun y => h' y + ℓ y) := hsmooth.add ℓ.contDiff
      exact hs.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt.mono
        (fun x hx => hx.1.1))
    · intro x hx
      have := hv (φ x) (hsub x hx)
      rw [hhx x hx.1.1] at this
      calc |h' (φ x) + ℓ (φ x) - Metric.infDist x Y|
          = |h' (φ x) - (Metric.infDist x Y - ℓ (φ x))| := by ring_nf
        _ ≤ a * (C * r) := this
        _ ≤ η := haδ
    · intro x hx x' hx'
      have h1 := hl (φ x) (φ x') (hsub x hx) (hsub x' hx')
      have h2 := hlip (φ x) ((hsub x hx) (Metric.mem_closedBall_self hrpos.le))
        (φ x') ((hsub x' hx') (Metric.mem_closedBall_self hrpos.le))
      rw [hhx x hx.1.1, hhx x' hx'.1.1] at h2
      have h3 := hchart x' hx'.2 x hx.2
      rw [dist_comm x' x] at h3
      calc |(h' (φ x) + ℓ (φ x) - Metric.infDist x Y) -
            (h' (φ x') + ℓ (φ x') - Metric.infDist x' Y)|
          = |(h' (φ x) - h' (φ x')) -
              ((Metric.infDist x Y - ℓ (φ x)) - (Metric.infDist x' Y - ℓ (φ x')))| := by
            ring_nf
        _ ≤ |h' (φ x) - h' (φ x')| +
              |(Metric.infDist x Y - ℓ (φ x)) - (Metric.infDist x' Y - ℓ (φ x'))| := abs_sub _ _
        _ ≤ a * N (φ x - φ x') + a * N (φ x - φ x') := add_le_add h1 h2
        _ = 2 * a * N (φ x - φ x') := by ring
        _ ≤ 2 * a * (κ * dist x x') := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = L * dist x x' := by rw [← h2aκ]; ring

end DifferentialGeometry.Geometry.Collapse
