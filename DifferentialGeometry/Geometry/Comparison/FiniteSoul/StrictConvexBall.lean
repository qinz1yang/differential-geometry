import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SquaredDistanceChart
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SecondSlotDerivative
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SpeedBound
import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSprayFiniteRegularity
import Mathlib.Analysis.Convex.Deriv

/-!
# Strictly convex balls of a complete finite metric (S-CVX, finite CG 2.3)

For a complete metric `g` of class `C^{r+1}` (`2 ≤ r`) whose length distance is the ambient
distance (`hnorm`):

* `exists_ball_deriv2_sq_dist_pos`: around every `x₀` there is `δ > 0` such that for `x` and a
  point `γ t` of a unit-speed geodesic both in `ball x₀ δ`, the second derivative of
  `s ↦ d(x, γ s)²` at `t` is positive. Route: in the chart at `x₀` the squared distance is `C²`
  near the diagonal (`exists_contDiffOn_sq_dist_chart`); along the chart geodesic equation the
  second derivative is `Θ((a, β), β') = D²_b Q(β', β') + D_b Q(spray₂(β, β'))`, continuous and
  quadratic in `β'`; on the diagonal it equals `2 g(ξ, ξ)` (radial geodesic, where
  `d(x₀, exp(sξ))² = s² g(ξ, ξ)`), so it is positive nearby (compactness of the unit sphere).
* `exists_strictConvex_radius` (frozen interface): on a compact set there is a uniform radius `ρ`
  below which `t ↦ d(x, σ t)²` is strictly convex along every unit geodesic arc of length `≤ 2ρ`
  with endpoints in `closedBall x ρ`, and the arc stays in that ball.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  {r : ℕ∞}

local instance : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

/-- Unit-speed geodesics of a complete finite metric are `1`-Lipschitz. -/
theorem dist_proj_geodesicFlow_le_of_unit
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} (hp : g.inner p.proj p.snd p.snd = 1) (s t : ℝ) :
    dist (g.geodesicFlow p s).proj (g.geodesicFlow p t).proj ≤ |t - s| := by
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have h := g.dist_proj_geodesicFlow_le (one_le_two.trans hr) hnorm (p := p) (s := s) (t := t)
    (fun τ _ => by rw [hD]; exact mem_univ _)
  rwa [hp, Real.sqrt_one, one_mul] at h

theorem continuous_proj_geodesicFlow_of_unit
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} (hp : g.inner p.proj p.snd p.snd = 1) :
    Continuous (fun s => (g.geodesicFlow p s).proj) := by
  refine Metric.continuous_iff.2 fun b ε hε => ⟨ε, hε, fun a hab => ?_⟩
  refine (dist_proj_geodesicFlow_le_of_unit g hr hnorm hp a b).trans_lt ?_
  rw [abs_sub_comm, ← Real.dist_eq]
  exact hab

/-- **Local positivity of the second derivative of the squared distance along geodesics.** -/
theorem exists_ball_deriv2_sq_dist_pos
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (x₀ : M) :
    ∃ δ > 0, ∀ x ∈ ball x₀ δ, ∀ p : TangentBundle I M, g.inner p.proj p.snd p.snd = 1 →
      ∀ t : ℝ, (g.geodesicFlow p t).proj ∈ ball x₀ δ →
        0 < deriv^[2] (fun s => dist x (g.geodesicFlow p s).proj ^ 2) t := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hmem : ∀ (P : TangentBundle I M) (τ : ℝ), (P, τ) ∈ g.geodesicFlowDomain := fun P τ => by
    rw [hD]; exact mem_univ _
  set κ := extChartAt I x₀ with hκ
  set T := extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I M) with hT
  obtain ⟨U, hUo, hU₀, -, hQ⟩ := exists_contDiffOn_sq_dist_chart g hr hnorm x₀
  set Q : E × E → ℝ := fun z => dist (κ.symm z.1) (κ.symm z.2) ^ 2 with hQdef
  set a₀ : E := κ x₀ with ha₀
  set G := g.chartInner x₀ with hG
  set V : E × E → E × E := DifferentialGeometry.MetricKoszul.metricSpray G with hVdef
  set Θ : (E × E) × E → ℝ := fun w =>
    secondSlotDeriv2 Q w.1 w.2 w.2 + secondSlotDeriv Q w.1 (V (w.1.2, w.2)).2 with hΘ
  -- the chart equation of the geodesic flow
  have hZ : ∀ (P : TangentBundle I M) (τ : ℝ), (g.geodesicFlow P τ).proj ∈ (chartAt H x₀).source →
      HasDerivAt (fun s => T (g.geodesicFlow P s)) (V (T (g.geodesicFlow P τ))) τ :=
    fun P τ h => g.hasDerivAt_geodesicFlow_chart hr1 (hmem P τ) (⟨x₀, 0⟩ : TangentBundle I M) h
  have hV1 : ∀ w : E × E, (V w).1 = w.2 := fun _ => rfl
  have hZ1 : ∀ (P : TangentBundle I M) (τ : ℝ),
      (T (g.geodesicFlow P τ)).1 = κ (g.geodesicFlow P τ).proj := fun _ _ =>
    TangentBundle.extChartAt_tangent_apply_fst _
  have hZ2 : ∀ (P : TangentBundle I M) (τ : ℝ),
      (g.geodesicFlow P τ).proj ∈ (chartAt H x₀).source →
      (T (g.geodesicFlow P τ)).2 =
        mfderiv I 𝓘(ℝ, E) κ (g.geodesicFlow P τ).proj (g.geodesicFlow P τ).snd :=
    fun P τ h => congrArg Prod.snd
      (Bundle.ContMDiffRiemannianMetric.extChartAt_tangent_mk x₀ h (g.geodesicFlow P τ).snd)
  -- continuity of `Θ` at the diagonal point
  have hU₀' : ((a₀, a₀) : E × E) ∈ U := hU₀
  have hQ₀ : ContDiffAt ℝ 2 Q (a₀, a₀) := hQ.contDiffAt (hUo.mem_nhds hU₀')
  have hr01 : (0 : WithTop ℕ∞) + 1 ≤ r := by
    rw [zero_add]
    exact_mod_cast hr1
  have hVc : ContinuousOn V (κ.target ×ˢ univ) :=
    (DifferentialGeometry.MetricKoszul.metricSpray_contDiffOn_succ (n := 0)
      (isOpen_extChartAt_target x₀) ((g.contDiffOn_chartInner x₀).of_le hr01)
      (fun y hy => g.isCoercive_chartInner x₀ hy)).continuousOn
  have hΘc : ∀ ξ : E, ContinuousAt Θ (((a₀, a₀) : E × E), ξ) := by
    intro ξ
    have hD2 : ContinuousAt (secondSlotDeriv2 Q) (a₀, a₀) :=
      continuousAt_secondSlotDeriv2 hUo hQ hU₀'
    have hD1 : ContinuousAt (secondSlotDeriv Q) (a₀, a₀) := continuousAt_secondSlotDeriv hQ₀
    have hVat : ContinuousAt V (a₀, ξ) :=
      hVc.continuousAt (prod_mem_nhds ((isOpen_extChartAt_target x₀).mem_nhds
        (mem_extChartAt_target x₀)) univ_mem)
    have hm : ContinuousAt (fun w : (E × E) × E => ((w.1.2, w.2) : E × E))
        (((a₀, a₀) : E × E), ξ) :=
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd).continuousAt
    have hVξ : ContinuousAt (fun w : (E × E) × E => (V (w.1.2, w.2)).2)
        (((a₀, a₀) : E × E), ξ) :=
      continuous_snd.continuousAt.comp (ContinuousAt.comp (g := V) hVat hm)
    have hfst : ContinuousAt (fun w : (E × E) × E => w.1) (((a₀, a₀) : E × E), ξ) :=
      continuousAt_fst
    have h1 : ContinuousAt (fun w : (E × E) × E => secondSlotDeriv2 Q w.1 w.2 w.2)
        (((a₀, a₀) : E × E), ξ) :=
      ((ContinuousAt.comp (g := secondSlotDeriv2 Q) (f := fun w : (E × E) × E => w.1)
        (x := (((a₀, a₀) : E × E), ξ)) hD2 hfst).clm_apply continuousAt_snd).clm_apply
        continuousAt_snd
    have h2 : ContinuousAt (fun w : (E × E) × E => secondSlotDeriv Q w.1 (V (w.1.2, w.2)).2)
        (((a₀, a₀) : E × E), ξ) :=
      (ContinuousAt.comp (g := secondSlotDeriv Q) (f := fun w : (E × E) × E => w.1)
        (x := (((a₀, a₀) : E × E), ξ)) hD1 hfst).clm_apply hVξ
    exact h1.add h2
  -- the value on the diagonal (radial geodesics from `x₀`)
  obtain ⟨ρ, hρ, hch⟩ := g.exists_uniform_normal_charts hr hnorm (isCompact_singleton (x := x₀))
  obtain ⟨e, hesrc, -, hexp, -, -, hdist⟩ := hch x₀ rfl
  have hbase : ∀ ξ : E, Θ (((a₀, a₀) : E × E), ξ) = 2 * g.inner x₀ ξ ξ := by
    intro ξ
    set P : TangentBundle I M := ⟨x₀, ξ⟩ with hP
    set c : ℝ := g.inner x₀ ξ ξ with hc
    set Z : ℝ → E × E := fun s => T (g.geodesicFlow P s) with hZdef
    have hγ : ∀ s, (g.geodesicFlow P s).proj = g.expMap (⟨x₀, s • ξ⟩ : TangentBundle I M) :=
      fun s => (g.expMap_smul_eq_proj_geodesicFlow hr1 x₀ ξ s (hmem _ _)).symm
    have hγc : Continuous (fun s => (g.geodesicFlow P s).proj) := by
      have h := (g.contMDiffOn_geodesicFlow hr1).continuousOn
      rw [hD] at h
      exact (FiberBundle.continuous_proj E (TangentSpace I)).comp
        ((continuousOn_univ.mp h).comp (continuous_const.prodMk continuous_id))
    have hγ0 : (g.geodesicFlow P 0).proj = x₀ := by rw [g.geodesicFlow_zero hr1]
    have hZ0 : Z 0 = ((a₀, ξ) : E × E) := by
      change T (g.geodesicFlow P 0) = _
      rw [g.geodesicFlow_zero hr1, hP, hT,
        Bundle.ContMDiffRiemannianMetric.extChartAt_tangent_mk x₀ (mem_chart_source H x₀) ξ,
        mfderiv_extChartAt_self]
      rfl
    -- near `0` the curve is in the chart and in the normal ball
    have hev1 : ∀ᶠ s in 𝓝 (0 : ℝ), (g.geodesicFlow P s).proj ∈ κ.source := by
      refine hγc.continuousAt.preimage_mem_nhds ?_
      rw [hγ0]
      exact extChartAt_source_mem_nhds x₀
    have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ), ((a₀, (Z s).1) : E × E) ∈ U := by
      have hcont : ContinuousAt (fun s => ((a₀, κ (g.geodesicFlow P s).proj) : E × E)) 0 := by
        refine continuousAt_const.prodMk ?_
        refine ContinuousAt.comp (g := κ) ?_ hγc.continuousAt
        rw [hγ0]
        exact continuousAt_extChartAt x₀
      have h := hcont.preimage_mem_nhds (hUo.mem_nhds (by
        rw [hγ0]
        exact hU₀'))
      filter_upwards [h] with s hs
      change ((a₀, (T (g.geodesicFlow P s)).1) : E × E) ∈ U
      rw [hZ1]
      exact hs
    have hev3 : ∀ᶠ s in 𝓝 (0 : ℝ), c * s ^ 2 < ρ ^ 2 := by
      have hcont : ContinuousAt (fun s : ℝ => c * s ^ 2) 0 := by fun_prop
      exact hcont.eventually (gt_mem_nhds (by simp only [ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero]; positivity))
    -- the squared distance is `c s²` near `0`
    have hfeq : ∀ᶠ s in 𝓝 (0 : ℝ), Q (a₀, (Z s).1) = c * s ^ 2 := by
      filter_upwards [hev1, hev3] with s hs1 hs3
      change dist (κ.symm a₀) (κ.symm (T (g.geodesicFlow P s)).1) ^ 2 = c * s ^ 2
      rw [hZ1, κ.left_inv hs1, ha₀, κ.left_inv (mem_extChartAt_source x₀), hγ s]
      have hin : g.inner x₀ (s • ξ) (s • ξ) = c * s ^ 2 :=
        (Bundle.ContMDiffRiemannianMetric.inner_smul_self_smul g x₀ s ξ).trans (by rw [hc]; ring)
      have hse : s • ξ ∈ e.source := by
        rw [hesrc]
        change g.inner x₀ (s • ξ) (s • ξ) < ρ ^ 2
        rw [hin]
        exact hs3
      have hd := hdist _ hse
      rw [(hexp _ hse).2] at hd
      rw [hd]
      exact (Real.sq_sqrt (g.inner_self_nonneg' x₀ _)).trans hin
    -- first derivatives near `0`
    set h : ℝ → ℝ := fun s => secondSlotDeriv Q (a₀, (Z s).1) (Z s).2 with hh
    have hheq : ∀ᶠ s in 𝓝 (0 : ℝ), h s = 2 * c * s := by
      filter_upwards [hev1, hev2, hfeq.eventually_nhds] with s hs1 hs2 hs3
      have hsc : (g.geodesicFlow P s).proj ∈ (chartAt H x₀).source := by
        rwa [hκ, extChartAt_source] at hs1
      have h1 := hasDerivAt_comp_secondSlot (hQ.contDiffAt (hUo.mem_nhds hs2)) (hZ P s hsc)
        (hV1 _)
      have h2 : HasDerivAt (fun s => Q (a₀, (Z s).1)) (2 * c * s) s := by
        have h3 : HasDerivAt (fun s : ℝ => c * s ^ 2) (2 * c * s) s := by
          have := (hasDerivAt_pow 2 s).const_mul c
          convert this using 1
          push_cast
          ring
        exact h3.congr_of_eventuallyEq hs3
      exact h1.unique h2
    have hsc0 : (g.geodesicFlow P 0).proj ∈ (chartAt H x₀).source := by
      rw [hγ0]; exact mem_chart_source H x₀
    have hU0 : ((a₀, (Z 0).1) : E × E) ∈ U := hev2.self_of_nhds
    have hd2 := hasDerivAt_secondSlotDeriv_comp (hQ.contDiffAt (hUo.mem_nhds hU0)) (hZ P 0 hsc0)
      (hV1 _)
    have hd2' : HasDerivAt h (2 * c) 0 := by
      have h3 : HasDerivAt (fun s : ℝ => 2 * c * s) (2 * c) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * c)
      exact h3.congr_of_eventuallyEq hheq
    have huniq := hd2.unique hd2'
    have hval : Θ (((a₀, (Z 0).1) : E × E), (Z 0).2) = 2 * c := huniq
    rw [hZ0] at hval
    exact hval
  -- homogeneity in the direction
  have hhom : ∀ (z : E × E) (ξ : E) (s : ℝ), Θ (z, s • ξ) = s ^ 2 * Θ (z, ξ) := by
    intro z ξ s
    have hVs : V (z.2, s • ξ) = (s • (V (z.2, ξ)).1, (s * s) • (V (z.2, ξ)).2) :=
      DifferentialGeometry.MetricKoszul.metricSpray_smul_snd G z.2 ξ s
    change secondSlotDeriv2 Q z (s • ξ) (s • ξ) + secondSlotDeriv Q z (V (z.2, s • ξ)).2 =
      s ^ 2 * (secondSlotDeriv2 Q z ξ ξ + secondSlotDeriv Q z (V (z.2, ξ)).2)
    rw [hVs]
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  -- positivity on a neighbourhood of the diagonal point
  have htube : ∀ᶠ z in 𝓝 ((a₀, a₀) : E × E), ∀ ξ ∈ sphere (0 : E) 1, 0 < Θ (z, ξ) := by
    refine (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually fun ξ hξ => ?_
    have hξ0 : ξ ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hξ
      exact zero_ne_one hξ
    have hpos : 0 < Θ (((a₀, a₀) : E × E), ξ) := by
      rw [hbase]
      have := g.pos x₀ ξ hξ0
      linarith
    exact (hΘc ξ).eventually (lt_mem_nhds hpos)
  have hposΘ : ∀ z : E × E, (∀ ξ ∈ sphere (0 : E) 1, 0 < Θ (z, ξ)) →
      ∀ ξ : E, ξ ≠ 0 → 0 < Θ (z, ξ) := by
    intro z hz ξ hξ
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hunit : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hsplit : ξ = ‖ξ‖ • (‖ξ‖⁻¹ • ξ) := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [hsplit, hhom]
    exact mul_pos (pow_pos hn 2) (hz _ hunit)
  -- the radius
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (inter_mem htube (hUo.mem_nhds hU₀'))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (extChartAt_source_mem_nhds
    (I := I) x₀) ((continuousAt_extChartAt (I := I) x₀).preimage_mem_nhds (ball_mem_nhds a₀ hε)))
  refine ⟨δ, hδ, fun x hx P hP t ht => ?_⟩
  set γ : ℝ → M := fun s => (g.geodesicFlow P s).proj with hγ
  set Z : ℝ → E × E := fun s => T (g.geodesicFlow P s) with hZdef
  set a : E := κ x with ha
  obtain ⟨hxs, hxa⟩ := hδsub hx
  have hγc : Continuous γ := continuous_proj_geodesicFlow_of_unit g hr hnorm hP
  have hgood : ∀ s, γ s ∈ ball x₀ δ → ((a, (Z s).1) : E × E) ∈ U ∧
      (∀ ξ ∈ sphere (0 : E) 1, 0 < Θ (((a, (Z s).1) : E × E), ξ)) ∧ γ s ∈ κ.source ∧
      γ s ∈ (chartAt H x₀).source := by
    intro s hs
    obtain ⟨hss, hsa⟩ := hδsub hs
    have hZs : (Z s).1 = κ (γ s) := hZ1 P s
    have hmb : ((a, (Z s).1) : E × E) ∈ ball ((a₀, a₀) : E × E) ε := by
      rw [hZs, mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨hxa, hsa⟩
    have hW := hεW hmb
    refine ⟨hW.2, hW.1, hss, ?_⟩
    rwa [extChartAt_source] at hss
  have hfeq : ∀ s, γ s ∈ κ.source → dist x (γ s) ^ 2 = Q (a, (Z s).1) := by
    intro s hs
    change dist x (γ s) ^ 2 = dist (κ.symm (κ x)) (κ.symm (T (g.geodesicFlow P s)).1) ^ 2
    rw [hZ1, κ.left_inv hxs]
    change dist x (γ s) ^ 2 = dist x (κ.symm (κ (γ s))) ^ 2
    rw [κ.left_inv hs]
  have hderiv : ∀ s, γ s ∈ ball x₀ δ →
      HasDerivAt (fun s => dist x (γ s) ^ 2) (secondSlotDeriv Q (a, (Z s).1) (Z s).2) s := by
    intro s hs
    obtain ⟨hU', -, hss, hsc⟩ := hgood s hs
    have h := hasDerivAt_comp_secondSlot (hQ.contDiffAt (hUo.mem_nhds hU')) (hZ P s hsc) (hV1 _)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hγc.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) x₀).mem_nhds hss)] with s' hs'
    exact hfeq s' hs'
  have hnear : ∀ᶠ s in 𝓝 t, γ s ∈ ball x₀ δ :=
    hγc.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds ht)
  have hd2 : deriv^[2] (fun s => dist x (γ s) ^ 2) t = Θ (((a, (Z t).1) : E × E), (Z t).2) := by
    have hev : deriv (fun s => dist x (γ s) ^ 2) =ᶠ[𝓝 t]
        fun s => secondSlotDeriv Q (a, (Z s).1) (Z s).2 := by
      filter_upwards [hnear] with s hs
      exact (hderiv s hs).deriv
    obtain ⟨hU', -, -, hsc⟩ := hgood t ht
    have h2 := hasDerivAt_secondSlotDeriv_comp (hQ.contDiffAt (hUo.mem_nhds hU')) (hZ P t hsc)
      (hV1 _)
    change deriv (deriv (fun s => dist x (γ s) ^ 2)) t = _
    rw [hev.deriv_eq]
    exact h2.deriv
  change 0 < deriv^[2] (fun s => dist x (γ s) ^ 2) t
  rw [hd2]
  obtain ⟨-, htube', hss, hsc⟩ := hgood t ht
  refine hposΘ _ htube' _ ?_
  intro h0
  have hsnd : g.inner (γ t) (g.geodesicFlow P t).snd (g.geodesicFlow P t).snd = 1 :=
    (g.inner_geodesicFlow_eq hr1 P t (hmem P t)).trans hP
  rw [hZdef] at h0
  change (T (g.geodesicFlow P t)).2 = 0 at h0
  rw [hZ2 P t hsc] at h0
  have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I) (x := x₀) hss
  rw [I.range_eq_univ, mfderivWithin_univ] at hcomp
  have hv : mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ (γ t))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (γ t) (g.geodesicFlow P t).snd) =
        (g.geodesicFlow P t).snd :=
    congrArg (fun L => L (g.geodesicFlow P t).snd) hcomp
  have h0' : mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (γ t) (g.geodesicFlow P t).snd = 0 := h0
  rw [h0', map_zero] at hv
  rw [← hv] at hsnd
  exact zero_ne_one ((ContinuousLinearMap.map_zero₂ _ _).symm.trans hsnd)

/-- **S-CVX (frozen interface): strictly convex balls.** On a compact set there is a uniform
radius `ρ` such that along every unit geodesic arc of length `≤ 2ρ` with endpoints in
`closedBall x ρ` (`x ∈ K`), `t ↦ d(x, σ t)²` is strictly convex and the arc stays in the ball.
The arc is first confined to `ball x (3ρ)` by unit speed, where the second derivative of `d_x²` is
positive (`exists_ball_deriv2_sq_dist_pos`); convexity and the endpoint bounds then keep it in the
closed `ρ`-ball. -/
theorem exists_strictConvex_radius
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ > 0, ∀ x ∈ K, ∀ (p : TangentBundle I M) (ℓ : ℝ), 0 ≤ ℓ → ℓ ≤ 2 * ρ →
      g.inner p.proj p.snd p.snd = 1 → dist x p.proj ≤ ρ → dist x (g.geodesicFlow p ℓ).proj ≤ ρ →
      StrictConvexOn ℝ (Icc 0 ℓ) (fun t => dist x (g.geodesicFlow p t).proj ^ 2) ∧
        ∀ t ∈ Icc 0 ℓ, dist x (g.geodesicFlow p t).proj ≤ ρ := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  choose δ hδ hloc using fun x₀ : M => exists_ball_deriv2_sq_dist_pos g hr hnorm x₀
  obtain ⟨ε, hε, hleb⟩ := lebesgue_number_lemma_of_metric hK
    (c := fun i : K => ball (i : M) (δ i)) (fun _ => isOpen_ball)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hδ x)⟩)
  refine ⟨ε / 3, by positivity, fun x hx p ℓ hℓ0 hℓ hp h0 hℓd => ?_⟩
  obtain ⟨i, hi⟩ := hleb x hx
  set γ : ℝ → M := fun s => (g.geodesicFlow p s).proj with hγ
  have hlip : ∀ s t, dist (γ s) (γ t) ≤ |t - s| := dist_proj_geodesicFlow_le_of_unit g hr hnorm hp
  have hγ0 : γ 0 = p.proj := by
    change (g.geodesicFlow p 0).proj = p.proj
    rw [g.geodesicFlow_zero hr1]
  have hcont : Continuous γ := continuous_proj_geodesicFlow_of_unit g hr hnorm hp
  have h0' : dist x (γ 0) ≤ ε / 3 := by rw [hγ0]; exact h0
  -- the arc stays in `ball x ε`
  have hin : ∀ t ∈ Icc 0 ℓ, γ t ∈ ball x ε := by
    intro t ht
    have h1 : dist x (γ t) ≤ dist x (γ 0) + t := by
      have := hlip 0 t
      rw [sub_zero, abs_of_nonneg ht.1] at this
      linarith [dist_triangle x (γ 0) (γ t)]
    have h2 : dist x (γ t) ≤ dist x (γ ℓ) + (ℓ - t) := by
      have := hlip ℓ t
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 ht.2)] at this
      linarith [dist_triangle x (γ ℓ) (γ t), dist_comm (γ ℓ) (γ t)]
    rw [mem_ball, dist_comm]
    rcases le_total t (ℓ - t) with h | h
    · linarith
    · change dist x (g.geodesicFlow p ℓ).proj ≤ ε / 3 at hℓd
      linarith
  have hxi : x ∈ ball (i : M) (δ i) := hi (mem_ball_self hε)
  have hpos : ∀ t ∈ interior (Icc 0 ℓ), 0 < deriv^[2] (fun s => dist x (γ s) ^ 2) t := by
    intro t ht
    rw [interior_Icc] at ht
    exact hloc i x hxi p hp t (hi (hin t (Ioo_subset_Icc_self ht)))
  have hsc : StrictConvexOn ℝ (Icc 0 ℓ) (fun t => dist x (γ t) ^ 2) :=
    strictConvexOn_of_deriv2_pos (convex_Icc 0 ℓ)
      ((continuous_const.dist hcont).pow 2).continuousOn hpos
  refine ⟨hsc, fun t ht => ?_⟩
  have hmax := hsc.convexOn.le_max_of_mem_Icc (left_mem_Icc.2 hℓ0) (right_mem_Icc.2 hℓ0) ht
  have hsq : dist x (γ t) ^ 2 ≤ (ε / 3) ^ 2 :=
    hmax.trans (max_le (pow_le_pow_left₀ dist_nonneg h0' 2)
      (pow_le_pow_left₀ dist_nonneg hℓd 2))
  exact (pow_le_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).mp hsq

end DifferentialGeometry.Geometry.FiniteSoul
