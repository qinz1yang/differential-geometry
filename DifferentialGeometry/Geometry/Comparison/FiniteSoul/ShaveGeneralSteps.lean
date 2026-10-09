import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveSteps

/-!
# General-dimension S-SHAVE: the linear upper support of the boundary distance from the shift

Lane CMS3-SHAVE (group 2, steps of A2). For a complete metric `g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`)
with `sec ≥ 0` in ANY dimension and a set `C` with the orthogonal boundary shift `hshiftC` (the
conclusion of A1 `exists_orthogonal_boundary_shift_of_transverseShift` at every interior point, or of
CMS-B's `exists_orthogonal_boundary_shift_dim_two` in dimension two): at `x ∈ int C`, for a unit
direction `u` reaching `∂C` at time `d(x, ∂C)` and any unit `e`,
`d(exp_x (h e), ∂C) ≤ d(x, ∂C) - h g_x(u, e)` for all small `h > 0` (`infDist_frontier_step_of_shift`).

The proofs are CMS-B's `ShaveSteps.lean` with the 2D shift replaced by `hshiftC x hx` (recipe of
`build-logs/worker-CMS-B.md` §G4); the hinge (`dist_sq_le_hinge_finite`) is dimension-free. In general
dimension `e = c u + n w` with `w = (e - c u)/n`, `c = g_x(u, e)`, `n = (1 - c²)^{1/2}`. Total convexity
and closedness of `C` enter only through `hshiftC`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **The step, case `g_x(u, e) ≤ 0`** (any dimension, from the orthogonal shift). -/
theorem infDist_frontier_step_of_inner_nonpos_of_shift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) {C : Set M}
    (hshiftC : ∀ x ∈ interior C, ∃ ρ > 0, ∀ y : M, dist x y < ρ → ∀ u w : E, g.inner y u u = 1 →
      g.inner y w w = 1 → g.inner y u w = 0 →
      g.expMap (⟨y, infDist y (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) (frontier C) ≤
        infDist y (frontier C))
    {x : M} (hx : x ∈ interior C) {u : E} (hu : g.inner x u u = 1)
    (hfoot : g.expMap (⟨x, infDist x (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C)
    {e : E} (he : g.inner x e e = 1) (hc : g.inner x u e ≤ 0) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) (frontier C) ≤
      infDist x (frontier C) - h * g.inner x u e := by
  obtain ⟨ρ₀, hρ₀, hshift⟩ := hshiftC x hx
  obtain ⟨ρ₁, hρ₁, hrad⟩ := exists_radial_dist_eq g hr hnorm x
  set c : ℝ := g.inner x u e with hcdef
  have heu : g.inner x e u = c := by rw [shaveInner_symm]
  have hw2 : g.inner x (e - c • u) (e - c • u) = 1 - c ^ 2 := by
    simp only [shaveInner_sub_left, shaveInner_sub_right, shaveInner_smul_left,
      shaveInner_smul_right, he, hu, heu, ← hcdef]
    ring
  have hnn : 0 ≤ g.inner x (e - c • u) (e - c • u) :=
    DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g x _
  rw [hw2] at hnn
  set n : ℝ := Real.sqrt (1 - c ^ 2) with hndef
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hnsq : n ^ 2 = 1 - c ^ 2 := Real.sq_sqrt hnn
  have hn1 : n ≤ 1 := by nlinarith [sq_nonneg c]
  rcases eq_or_lt_of_le hn0 with hnzero | hnpos
  · -- `c = -1`
    have hc1 : c = -1 := by
      have h := hnsq
      rw [← hnzero] at h
      nlinarith
    filter_upwards [Ioo_mem_nhdsGT hρ₁] with h hh
    have hd : dist x (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) = h :=
      hrad e he h ⟨hh.1.le, hh.2⟩
    have htri : infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) (frontier C) ≤
        infDist x (frontier C) + dist (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) x :=
      infDist_le_infDist_add_dist
    rw [dist_comm, hd] at htri
    refine htri.trans (le_of_eq ?_)
    rw [hc1]
    ring
  · have hne : n ≠ 0 := ne_of_gt hnpos
    have hw : g.inner x (n⁻¹ • (e - c • u)) (n⁻¹ • (e - c • u)) = 1 := by
      rw [shaveInner_smul_left, shaveInner_smul_right, hw2, ← hnsq]
      field_simp
    have huw : g.inner x u (n⁻¹ • (e - c • u)) = 0 := by
      rw [shaveInner_smul_right, shaveInner_sub_right, shaveInner_smul_right, hu, ← hcdef]
      ring
    have hwe : g.inner x (n⁻¹ • (e - c • u)) e = n := by
      rw [shaveInner_smul_left, shaveInner_sub_left, shaveInner_smul_left, he, ← hcdef]
      have h1 : 1 - c * c = n ^ 2 := by rw [hnsq]; ring
      rw [h1]
      field_simp
    have hδ : 0 < min ρ₀ ρ₁ := lt_min hρ₀ hρ₁
    filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
    obtain ⟨hh0, hhδ⟩ := hh
    have hhρ₀ : h < ρ₀ := lt_of_lt_of_le hhδ (min_le_left _ _)
    have hhρ₁ : h < ρ₁ := lt_of_lt_of_le hhδ (min_le_right _ _)
    have hhn0 : 0 < h * n := mul_pos hh0 hnpos
    have hhnle : h * n ≤ h := by nlinarith
    have hshiftb : infDist (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M))
        (frontier C) ≤ infDist x (frontier C) :=
      hshift x (by rw [dist_self]; exact hρ₀) u (n⁻¹ • (e - c • u)) hu hw huw hfoot
        (h * n) ⟨hhn0.le, lt_of_le_of_lt hhnle hhρ₀⟩
    have hminw : dist x (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M)) =
        h * n := hrad _ hw (h * n) ⟨hhn0.le, lt_of_le_of_lt hhnle hhρ₁⟩
    have hmine : dist x (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) = h :=
      hrad e he h ⟨hh0.le, hhρ₁⟩
    have hhinge := dist_sq_le_hinge_finite g hr hnorm hsec x hhn0 hh0 hw he hminw hmine
    rw [hwe] at hhinge
    have hcn : (0 : ℝ) ≤ h * (-c) := mul_nonneg hh0.le (by linarith)
    have hsq : dist (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M))
        (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) ^ 2 ≤ (h * (-c)) ^ 2 := by
      have heq : (h * n) ^ 2 + h ^ 2 - 2 * (h * n) * h * n = (h * (-c)) ^ 2 := by
        linear_combination (-h ^ 2) * hnsq
      linarith
    have hdle : dist (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M))
        (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) ≤ h * (-c) := by
      have hroot := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq hcn] at hroot
    have hfinal : infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) (frontier C) ≤
        infDist (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M)) (frontier C) +
          dist (g.expMap (⟨x, h • e⟩ : TangentBundle I M))
            (g.expMap (⟨x, (h * n) • (n⁻¹ • (e - c • u))⟩ : TangentBundle I M)) :=
      infDist_le_infDist_add_dist
    rw [dist_comm] at hfinal
    refine hfinal.trans ((add_le_add hshiftb hdle).trans (le_of_eq ?_))
    ring

/-- **The step, case `g_x(u, e) > 0`** (any dimension; four hinges and one orthogonal shift). -/
theorem infDist_frontier_step_of_inner_pos_of_shift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) {C : Set M}
    (hshiftC : ∀ x ∈ interior C, ∃ ρ > 0, ∀ y : M, dist x y < ρ → ∀ u w : E, g.inner y u u = 1 →
      g.inner y w w = 1 → g.inner y u w = 0 →
      g.expMap (⟨y, infDist y (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) (frontier C) ≤
        infDist y (frontier C))
    {x : M} (hx : x ∈ interior C) {u : E} (hu : g.inner x u u = 1)
    (hfoot : g.expMap (⟨x, infDist x (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C)
    {e : E} (he : g.inner x e e = 1) (hc : 0 < g.inner x u e) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) (frontier C) ≤
      infDist x (frontier C) - h * g.inner x u e := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  obtain ⟨ρ₀, hρ₀, hshift⟩ := hshiftC x hx
  obtain ⟨ρ₁, hρ₁, hrad⟩ := exists_radial_dist_eq g hr hnorm x
  have hfne : (frontier C).Nonempty := ⟨_, hfoot⟩
  have hlpos : 0 < infDist x (frontier C) :=
    (isClosed_frontier.notMem_iff_infDist_pos hfne).1 (fun hf => hf.2 hx)
  have hc1 : g.inner x u e ≤ 1 := by
    have hcs := DifferentialGeometry.Geometry.Collapse.abs_finite_inner_le g x u e
    rw [hu, he, Real.sqrt_one, mul_one] at hcs
    exact (abs_le.mp hcs).2
  obtain ⟨hseg, hτ⟩ := dist_infDist_expMap_smul_of_foot g hr hnorm hu hfoot
  set l : ℝ := infDist x (frontier C) with hldef
  set c : ℝ := g.inner x u e with hcdef
  have hτlip : ∀ s t : ℝ, dist (g.expMap (⟨x, s • u⟩ : TangentBundle I M))
      (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) ≤ |t - s| := by
    intro s t
    have h := g.dist_expMap_smul_le_of_completeSpace hr1 hnorm (x := x) u s t
    rwa [hu, Real.sqrt_one, one_mul] at h
  have hτc : Continuous (fun t : ℝ => g.expMap (⟨x, t • u⟩ : TangentBundle I M)) := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun s t => ?_)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_comm]
    exact hτlip s t
  have hτ0 : g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x := by
    rw [zero_smul]; exact g.expMap_zero hr1 x
  have hδ : 0 < min (min (ρ₀ / 4) ρ₁) (l / 4) := lt_min (lt_min (by linarith) hρ₁) (by linarith)
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
  obtain ⟨hh0, hhδ⟩ := hh
  have hhρ₀ : h < ρ₀ / 4 := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_left _ _))
  have hhρ₁ : h < ρ₁ := lt_of_lt_of_le hhδ ((min_le_left _ _).trans (min_le_right _ _))
  have hhl : h < l / 4 := lt_of_lt_of_le hhδ (min_le_right _ _)
  have hxz : dist x (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) = h := hrad e he h ⟨hh0.le, hhρ₁⟩
  set z : M := g.expMap (⟨x, h • e⟩ : TangentBundle I M) with hzdef
  change infDist z (frontier C) ≤ l - h * c
  have hzx : dist z x = h := by rw [dist_comm]; exact hxz
  obtain ⟨t₀, ht₀mem, ht₀min⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlpos.le)
    ((continuous_const.dist hτc).continuousOn :
      ContinuousOn (fun t => dist z (g.expMap (⟨x, t • u⟩ : TangentBundle I M))) (Icc 0 l))
  have hmin : ∀ t ∈ Icc 0 l, dist z (g.expMap (⟨x, t₀ • u⟩ : TangentBundle I M)) ≤
      dist z (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) := fun t ht => ht₀min ht
  have hxt₀ : dist x (g.expMap (⟨x, t₀ • u⟩ : TangentBundle I M)) = t₀ := (hτ t₀ ht₀mem).1
  have hψt₀ : infDist (g.expMap (⟨x, t₀ • u⟩ : TangentBundle I M)) (frontier C) = l - t₀ :=
    (hτ t₀ ht₀mem).2
  set τ₀ : M := g.expMap (⟨x, t₀ • u⟩ : TangentBundle I M) with hτ₀def
  have hmin0 : dist z τ₀ ≤ dist z (g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M)) :=
    hmin 0 ⟨le_rfl, hlpos.le⟩
  rw [hτ0, hzx] at hmin0
  set rr : ℝ := dist z τ₀ with hrrdef
  have hrrnn : 0 ≤ rr := dist_nonneg
  have ht₀le : t₀ ≤ 2 * h := by
    have htri : dist x τ₀ ≤ dist x z + dist z τ₀ := dist_triangle _ _ _
    rw [hxt₀, hxz] at htri
    linarith
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀mem.1 with hzero | hposi
    · exfalso
      have hτ₀x : τ₀ = x := by rw [hτ₀def, ← hzero]; exact hτ0
      have hrr_eq : rr = h := by rw [hrrdef, hτ₀x]; exact hzx
      have hspos : 0 < min l (h * c) := lt_min hlpos (mul_pos hh0 hc)
      have hsl : min l (h * c) ≤ l := min_le_left _ _
      have hshc : min l (h * c) ≤ h * c := min_le_right _ _
      have hminu : dist x (g.expMap (⟨x, min l (h * c) • u⟩ : TangentBundle I M)) = min l (h * c) :=
        (hτ _ ⟨hspos.le, hsl⟩).1
      have hhinge : dist (g.expMap (⟨x, min l (h * c) • u⟩ : TangentBundle I M)) z ^ 2 ≤
          min l (h * c) ^ 2 + h ^ 2 - 2 * min l (h * c) * h * c :=
        dist_sq_le_hinge_finite g hr hnorm hsec x hspos hh0 hu he hminu hxz
      have hmins : rr ≤ dist z (g.expMap (⟨x, min l (h * c) • u⟩ : TangentBundle I M)) :=
        hmin _ ⟨hspos.le, hsl⟩
      have hge : h ≤ dist (g.expMap (⟨x, min l (h * c) • u⟩ : TangentBundle I M)) z := by
        rw [dist_comm]; linarith
      exact shave_hinge_start_aux hspos hh0 hc hge hshc hhinge
    · exact hposi
  have ht₀l : t₀ < l := by linarith
  rcases eq_or_lt_of_le hrrnn with hr0 | hrrpos
  · have hzeq : z = τ₀ := dist_eq_zero.1 (by rw [← hrrdef]; exact hr0.symm)
    have ht₀h : t₀ = h := by rw [← hxt₀, ← hzeq]; exact hxz
    rw [hzeq, hψt₀, ht₀h]
    nlinarith
  · -- the velocity of the segment at `t₀`
    have hPproj : (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) t₀).proj = τ₀ :=
      (g.expMap_smul_eq_proj_geodesicFlow hr1 x u t₀ (by rw [hD]; exact mem_univ _)).symm
    obtain ⟨V, hVdef⟩ : ∃ V : E, V = (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) t₀).snd :=
      ⟨_, rfl⟩
    have hfwd : ∀ s : ℝ, g.expMap (⟨τ₀, s • V⟩ : TangentBundle I M) =
        g.expMap (⟨x, (t₀ + s) • u⟩ : TangentBundle I M) := by
      intro s
      have h1 := proj_geodesicFlow_add_eq_expMap g hr hnorm (⟨x, u⟩ : TangentBundle I M) t₀ s
      have h2 := g.expMap_smul_eq_proj_geodesicFlow hr1 x u (t₀ + s) (by rw [hD]; exact mem_univ _)
      calc g.expMap (⟨τ₀, s • V⟩ : TangentBundle I M)
          = g.expMap (⟨(g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) t₀).proj, s • V⟩ :
              TangentBundle I M) := expMap_mk_congr g hPproj.symm (s • V)
        _ = (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) (t₀ + s)).proj := by
            subst hVdef; exact h1.symm
        _ = g.expMap (⟨x, (t₀ + s) • u⟩ : TangentBundle I M) := h2.symm
    have hVu : g.inner τ₀ V V = 1 := by
      have h3 := g.inner_geodesicFlow_eq hr1 (⟨x, u⟩ : TangentBundle I M) t₀
        (by rw [hD]; exact mem_univ _)
      rw [← hPproj]
      subst hVdef
      exact h3.trans hu
    -- the back leg to `x`
    have hback : g.expMap (⟨τ₀, t₀ • ((-1 : ℝ) • V)⟩ : TangentBundle I M) = x := by
      have hv : (t₀ • ((-1 : ℝ) • V) : E) = (-t₀) • V := by rw [smul_smul, mul_neg_one]
      calc g.expMap (⟨τ₀, t₀ • ((-1 : ℝ) • V)⟩ : TangentBundle I M)
          = g.expMap (⟨τ₀, (-t₀) • V⟩ : TangentBundle I M) :=
            congrArg (fun w : E => g.expMap (⟨τ₀, w⟩ : TangentBundle I M)) hv
        _ = g.expMap (⟨x, (t₀ + -t₀) • u⟩ : TangentBundle I M) := hfwd (-t₀)
        _ = x := by rw [add_neg_cancel]; exact hτ0
    have hnegV : g.inner τ₀ ((-1 : ℝ) • V) ((-1 : ℝ) • V) = 1 := by
      rw [shaveInner_smul_left, shaveInner_smul_right, hVu]; norm_num
    have hminback : dist τ₀ (g.expMap (⟨τ₀, t₀ • ((-1 : ℝ) • V)⟩ : TangentBundle I M)) = t₀ := by
      rw [hback, dist_comm]; exact hxt₀
    -- the segment from `τ₀` to `z`
    obtain ⟨W, hW, -, hWend⟩ := g.exists_unit_segment_expMap hr hnorm τ₀ z
    have hτ₀z : dist τ₀ z = rr := by rw [hrrdef, dist_comm]
    have hWend' : g.expMap (⟨τ₀, rr • W⟩ : TangentBundle I M) = z := by
      rw [← hτ₀z]; exact hWend
    have hminW : dist τ₀ (g.expMap (⟨τ₀, rr • W⟩ : TangentBundle I M)) = rr := by
      rw [hWend']; exact hτ₀z
    have hloc : ∀ᶠ s in 𝓝 (0 : ℝ), dist (g.expMap (⟨τ₀, rr • W⟩ : TangentBundle I M)) τ₀ ≤
        dist (g.expMap (⟨τ₀, rr • W⟩ : TangentBundle I M)) (g.expMap (⟨τ₀, s • V⟩ : TangentBundle I M)) := by
      filter_upwards [Ioo_mem_nhds (show -t₀ < (0 : ℝ) by linarith)
        (show (0 : ℝ) < l - t₀ by linarith)] with s hs
      have h5 := hmin (t₀ + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
      rw [← hfwd s] at h5
      rw [hWend']
      exact h5
    have hperp : g.inner τ₀ W V = 0 :=
      inner_eq_zero_of_isLocalMin_dist g hr hnorm hsec hVu hW hrrpos hminW hloc
    -- hinge at `τ₀`: Pythagoras
    have hinge2 : dist x z ^ 2 ≤ t₀ ^ 2 + rr ^ 2 - 2 * t₀ * rr * g.inner τ₀ ((-1 : ℝ) • V) W := by
      have h4 := dist_sq_le_hinge_finite g hr hnorm hsec τ₀ ht₀pos hrrpos hnegV hW hminback hminW
      rwa [hback, hWend'] at h4
    have hVW : g.inner τ₀ ((-1 : ℝ) • V) W = 0 := by
      rw [shaveInner_smul_left, shaveInner_symm g τ₀ V W, hperp, mul_zero]
    rw [hVW, hxz] at hinge2
    have hpyth : h ^ 2 ≤ t₀ ^ 2 + rr ^ 2 := by linarith
    -- hinge at `x`
    have hinge1 : dist τ₀ z ^ 2 ≤ t₀ ^ 2 + h ^ 2 - 2 * t₀ * h * c :=
      dist_sq_le_hinge_finite g hr hnorm hsec x ht₀pos hh0 hu he hxt₀ hxz
    rw [hτ₀z] at hinge1
    have ht₀ge : h * c ≤ t₀ := shave_hinge_foot_aux ht₀pos hinge1 hpyth
    -- the orthogonal shift at `τ₀`
    have hfoot₀ : g.expMap (⟨τ₀, infDist τ₀ (frontier C) • V⟩ : TangentBundle I M) ∈ frontier C := by
      rw [hψt₀, hfwd (l - t₀), show t₀ + (l - t₀) = l by ring]
      exact hfoot
    have hVW' : g.inner τ₀ V W = 0 := by rw [shaveInner_symm]; exact hperp
    have hsh : infDist (g.expMap (⟨τ₀, rr • W⟩ : TangentBundle I M)) (frontier C) ≤
        infDist τ₀ (frontier C) :=
      hshift τ₀ (by rw [hxt₀]; linarith) V W hVu hW hVW' hfoot₀ rr ⟨hrrnn, by linarith⟩
    rw [hWend', hψt₀] at hsh
    linarith

/-- **The exact linear upper support of `d(·, ∂C)`, any dimension** (B4.4 with the orthogonal boundary
shift `hshiftC` as hypothesis): at an interior point, along any unit direction `e`, with slope
`-g_x(u, e)` for a unit direction `u` to a nearest boundary point. -/
theorem infDist_frontier_step_of_shift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) {C : Set M}
    (hshiftC : ∀ x ∈ interior C, ∃ ρ > 0, ∀ y : M, dist x y < ρ → ∀ u w : E, g.inner y u u = 1 →
      g.inner y w w = 1 → g.inner y u w = 0 →
      g.expMap (⟨y, infDist y (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) (frontier C) ≤
        infDist y (frontier C))
    {x : M} (hx : x ∈ interior C) {u : E} (hu : g.inner x u u = 1)
    (hfoot : g.expMap (⟨x, infDist x (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C)
    {e : E} (he : g.inner x e e = 1) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), infDist (g.expMap (⟨x, h • e⟩ : TangentBundle I M)) (frontier C) ≤
      infDist x (frontier C) - h * g.inner x u e := by
  rcases le_or_gt (g.inner x u e) 0 with hc | hc
  · exact infDist_frontier_step_of_inner_nonpos_of_shift g hr hnorm hsec hshiftC hx hu hfoot he hc
  · exact infDist_frontier_step_of_inner_pos_of_shift g hr hnorm hsec hshiftC hx hu hfoot he hc

end DifferentialGeometry.Geometry.FiniteSoul

end
