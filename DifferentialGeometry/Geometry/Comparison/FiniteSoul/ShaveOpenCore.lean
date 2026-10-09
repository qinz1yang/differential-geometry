import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TotallyConvexSegments
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.HopfRinow
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SpeedBound
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.ChartMetric

/-!
# S-SHAVE, R1(i): the open core of a totally convex set (finite metric)

Lane CMS-B (finite soul package CM-S-surface, review `review-finite-soul.md` §4 R1(i)). For a
complete metric `g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`) and a totally convex set `C`
(`IsTotallyConvexFinite`, every geodesic-flow arc with ends in `C` stays in `C`):

* `exists_expMap_smul_mem_interior` (radial cone, kernel): on a compact set `K` there is a uniform
  radius `ρ` such that for `y ∈ K ∩ C` and `|v|_{g_y} < ρ`, `exp_y v ∈ int C` forces
  `exp_y (a v) ∈ int C` for every `a ∈ (0, 1]`. Proof: in the normal chart `e` of CM1.d the map
  `z ↦ e (a e⁻¹ z)` is open and, by total convexity, maps `int C ∩ ball y ρ` into `C`. No
  "no conjugate points" statement and no short interpolation `J` is needed.
* `IsTotallyConvexFinite.proj_geodesicFlow_mem_interior` (R1(i), propagation): if a geodesic arc
  `γ = π ∘ φ_·(p)` maps `[a, b]` into `C` and meets `int C` at one time, then `γ (a, b) ⊆ int C`.
  Short steps by the radial cone (always at the midpoint) and connectedness of `(a, b)`.
* `IsTotallyConvexFinite.expMap_smul_mem_interior_of_segment`: the segment form `[x, y) ⊆ int C`.
* `ball_infDist_frontier_subset_interior`: `ball y (d(y, ∂C)) ⊆ int C` for `y ∈ C` (no convexity).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology Pointwise

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **Radial cone (kernel of R1(i)).** Uniformly on a compact set `K`: for `y ∈ K ∩ C`, `C` totally
convex, and `|v|_{g_y} < ρ`, if `exp_y v ∈ int C` then `exp_y (a v) ∈ int C` for all `a ∈ (0, 1]`. -/
theorem exists_expMap_smul_mem_interior
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ > 0, ∀ {C : Set M}, IsTotallyConvexFinite g C → ∀ y ∈ K, y ∈ C → ∀ v : E,
      g.inner y v v < ρ ^ 2 → g.expMap (⟨y, v⟩ : TangentBundle I M) ∈ interior C →
        ∀ a ∈ Ioc (0 : ℝ) 1, g.expMap (⟨y, a • v⟩ : TangentBundle I M) ∈ interior C := by
  obtain ⟨ρ, hρ, hch⟩ := g.exists_uniform_normal_charts hr hnorm hK
  refine ⟨ρ, hρ, fun {C} hC y hyK hyC v hv hvint a ha => ?_⟩
  obtain ⟨e, hsrc, htgt, hexp, -, -, -⟩ := hch y hyK
  set U : Set M := interior C ∩ ball y ρ with hU
  have hUo : IsOpen U := isOpen_interior.inter isOpen_ball
  set V : Set E := e.source ∩ e ⁻¹' U with hV
  have hVo : IsOpen V := e.isOpen_inter_preimage hUo
  have hvsrc : v ∈ e.source := by rw [hsrc]; exact hv
  have hvV : v ∈ V := by
    refine ⟨hvsrc, ?_, ?_⟩
    · rw [(hexp v hvsrc).2]; exact hvint
    · rw [← htgt]; exact e.map_source hvsrc
  have ha0 : a ≠ 0 := ne_of_gt ha.1
  have hWo : IsOpen (a • V) := hVo.smul₀ ha0
  have hsmul_src : ∀ w ∈ V, a • w ∈ e.source := by
    intro w hw
    have hw' : g.inner y w w < ρ ^ 2 := by
      have := hw.1; rw [hsrc] at this; exact this
    rw [hsrc]
    change g.inner y (a • w) (a • w) < ρ ^ 2
    have hsm : g.inner y (a • w) (a • w) = a ^ 2 * g.inner y w w :=
      DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self g y a w
    rw [hsm]
    have h0 := DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g y w
    have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
    nlinarith
  have hWsrc : a • V ⊆ e.source := by
    rintro _ ⟨w, hw, rfl⟩
    exact hsmul_src w hw
  have himgo : IsOpen (e '' (a • V)) := e.isOpen_image_of_subset_source hWo hWsrc
  have himgC : e '' (a • V) ⊆ C := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hwsrc : w ∈ e.source := hw.1
    have hzC : g.expMap (⟨y, (1 : ℝ) • w⟩ : TangentBundle I M) ∈ C := by
      rw [one_smul, ← (hexp w hwsrc).2]
      exact interior_subset hw.2.1
    have hmem := hC.expMap_mem hr hnorm zero_le_one hyC hzC a ⟨ha.1.le, ha.2⟩
    change e (a • w) ∈ C
    rw [(hexp (a • w) (hsmul_src w hw)).2]
    exact hmem
  have hmemimg : e (a • v) ∈ e '' (a • V) := ⟨a • v, ⟨v, hvV, rfl⟩, rfl⟩
  have hint := interior_maximal himgC himgo hmemimg
  rwa [(hexp (a • v) (hsmul_src v hvV)).2] at hint

omit [IsManifold I ∞ M] in
private theorem convex_comb_mem_Ioo {a b s θ : ℝ} (hab : a < b) (hs : s ∈ Icc a b)
    (hθ : θ ∈ Ioc (0 : ℝ) 1) : s + θ * ((a + b) / 2 - s) ∈ Ioo a b := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  constructor <;> nlinarith [hs.1, hs.2]

/-- The geodesic flow read through the exponential map from an intermediate time. -/
theorem proj_geodesicFlow_add_eq_expMap
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : TangentBundle I M) (s τ : ℝ) :
    (g.geodesicFlow p (s + τ)).proj =
      g.expMap (⟨(g.geodesicFlow p s).proj, τ • (g.geodesicFlow p s).snd⟩ : TangentBundle I M) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  rw [g.geodesicFlow_add hr1 (by rw [hD]; exact mem_univ _) (by rw [hD]; exact mem_univ _),
    g.expMap_smul_eq_proj_geodesicFlow hr1 _ _ τ (by rw [hD]; exact mem_univ _)]

/-- **R1(i): the open core along an arbitrary geodesic arc.** If `γ = π ∘ φ_·(p)` maps `[a, b]`
into the totally convex set `C` and `γ s ∈ int C` for one `s ∈ [a, b]`, then `γ t ∈ int C` for every
`t ∈ (a, b)`. -/
theorem IsTotallyConvexFinite.proj_geodesicFlow_mem_interior
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) (p : TangentBundle I M) {a b : ℝ}
    (hmaps : ∀ t ∈ Icc a b, (g.geodesicFlow p t).proj ∈ C) {s : ℝ} (hs : s ∈ Icc a b)
    (hsC : (g.geodesicFlow p s).proj ∈ interior C) :
    ∀ t ∈ Ioo a b, (g.geodesicFlow p t).proj ∈ interior C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set γ : ℝ → M := fun t => (g.geodesicFlow p t).proj with hγ
  set σ : ℝ := Real.sqrt (g.inner p.proj p.snd p.snd) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hlip : ∀ s t : ℝ, dist (γ s) (γ t) ≤ σ * |t - s| := fun s t =>
    g.dist_proj_geodesicFlow_le hr1 hnorm (fun τ _ => by rw [hD]; exact mem_univ _)
  have hγc : Continuous γ := by
    refine Metric.continuous_iff.2 fun t ε hε => ⟨ε / (σ + 1), by positivity, fun z hz => ?_⟩
    refine (hlip z t).trans_lt ?_
    rw [Real.dist_eq] at hz
    calc σ * |t - z| = σ * |z - t| := by rw [abs_sub_comm]
      _ ≤ σ * (ε / (σ + 1)) := mul_le_mul_of_nonneg_left hz.le hσ0
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  obtain ⟨ρ, hρ, hcone⟩ :=
    exists_expMap_smul_mem_interior g hr hnorm (isCompact_Icc.image hγc : IsCompact (γ '' Icc a b))
  -- the short step
  have hstep : ∀ s₁ ∈ Icc a b, ∀ s₂ ∈ Icc a b, σ * |s₁ - s₂| < ρ → γ s₁ ∈ interior C →
      ∀ c ∈ Ioc (0 : ℝ) 1, γ (s₂ + c * (s₁ - s₂)) ∈ interior C := by
    intro s₁ hs₁ s₂ hs₂ hlt hint c hc
    have hspeed : g.inner (g.geodesicFlow p s₂).proj (g.geodesicFlow p s₂).snd
        (g.geodesicFlow p s₂).snd = σ ^ 2 := by
      rw [g.inner_geodesicFlow_eq hr1 p s₂ (by rw [hD]; exact mem_univ _), hσ,
        Real.sq_sqrt (DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g _ _)]
    have hv : g.inner (g.geodesicFlow p s₂).proj ((s₁ - s₂) • (g.geodesicFlow p s₂).snd)
        ((s₁ - s₂) • (g.geodesicFlow p s₂).snd) < ρ ^ 2 := by
      rw [DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self, hspeed]
      have h1 : (σ * |s₁ - s₂|) ^ 2 < ρ ^ 2 := by
        have h0 : 0 ≤ σ * |s₁ - s₂| := mul_nonneg hσ0 (abs_nonneg _)
        nlinarith
      calc (s₁ - s₂) ^ 2 * σ ^ 2 = (σ * |s₁ - s₂|) ^ 2 := by rw [mul_pow, sq_abs]; ring
        _ < ρ ^ 2 := h1
    have hend : g.expMap (⟨(g.geodesicFlow p s₂).proj, (s₁ - s₂) • (g.geodesicFlow p s₂).snd⟩ :
        TangentBundle I M) ∈ interior C := by
      rw [← proj_geodesicFlow_add_eq_expMap g hr hnorm, add_sub_cancel]
      exact hint
    have h := hcone hC (γ s₂) ⟨s₂, hs₂, rfl⟩ (hmaps s₂ hs₂) _ hv hend c hc
    have heq : γ (s₂ + c * (s₁ - s₂)) = g.expMap (⟨(g.geodesicFlow p s₂).proj,
        c • (s₁ - s₂) • (g.geodesicFlow p s₂).snd⟩ : TangentBundle I M) := by
      change (g.geodesicFlow p (s₂ + c * (s₁ - s₂))).proj = _
      rw [proj_geodesicFlow_add_eq_expMap g hr hnorm p s₂, mul_smul]
    rw [heq]
    exact h
  intro t ht
  have hab : a < b := ht.1.trans ht.2
  -- connectedness of `(a, b)`
  set u : Set ℝ := γ ⁻¹' interior C with hu
  set v : Set ℝ := {t | ∃ δ > 0, ∀ z ∈ Ioo a b, |z - t| < δ → γ z ∉ interior C} with hv
  have huo : IsOpen u := isOpen_interior.preimage hγc
  have hvo : IsOpen v := by
    rw [Metric.isOpen_iff]
    rintro x ⟨δ, hδ, hkey⟩
    refine ⟨δ / 2, by linarith, fun x' hx' => ⟨δ / 2, by linarith, fun z hz hzx' => hkey z hz ?_⟩⟩
    rw [mem_ball, Real.dist_eq] at hx'
    calc |z - x| = |(z - x') + (x' - x)| := by ring_nf
      _ ≤ |z - x'| + |x' - x| := abs_add_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add hzx' hx'
      _ = δ := by ring
  have hcover : Ioo a b ⊆ u ∪ v := by
    intro x hx
    by_cases hxu : γ x ∈ interior C
    · exact Or.inl hxu
    · right
      set δ : ℝ := min (min (x - a) (b - x)) (ρ / (2 * σ + 1)) with hδ
      have hδ0 : 0 < δ := lt_min (lt_min (by linarith [hx.1]) (by linarith [hx.2])) (by positivity)
      refine ⟨δ, hδ0, fun z hz hzx hzint => hxu ?_⟩
      have hzx1 : |z - x| < x - a := lt_of_lt_of_le hzx ((min_le_left _ _).trans (min_le_left _ _))
      have hzx2 : |z - x| < b - x := lt_of_lt_of_le hzx ((min_le_left _ _).trans (min_le_right _ _))
      have hzx3 : |z - x| < ρ / (2 * σ + 1) := lt_of_lt_of_le hzx (min_le_right _ _)
      rw [abs_lt] at hzx1 hzx2
      have hs₂ : 2 * x - z ∈ Icc a b := ⟨by linarith, by linarith⟩
      have hlt : σ * |z - (2 * x - z)| < ρ := by
        rw [show z - (2 * x - z) = 2 * (z - x) by ring, abs_mul, abs_two]
        have h1 : σ * (2 * |z - x|) ≤ (2 * σ + 1) * |z - x| := by nlinarith [abs_nonneg (z - x)]
        have h2 : (2 * σ + 1) * |z - x| < ρ := by
          rw [lt_div_iff₀ (by positivity)] at hzx3; linarith
        linarith
      have h := hstep z (Ioo_subset_Icc_self hz) (2 * x - z) hs₂ hlt hzint (1 / 2)
        ⟨by norm_num, by norm_num⟩
      rwa [show 2 * x - z + 1 / 2 * (z - (2 * x - z)) = x by ring] at h
  have hdisj : Ioo a b ∩ (u ∩ v) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    rintro hx hxu ⟨δ, hδ, hkey⟩
    exact hkey x hx (by rw [sub_self, abs_zero]; exact hδ) hxu
  -- a point of `(a, b)` in `u`
  have hne : (Ioo a b ∩ u).Nonempty := by
    set m : ℝ := (a + b) / 2 with hm
    set c : ℝ := min 1 (ρ / ((σ + 1) * (|m - s| + 1))) with hc
    have hc0 : 0 < c := lt_min one_pos (by positivity)
    have hc1 : c ≤ 1 := min_le_left _ _
    have hs₂ : s + c * (m - s) ∈ Icc a b :=
      Ioo_subset_Icc_self (convex_comb_mem_Ioo hab hs ⟨hc0, hc1⟩)
    have hlt : σ * |s - (s + c * (m - s))| < ρ := by
      rw [show s - (s + c * (m - s)) = -(c * (m - s)) by ring, abs_neg, abs_mul, abs_of_pos hc0]
      have hcle : c * ((σ + 1) * (|m - s| + 1)) ≤ ρ := by
        have := min_le_right 1 (ρ / ((σ + 1) * (|m - s| + 1)))
        rw [← hc, le_div_iff₀ (by positivity)] at this
        exact this
      nlinarith [abs_nonneg (m - s)]
    have h := hstep s hs (s + c * (m - s)) hs₂ hlt hsC (1 / 2) ⟨by norm_num, by norm_num⟩
    refine ⟨s + c / 2 * (m - s), convex_comb_mem_Ioo hab hs ⟨by positivity, by linarith⟩, ?_⟩
    change γ _ ∈ interior C
    rwa [show s + c * (m - s) + 1 / 2 * (s - (s + c * (m - s))) = s + c / 2 * (m - s) by ring] at h
  rcases (isPreconnected_iff_subset_of_disjoint.1 isPreconnected_Ioo) u v huo hvo hcover hdisj with
    hsub | hsub
  · exact hsub ht
  · exfalso
    obtain ⟨x, hx, hxu⟩ := hne
    obtain ⟨δ, hδ, hkey⟩ := hsub hx
    exact hkey x hx (by rw [sub_self, abs_zero]; exact hδ) hxu

/-- **R1(i), segment form** (design R1(i)): for `x ∈ int C`, `y ∈ C` and the unit initial vector `u`
of a segment from `x` to `y`, the half-open segment `[x, y)` lies in `int C`. -/
theorem IsTotallyConvexFinite.expMap_smul_mem_interior_of_segment
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) {x y : M} (hx : x ∈ interior C) (hy : y ∈ C)
    {u : E} (hxy : g.expMap (⟨x, dist x y • u⟩ : TangentBundle I M) = y) :
    ∀ s ∈ Ico 0 (dist x y), g.expMap (⟨x, s • u⟩ : TangentBundle I M) ∈ interior C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have hflow : ∀ τ : ℝ, g.expMap (⟨x, τ • u⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) τ).proj := fun τ =>
    g.expMap_smul_eq_proj_geodesicFlow hr1 x u τ (by rw [hD]; exact mem_univ _)
  have hmem := hC.expMap_mem hr hnorm dist_nonneg (interior_subset hx) (by rw [hxy]; exact hy)
  have h0 : (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) 0).proj ∈ interior C := by
    rw [g.geodesicFlow_zero hr1]; exact hx
  intro s hs
  rcases eq_or_lt_of_le hs.1 with h | h
  · have h00 : g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x := by
      rw [zero_smul]; exact g.expMap_zero hr1 x
    rw [← h, h00]; exact hx
  · rw [hflow]
    exact hC.proj_geodesicFlow_mem_interior hr hnorm _ (fun t ht => by rw [← hflow]; exact hmem t ht)
      ⟨le_rfl, dist_nonneg⟩ h0 s ⟨h, hs.2⟩

/-- The open ball of radius `d(y, ∂C)` about `y ∈ C` lies in `int C` (segments and connectedness; no
convexity). -/
theorem ball_infDist_frontier_subset_interior [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} {y : M} (hy : y ∈ C) : ball y (infDist y (frontier C)) ⊆ interior C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  intro z hz
  rw [mem_ball, dist_comm] at hz
  have hl : 0 < infDist y (frontier C) := lt_of_le_of_lt dist_nonneg hz
  obtain ⟨u, -, hseg, hend⟩ := g.exists_unit_segment_expMap hr hnorm y z
  set d := dist y z with hd
  set c : ℝ → M := fun s => g.expMap (⟨y, s • u⟩ : TangentBundle I M) with hcdef
  have hc0 : c 0 = y := by simp only [hcdef, zero_smul]; exact g.expMap_zero hr1 y
  have hcd : ∀ s ∈ Icc 0 d, dist y (c s) = s := by
    intro s hs
    have h := hseg 0 ⟨le_rfl, dist_nonneg⟩ s hs
    change dist (c 0) (c s) = |0 - s| at h
    rw [hc0, zero_sub, abs_neg, abs_of_nonneg hs.1] at h
    exact h
  have hcont : ContinuousOn c (Icc 0 d) := by
    refine Metric.continuousOn_iff.2 fun s hs ε hε => ⟨ε, hε, fun t ht hts => ?_⟩
    have h := hseg t ht s hs
    simp only [hcdef]
    rw [h, ← Real.dist_eq]
    exact hts
  have hnf : ∀ s ∈ Icc 0 d, c s ∉ frontier C := by
    intro s hs hf
    have h1 := infDist_le_dist_of_mem (x := y) hf
    rw [hcd s hs] at h1
    linarith [hs.2]
  have hyint : y ∈ interior C := by
    have hyf : y ∉ frontier C := fun hf => by
      rw [infDist_zero_of_mem hf] at hl; exact lt_irrefl 0 hl
    by_contra hyi
    exact hyf ⟨subset_closure hy, hyi⟩
  have hpre : IsPreconnected (c '' Icc 0 d) := isPreconnected_Icc.image c hcont
  have hcover : c '' Icc 0 d ⊆ interior C ∪ (closure C)ᶜ := by
    rintro _ ⟨s, hs, rfl⟩
    by_cases hi : c s ∈ interior C
    · exact Or.inl hi
    · right
      intro hcl
      exact hnf s hs ⟨hcl, hi⟩
  have hdisj : c '' Icc 0 d ∩ (interior C ∩ (closure C)ᶜ) = ∅ := by
    ext w
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and, not_not]
    intro _ hw
    exact interior_subset_closure hw
  rcases (isPreconnected_iff_subset_of_disjoint.1 hpre) _ _ isOpen_interior
      isClosed_closure.isOpen_compl hcover hdisj with hsub | hsub
  · have hzimg : z ∈ c '' Icc 0 d := ⟨d, ⟨dist_nonneg, le_rfl⟩, hend⟩
    exact hsub hzimg
  · exfalso
    have hyimg : y ∈ c '' Icc 0 d := ⟨0, ⟨le_rfl, dist_nonneg⟩, hc0⟩
    exact hsub hyimg (subset_closure hy)

end DifferentialGeometry.Geometry.FiniteSoul

end
