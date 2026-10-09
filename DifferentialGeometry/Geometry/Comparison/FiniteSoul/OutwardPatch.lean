import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# S-PATCH: a smooth strictly outward field from pointwise outward vectors

Package CM-S (finite soul), lane CMS-H. Design `docs/geometrization/chapter13/design-finite-soul-20261004.md`
§4.2 "S-PATCH"; blueprint master207A LFR23 proof (A:26787–26794: *upper semicontinuity of the
direction sets extends each such vector to a smooth local field … a finite partition of unity
patches these fields … convexity preserves both inequalities*) and LFR46 proof (A:28920–28931).

Setting: a smooth carrier `M`, a metric `g` of class `C^{r+1}` (only continuity of its chart
coefficients is used), and a family of direction sets `D x ⊆ T_x M` of `g`-length `≤ 1` whose graph
is sequentially closed in `TM` (exactly the shape of CM3.b,
`mem_finiteMinimizingDirectionsTo_of_tendsto`). The pointwise outward vectors are DATA `v` on a
closed set `A`.

* `exists_subseq_tendsto_of_inner_le`: `g`-bounded vectors over a convergent sequence of base
  points have a convergent subsequence in `TM` (factored from CM-H's escape argument).
* `exists_mem_le_inner_of_tendsto`, `eventually_forall_inner_lt`: upper semicontinuity of
  `y ↦ max_{u ∈ D y} g(Y y, u)` along continuous sections.
* `exists_margin_of_isCompact`: a strict pairing on a compact set has a uniform margin.
* `exists_contMDiff_outward_field`: the smooth field (`g(V, V) < R²` everywhere, pairing `< -c` on
  an open neighbourhood of `A`), by Mathlib's convex patching of local sections.
* `exists_contMDiff_outward_field_minimizingDirections`: the binding to the minimizing directions
  `g.finiteMinimizingDirectionsTo S` (CM3).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- `g(w, w) ≥ 0`. -/
theorem inner_self_nonneg_finite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M)
    (w : TangentSpace I x) : 0 ≤ g.inner x w w := by
  by_cases hw : w = 0
  · rw [hw]
    simp
  · exact (g.pos x w hw).le

/-- A convex combination of two numbers below `L` is below `L`. -/
theorem convex_combination_lt {α β p q L : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hp : p < L) (hq : q < L) : α * p + β * q < L := by
  rcases eq_or_lt_of_le hα with h | h
  · rw [← h] at hαβ ⊢
    rw [zero_add] at hαβ
    rw [hαβ]
    linarith
  · have h1 : α * p < α * L := mul_lt_mul_of_pos_left hp h
    have h2 : β * q ≤ β * L := mul_le_mul_of_nonneg_left hq.le hβ
    have h3 : α * L + β * L = L := by rw [← add_mul, hαβ, one_mul]
    linarith

/-- **Extraction in the tangent bundle.** Vectors of bounded `g`-length over a convergent sequence
of base points have a subsequence converging in `TM`. -/
theorem exists_subseq_tendsto_of_inner_le
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {q : ℕ → TangentBundle I M} {y : M} (hy : Tendsto (fun k => (q k).proj) atTop (𝓝 y))
    {R : ℝ} (hR : ∀ k, g.inner (q k).proj (q k).snd (q k).snd ≤ R) :
    ∃ v : TangentSpace I y, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun j => q (ψ j)) atTop (𝓝 (⟨y, v⟩ : TangentBundle I M)) := by
  have hsrc : ∀ᶠ k in atTop, (q k).proj ∈ (chartAt H y).source :=
    hy ((chartAt H y).open_source.mem_nhds (mem_chart_source H y))
  have hκ : Tendsto (fun k => extChartAt I y (q k).proj) atTop (𝓝 (extChartAt I y y)) :=
    ((continuousAt_extChartAt y).tendsto).comp hy
  have hBc : ContinuousAt (g.chartInner y) (extChartAt I y y) :=
    ((g.contDiffOn_chartInner y).continuousOn).continuousAt
      ((isOpen_extChartAt_target y).mem_nhds (mem_extChartAt_target y))
  obtain ⟨C, hC, hCev⟩ := Bundle.ContMDiffRiemannianMetric.exists_pos_eventually_le_of_isCoercive
    hBc (g.isCoercive_chartInner y (mem_extChartAt_target y))
  set V : ℕ → E := fun k => mfderiv I 𝓘(ℝ, E) (extChartAt I y) (q k).proj (q k).snd with hV
  have hVb : ∀ᶠ k in atTop, V k ∈ closedBall (0 : E) (Real.sqrt (max R 0 / C)) := by
    filter_upwards [hsrc, hκ hCev] with k hk hck
    have h1 := hck (V k)
    change C * ‖V k‖ ^ 2 ≤ g.chartInner y (extChartAt I y (q k).proj) (V k) (V k) at h1
    rw [← g.inner_eq_chartInner hk] at h1
    have h2 : ‖V k‖ ^ 2 ≤ max R 0 / C := by
      rw [le_div_iff₀ hC]
      nlinarith [le_max_left R 0, hR k]
    rw [mem_closedBall_zero_iff]
    calc ‖V k‖ = |‖V k‖| := (abs_of_nonneg (norm_nonneg _)).symm
      _ ≤ Real.sqrt (max R 0 / C) := Real.abs_le_sqrt h2
  obtain ⟨Vlim, -, ψ, hψ, hVlim⟩ :=
    (isCompact_closedBall (0 : E) _).tendsto_subseq' hVb.frequently
  set T := extChartAt I.tangent (⟨y, 0⟩ : TangentBundle I M) with hT
  set z : TangentBundle I M := ⟨y, Vlim⟩ with hz
  have hzsrc : z ∈ T.source := by
    simpa only [hT, extChartAt_source, TangentBundle.mem_chart_source_iff] using
      mem_chart_source H y
  have hTz : T z = (extChartAt I y y, Vlim) := by
    rw [hT, Bundle.ContMDiffRiemannianMetric.extChartAt_tangent_apply_eq _ _
      (mem_chart_source H y)]
    change (extChartAt I y y, mfderiv I 𝓘(ℝ, E) (extChartAt I y) y Vlim) = _
    rw [mfderiv_extChartAt_self]
    rfl
  have hTq : ∀ᶠ k in atTop, T (q k) = (extChartAt I y (q k).proj, V k) :=
    hsrc.mono fun k hk => Bundle.ContMDiffRiemannianMetric.extChartAt_tangent_apply_eq _ _ hk
  have hTlim : Tendsto (fun j => T (q (ψ j))) atTop (𝓝 (T z)) := by
    rw [hTz]
    refine Tendsto.congr' ((hψ.tendsto_atTop.eventually hTq).mono fun j hj => hj.symm) ?_
    exact (hκ.comp hψ.tendsto_atTop).prodMk_nhds hVlim
  have hqsrc : ∀ᶠ j in atTop, q (ψ j) ∈ T.source :=
    hψ.tendsto_atTop.eventually (hsrc.mono fun k hk => (show q k ∈ T.source by
      simpa only [hT, extChartAt_source, TangentBundle.mem_chart_source_iff] using hk))
  refine ⟨Vlim, ψ, hψ, ?_⟩
  have hcont : ContinuousAt T.symm (T z) := continuousAt_extChartAt_symm'' (T.map_source hzsrc)
  have h := hcont.tendsto.comp hTlim
  rw [T.left_inv hzsrc] at h
  refine h.congr' ?_
  filter_upwards [hqsrc] with j hj
  exact T.left_inv hj

/-- **Upper semicontinuity, sequential core.** Along a sequence of directions `u_k ∈ D y_k` with
`y_k → y` and `β_k ≤ g(Y y_k, u_k)`, `β_k → β₀`, some direction `u ∈ D y` has `β₀ ≤ g(Y y, u)`. -/
theorem exists_mem_le_inner_of_tendsto
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (D : (x : M) → Set (TangentSpace I x)) (hDbdd : ∀ x, ∀ u ∈ D x, g.inner x u u ≤ 1)
    (hDclosed : ∀ (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M),
      (∀ k, (p k).snd ∈ D (p k).proj) → Tendsto p atTop (𝓝 pInf) → pInf.snd ∈ D pInf.proj)
    (Y : (x : M) → TangentSpace I x) {N : Set M} (hN : IsOpen N)
    (hY : ContinuousOn (fun x => (⟨x, Y x⟩ : TangentBundle I M)) N) {y : M} (hyN : y ∈ N)
    {q : ℕ → TangentBundle I M} (hq : ∀ k, (q k).snd ∈ D (q k).proj)
    (hqy : Tendsto (fun k => (q k).proj) atTop (𝓝 y)) {β : ℕ → ℝ} {β₀ : ℝ}
    (hβ : Tendsto β atTop (𝓝 β₀))
    (hle : ∀ k, β k ≤ g.inner (q k).proj (Y (q k).proj) (q k).snd) :
    ∃ u ∈ D y, β₀ ≤ g.inner y (Y y) u := by
  obtain ⟨v, ψ, hψ, hlim⟩ := exists_subseq_tendsto_of_inner_le g hqy (R := 1)
    (fun k => hDbdd _ _ (hq k))
  have hv : v ∈ D y := hDclosed (fun j => q (ψ j)) ⟨y, v⟩ (fun j => hq (ψ j)) hlim
  have hproj : Continuous (fun p : TangentBundle I M => p.proj) :=
    FiberBundle.continuous_proj E (TangentSpace I)
  have hF : ContinuousOn (fun p : TangentBundle I M => g.inner p.proj (Y p.proj) p.snd)
      ((fun p : TangentBundle I M => p.proj) ⁻¹' N) :=
    DifferentialGeometry.Geometry.Collapse.continuousOn_finiteInner_of_bundle (g := g) (b := fun p : TangentBundle I M => p.proj)
      (v := fun p => Y p.proj) (w := fun p => p.snd)
      (hY.comp hproj.continuousOn fun _ hp => hp) continuousOn_id
  have hFz : ContinuousAt (fun p : TangentBundle I M => g.inner p.proj (Y p.proj) p.snd)
      (⟨y, v⟩ : TangentBundle I M) :=
    hF.continuousAt ((hN.preimage hproj).mem_nhds hyN)
  refine ⟨v, hv, ?_⟩
  exact le_of_tendsto_of_tendsto' (hβ.comp hψ.tendsto_atTop) (hFz.tendsto.comp hlim)
    (fun j => hle (ψ j))

/-- **Upper semicontinuity.** A section continuous near `x` that pairs `< -c` with every direction
of `D x` does so with every direction of `D y`, `y` near `x`. -/
theorem eventually_forall_inner_lt
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (D : (x : M) → Set (TangentSpace I x)) (hDbdd : ∀ x, ∀ u ∈ D x, g.inner x u u ≤ 1)
    (hDclosed : ∀ (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M),
      (∀ k, (p k).snd ∈ D (p k).proj) → Tendsto p atTop (𝓝 pInf) → pInf.snd ∈ D pInf.proj)
    (Y : (x : M) → TangentSpace I x) {N : Set M} (hN : IsOpen N)
    (hY : ContinuousOn (fun x => (⟨x, Y x⟩ : TangentBundle I M)) N) {x : M} (hxN : x ∈ N)
    {c : ℝ} (hx : ∀ u ∈ D x, g.inner x (Y x) u < -c) :
    ∀ᶠ y in 𝓝 x, ∀ u ∈ D y, g.inner y (Y y) u < -c := by
  by_contra h
  rw [not_eventually] at h
  have h' : ∃ᶠ y in 𝓝 x, ∃ u ∈ D y, -c ≤ g.inner y (Y y) u :=
    h.mono fun y hy => by
      by_contra hne
      exact hy fun u hu => lt_of_not_ge fun hle => hne ⟨u, hu, hle⟩
  obtain ⟨ys, hys, hP⟩ := exists_seq_forall_of_frequently h'
  choose us hus hle using hP
  obtain ⟨u, hu, hcu⟩ := exists_mem_le_inner_of_tendsto g D hDbdd hDclosed Y hN hY hxN
    (q := fun k => (⟨ys k, us k⟩ : TangentBundle I M)) hus hys tendsto_const_nhds hle
  exact absurd (hx u hu) (not_lt.mpr hcu)

/-- **Uniform margin on compact sets.** A continuous section pairing `< -c` with every direction
over a compact set pairs `≤ -c'` there for some `c' > c`. -/
theorem exists_margin_of_isCompact
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (D : (x : M) → Set (TangentSpace I x)) (hDbdd : ∀ x, ∀ u ∈ D x, g.inner x u u ≤ 1)
    (hDclosed : ∀ (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M),
      (∀ k, (p k).snd ∈ D (p k).proj) → Tendsto p atTop (𝓝 pInf) → pInf.snd ∈ D pInf.proj)
    (Y : (x : M) → TangentSpace I x)
    (hY : Continuous (fun x => (⟨x, Y x⟩ : TangentBundle I M))) {K : Set M} (hK : IsCompact K)
    {c : ℝ} (hout : ∀ x ∈ K, ∀ u ∈ D x, g.inner x (Y x) u < -c) :
    ∃ c' > c, ∀ x ∈ K, ∀ u ∈ D x, g.inner x (Y x) u ≤ -c' := by
  by_contra h
  have hk : ∀ k : ℕ, ∃ x ∈ K, ∃ u ∈ D x, -(c + 1 / ((k : ℝ) + 1)) < g.inner x (Y x) u := by
    intro k
    by_contra hk
    apply h
    refine ⟨c + 1 / ((k : ℝ) + 1), lt_add_of_pos_right c (by positivity), fun x hx u hu => ?_⟩
    by_contra hlt
    exact hk ⟨x, hx, u, hu, lt_of_not_ge hlt⟩
  choose xs hxs us hus hlt using hk
  obtain ⟨y, hyK, φ, hφ, hlim⟩ := hK.tendsto_subseq hxs
  have hβ : Tendsto (fun j => -(c + 1 / ((φ j : ℝ) + 1))) atTop (𝓝 (-(c + 0))) :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).const_add c).neg
  rw [add_zero] at hβ
  obtain ⟨u, hu, hcu⟩ := exists_mem_le_inner_of_tendsto g D hDbdd hDclosed Y isOpen_univ
    hY.continuousOn (mem_univ y) (q := fun j => (⟨xs (φ j), us (φ j)⟩ : TangentBundle I M))
    (fun j => hus (φ j)) hlim hβ (fun j => (hlt (φ j)).le)
  exact absurd (hout y hyK u hu) (not_lt.mpr hcu)

/-- **S-PATCH.** Pointwise vectors `v x` on a closed set `A`, of `g`-length `< R` and pairing `< -c`
with every direction of `D x`, are replaced by ONE smooth field `V` with `g(V, V) < R²` everywhere
and pairing `< -c` with every direction on an open neighbourhood of `A`. -/
theorem exists_contMDiff_outward_field [SigmaCompactSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (D : (x : M) → Set (TangentSpace I x)) (hDbdd : ∀ x, ∀ u ∈ D x, g.inner x u u ≤ 1)
    (hDclosed : ∀ (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M),
      (∀ k, (p k).snd ∈ D (p k).proj) → Tendsto p atTop (𝓝 pInf) → pInf.snd ∈ D pInf.proj)
    {A : Set M} (hA : IsClosed A) {R c : ℝ} (hR : 0 < R) (v : (x : M) → TangentSpace I x)
    (hvR : ∀ x ∈ A, g.inner x (v x) (v x) < R ^ 2)
    (hvout : ∀ x ∈ A, ∀ u ∈ D x, g.inner x (v x) u < -c) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (V x) (V x) < R ^ 2) ∧
      ∃ O : Set M, IsOpen O ∧ A ⊆ O ∧ ∀ x ∈ O, ∀ u ∈ D x, g.inner x (V x) u < -c := by
  set t : (x : M) → Set (TangentSpace I x) := fun x =>
    {w | g.inner x w w < R ^ 2 ∧ (x ∈ A → ∀ u ∈ D x, g.inner x w u < -c)} with ht
  have hconv : ∀ x, Convex ℝ (t x) := by
    intro x w₁ hw₁ w₂ hw₂ α β hα hβ hαβ
    have hexp : g.inner x (α • w₁ + β • w₂) (α • w₁ + β • w₂) =
        α * α * g.inner x w₁ w₁ + α * β * g.inner x w₁ w₂ + β * α * g.inner x w₂ w₁ +
          β * β * g.inner x w₂ w₂ := by
      simp only [map_add, map_smul, add_apply,
        FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    have hsym : g.inner x w₂ w₁ = g.inner x w₁ w₂ := g.symm x w₂ w₁
    have hdiff : 0 ≤ g.inner x (w₁ - w₂) (w₁ - w₂) := inner_self_nonneg_finite g x _
    have hdexp : g.inner x (w₁ - w₂) (w₁ - w₂) =
        g.inner x w₁ w₁ - g.inner x w₁ w₂ - g.inner x w₂ w₁ + g.inner x w₂ w₂ := by
      simp only [map_sub, sub_apply]
      ring
    refine ⟨?_, fun hxA u hu => ?_⟩
    · rw [hexp, hsym]
      have hβ' : β = 1 - α := by linarith
      have hle : α * α * g.inner x w₁ w₁ + α * β * g.inner x w₁ w₂ +
          β * α * g.inner x w₁ w₂ + β * β * g.inner x w₂ w₂ ≤
          α * g.inner x w₁ w₁ + β * g.inner x w₂ w₂ := by
        rw [hdexp, hsym] at hdiff
        subst hβ'
        nlinarith [mul_nonneg hα hβ]
      exact hle.trans_lt (convex_combination_lt hα hβ hαβ hw₁.1 hw₂.1)
    · have hlin : g.inner x (α • w₁ + β • w₂) u = α * g.inner x w₁ u + β * g.inner x w₂ u := by
        simp only [map_add, map_smul, add_apply,
          FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [hlin]
      exact convex_combination_lt hα hβ hαβ (hw₁.2 hxA u hu) (hw₂.2 hxA u hu)
  have hloc : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ s : (x : M) → TangentSpace I x,
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => TotalSpace.mk' E x (s x)) U ∧ ∀ y ∈ U, s y ∈ t y := by
    intro x₀
    by_cases hx₀ : x₀ ∈ A
    · set e := trivializationAt E (TangentSpace I : M → Type _) x₀ with he
      set Y : (x : M) → TangentSpace I x := FiberBundle.extend E (v x₀) with hYdef
      have hYx₀ : Y x₀ = v x₀ := FiberBundle.extend_apply_self E (v x₀)
      have hYs : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x => TotalSpace.mk' E x (Y x)) e.baseSet := by
        rw [e.contMDiffOn_section_baseSet_iff]
        refine (contMDiffOn_const (c := (e ⟨x₀, v x₀⟩).2)).congr fun x hx => ?_
        change (e ⟨x, e.symm x (e ⟨x₀, v x₀⟩).2⟩).2 = (e ⟨x₀, v x₀⟩).2
        rw [e.apply_mk_symm hx]
      have hbase : e.baseSet ∈ 𝓝 x₀ :=
        e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀)
      have hYc : ContinuousOn (fun x => (⟨x, Y x⟩ : TangentBundle I M)) e.baseSet :=
        hYs.continuousOn
      have hpair := eventually_forall_inner_lt g D hDbdd hDclosed Y e.open_baseSet hYc
        (FiberBundle.mem_baseSet_trivializationAt' x₀) (c := c)
        (by rw [hYx₀]; exact hvout x₀ hx₀)
      have hnormc : ContinuousOn (fun x => g.inner x (Y x) (Y x)) e.baseSet :=
        DifferentialGeometry.Geometry.Collapse.continuousOn_finiteInner_of_bundle (g := g) (b := id) hYc hYc
      have hnorm : ∀ᶠ y in 𝓝 x₀, g.inner y (Y y) (Y y) < R ^ 2 :=
        (hnormc.continuousAt hbase).eventually (Iio_mem_nhds (by
          change g.inner x₀ (Y x₀) (Y x₀) < R ^ 2
          rw [hYx₀]; exact hvR x₀ hx₀))
      refine ⟨{y | y ∈ e.baseSet ∧ g.inner y (Y y) (Y y) < R ^ 2 ∧
        ∀ u ∈ D y, g.inner y (Y y) u < -c},
        (show ∀ᶠ y in 𝓝 x₀, y ∈ e.baseSet from hbase).and (hnorm.and hpair), Y,
        hYs.mono fun y hy => hy.1, fun y hy => ⟨hy.2.1, fun _ => hy.2.2⟩⟩
    · refine ⟨Aᶜ, hA.isOpen_compl.mem_nhds hx₀, fun x => (0 : TangentSpace I x),
        (Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)).contMDiffOn,
        fun y hy => ⟨?_, fun hyA => absurd hyA hy⟩⟩
      change g.inner y 0 0 < R ^ 2
      rw [map_zero]
      simpa using pow_pos hR 2
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I
    (n := (⊤ : ℕ∞)) (TangentSpace I : M → Type _) t hconv hloc
  have hsmooth : ContMDiff I I.tangent ∞ (fun x => (⟨x, s x⟩ : TangentBundle I M)) :=
    s.contMDiff
  refine ⟨fun x => s x, hsmooth, fun x => (hs x).1,
    interior {y | ∀ u ∈ D y, g.inner y (s y) u < -c}, isOpen_interior, fun x hx => ?_,
    fun x hx => interior_subset hx⟩
  rw [mem_interior_iff_mem_nhds]
  exact eventually_forall_inner_lt g D hDbdd hDclosed (fun y => s y) isOpen_univ
    hsmooth.continuous.continuousOn (mem_univ x) ((hs x).2 hx)

section Binding

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

/-- **S-PATCH bound to the minimizing directions** of a closed set `S` (CM3): pointwise strict
outward vectors on a closed set `A` give one smooth field, bounded by `R`, strictly outward against
ALL unit minimizing directions to `S` on an open neighbourhood of `A`. -/
theorem exists_contMDiff_outward_field_minimizingDirections [SigmaCompactSpace M]
    [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) {A : Set M} (hA : IsClosed A) {R c : ℝ} (hR : 0 < R)
    (v : (x : M) → TangentSpace I x) (hvR : ∀ x ∈ A, g.inner x (v x) (v x) < R ^ 2)
    (hvout : ∀ x ∈ A, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (v x) u < -c) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (V x) (V x) < R ^ 2) ∧
      ∃ O : Set M, IsOpen O ∧ A ⊆ O ∧
        ∀ x ∈ O, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (V x) u < -c :=
  exists_contMDiff_outward_field g (fun x => g.finiteMinimizingDirectionsTo S x)
    (fun _ _ hu => hu.1.le)
    (fun _ _ hp hlim => g.mem_finiteMinimizingDirectionsTo_of_tendsto hr hnorm hS hp hlim)
    hA hR v hvR hvout

end Binding

end DifferentialGeometry.Geometry.FiniteSoul
