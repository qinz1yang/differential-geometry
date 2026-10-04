import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteMinimizingLimit
import DifferentialGeometry.Geometry.Collapse.SublevelCore.FiniteUniformCollar

/-!
# The uniform source collar for a finite-order limit (B4 and LC51′)

LC51 (A:22607–22660, X84/LC5X's `exists_collar_constants_core_isotopy`) needs, besides LC49, the
transfer of a model directional margin to EVERY source minimizing direction on one tail; its proof
uses LC50. For the finite-order limit of LFR14 this is done here with LC50′
(`exists_subseq_inward_direction_limit_finite`). Lane F8-NEW2, task 4.

* `pullbackMetricCoefficients_extChartAt_mfderiv`: the pulled-back chart coefficients of `j` read
  the source metric on pushed vectors.
* `tendsto_pushforward_inner_of_tendsto`: if `⟨x k, ξ k⟩ → ⟨x₀, ξ₀⟩` and `⟨x k, ζ k⟩ → ⟨x₀, ζ₀⟩` in
  `TN`, then `g_k(dj_k ξ_k, dj_k ζ_k) → G(ξ₀, ζ₀)` (only the `C⁰` coefficient convergence is used).
* `eventually_pushforward_inner_le_of_finite_limit` (**B4**): a field with `G(V, v) ≤ -a` for
  every limit minimizing direction to `n` and `G(V, V) ≤ B²` along a compact `C` has, on one tail,
  `|(j_i)_* V| ≤ 2B` and `g_i((j_i)_* V, w) ≤ -α` for EVERY `α < a` and EVERY source minimizing
  direction `w` to `j_i n`.
* `exists_uniform_collar_finite_limit` (**LC51′**, collar half): LC49′ followed by B4 for a core
  `D` with `B̄(n, 1/2) ⊆ int D`, `D ⊆ B(n, 2)` and strict negativity on `∂D`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian.Geodesic

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

private local instance collarTransferDual : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

private local instance collarTransferBilinNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

omit [FiniteDimensional ℝ E] in
private theorem collarTransfer_two_le {r : ℕ∞} (hr : 1 ≤ r) : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
  have h1 : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  calc (2 : ℕ∞ω) = 1 + 1 := one_add_one_eq_two.symm
    _ ≤ (r : ℕ∞ω) + 1 := add_le_add_left h1 1

omit [FiniteDimensional ℝ E] in
private theorem collarTransfer_bilin {X : Type*} {l : Filter X}
    {B : X → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ} {u w : X → E} {u₀ w₀ : E}
    (hB : Tendsto B l (𝓝 B₀)) (hu : Tendsto u l (𝓝 u₀)) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun i => B i (u i) (w i)) l (𝓝 (B₀ u₀ w₀)) := by
  have h1 : Tendsto (fun i => B i (u i)) l (𝓝 (B₀ u₀)) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ)).continuous.tendsto
      (B₀, u₀)).comp (hB.prodMk_nhds hu)
  exact ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous.tendsto
    (B₀ u₀, w₀)).comp (h1.prodMk_nhds hw)

section Approximant

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']

omit [FiniteDimensional ℝ E] in
/-- The pulled-back chart coefficients of `j` at the chart reading of `y` evaluate the source
metric on the pushed vectors. -/
theorem pullbackMetricCoefficients_extChartAt_mfderiv (g : SmoothRiemannianMetric I M')
    {K : ℕ} (hK : 1 ≤ K) (j : PartialDiffeomorph I I N M' K) (x₀ : N) {y : N}
    (hy : y ∈ (extChartAt I x₀).source) (hyj : y ∈ j.source) (ξ ζ : TangentSpace I y) :
    pullbackMetricCoefficients g ((j : N → M') ∘ (extChartAt I x₀).symm) (extChartAt I x₀ y)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y ξ) (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y ζ) =
    g.inner (j y) (mfderiv I I (j : N → M') y ξ) (mfderiv I I (j : N → M') y ζ) := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hyφ : (extChartAt I x₀).symm (extChartAt I x₀ y) = y := (extChartAt I x₀).left_inv hy
  have hjd : MDifferentiableAt I I (j : N → M') ((extChartAt I x₀).symm (extChartAt I x₀ y)) := by
    rw [hyφ]; exact j.mdifferentiableAt hK0 hyj
  have hφd : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ y) :=
    mdifferentiableAt_extChartAt_symm_of_mem x₀ ((extChartAt I x₀).map_source hy)
  have hcξ := mfderiv_comp_apply (extChartAt I x₀ y) hjd hφd
    (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y ξ)
  have hcζ := mfderiv_comp_apply (extChartAt I x₀ y) hjd hφd
    (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y ζ)
  refine (pullbackMetricCoefficients_apply g _ _ _ _).trans ?_
  rw [hcξ, hcζ, mfderiv_extChartAt_symm_apply_mfderiv x₀ hy ξ,
    mfderiv_extChartAt_symm_apply_mfderiv x₀ hy ζ]
  change g.inner (j ((extChartAt I x₀).symm (extChartAt I x₀ y)))
    (mfderiv I I (j : N → M') ((extChartAt I x₀).symm (extChartAt I x₀ y)) ξ)
    (mfderiv I I (j : N → M') ((extChartAt I x₀).symm (extChartAt I x₀ y)) ζ) = _
  rw [hyφ]

end Approximant

/-- **Pushed inner products converge.** Under LFR14-shaped chart convergence (`C⁰` suffices),
if `⟨x k, ξ k⟩ → ⟨x₀, ξ₀⟩` and `⟨x k, ζ k⟩ → ⟨x₀, ζ₀⟩` in `TN` with `x k` in a compact set, then
`g_k(dj_k ξ_k, dj_k ζ_k) → G(ξ₀, ζ₀)`. -/
theorem tendsto_pushforward_inner_of_tendsto {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (g : ∀ i, SmoothRiemannianMetric I (M i)) {K : ℕ} (hK : 1 ≤ K)
    (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 0
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    {C : Set N} (hC : IsCompact C) (x : ℕ → N) (hx : ∀ k, x k ∈ C)
    (ξ ζ : ∀ k, TangentSpace I (x k)) (x₀ : N) (ξ₀ ζ₀ : TangentSpace I x₀)
    (hξ : Tendsto (fun k => (⟨x k, ξ k⟩ : TangentBundle I N)) atTop
      (𝓝 (⟨x₀, ξ₀⟩ : TangentBundle I N)))
    (hζ : Tendsto (fun k => (⟨x k, ζ k⟩ : TangentBundle I N)) atTop
      (𝓝 (⟨x₀, ζ₀⟩ : TangentBundle I N))) :
    Tendsto (fun k => (g k).inner (j k (x k)) (mfderiv I I (j k : N → M k) (x k) (ξ k))
      (mfderiv I I (j k : N → M k) (x k) (ζ k))) atTop (𝓝 (G.inner x₀ ξ₀ ζ₀)) := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  have hproj := FiberBundle.continuous_proj E (TangentSpace I : N → Type _)
  have hxlim : Tendsto x atTop (𝓝 x₀) := (hproj.tendsto _).comp hξ
  have hxsrc : ∀ᶠ k in atTop, x k ∈ (chartAt H x₀).source :=
    hxlim ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))
  have hjsrc : ∀ᶠ k in atTop, x k ∈ (j k).source := by
    filter_upwards [hexh C hC] with k hk
    exact hk (hx k)
  -- the readings in the tangent chart at `⟨x₀, 0⟩`
  have hread : ∀ (p₀ : TangentSpace I x₀) (p : ∀ k, TangentSpace I (x k)),
      Tendsto (fun k => (⟨x k, p k⟩ : TangentBundle I N)) atTop
        (𝓝 (⟨x₀, p₀⟩ : TangentBundle I N)) →
      Tendsto (fun k => mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (x k) (p k)) atTop
        (𝓝 (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x₀ p₀)) := by
    intro p₀ p hp
    have hsrc : (⟨x₀, p₀⟩ : TangentBundle I N) ∈
        (extChartAt I.tangent (⟨x₀, 0⟩ : TangentBundle I N)).source := by
      rw [extChartAt_source]
      exact (TangentBundle.mem_chart_source_iff _ _).mpr (mem_chart_source H x₀)
    have h := (continuous_snd.tendsto _).comp ((continuousAt_extChartAt' hsrc).tendsto.comp hp)
    rw [extChartAt_tangent_apply_eq_mfderiv (⟨x₀, 0⟩ : TangentBundle I N) ⟨x₀, p₀⟩
      (mem_chart_source H x₀)] at h
    refine h.congr' ?_
    filter_upwards [hxsrc] with k hk
    simp only [Function.comp_apply]
    rw [extChartAt_tangent_apply_eq_mfderiv (⟨x₀, 0⟩ : TangentBundle I N) ⟨x k, p k⟩ hk]
  -- the coefficients at the moving reading converge to the limit coefficients
  have hz₀t : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target := mem_extChartAt_target x₀
  have htgt : (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ x₀) :=
    (isOpen_extChartAt_target x₀).mem_nhds hz₀t
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp htgt
  have hconvL := hconv x₀ (closedBall (extChartAt I x₀ x₀) ρ) (isCompact_closedBall _ ρ) hρsub
  have hzlim : Tendsto (fun k => extChartAt I x₀ (x k)) atTop (𝓝 (extChartAt I x₀ x₀)) :=
    (continuousAt_extChartAt x₀).tendsto.comp hxlim
  have hzball : ∀ᶠ k in atTop, extChartAt I x₀ (x k) ∈ closedBall (extChartAt I x₀ x₀) ρ :=
    hzlim (closedBall_mem_nhds _ hρ)
  have hccont : ContinuousAt (chartCoeff G x₀) (extChartAt I x₀ x₀) :=
    ((contDiffOn_chartCoeff G (collarTransfer_two_le hr) x₀).continuousOn).continuousAt htgt
  have hBlim : Tendsto (fun k => pullbackMetricCoefficients (g k)
      ((j k : N → M k) ∘ (extChartAt I x₀).symm) (extChartAt I x₀ (x k))) atTop
      (𝓝 (chartCoeff G x₀ (extChartAt I x₀ x₀))) := by
    refine (hccont.tendsto.comp hzlim).congr_dist ?_
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := hconvL (ε / 2) (half_pos hε)
    filter_upwards [hzball, eventually_ge_atTop k₀] with k hk hkk
    have h0 := hk₀ k hkk 0 (Nat.zero_le _) _ hk
    rw [mapDerivNorm, norm_iteratedFDeriv_zero] at h0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm, norm_sub_rev]
    exact h0.trans_lt (half_lt_self hε)
  have hlim := collarTransfer_bilin hBlim (hread ξ₀ ξ hξ) (hread ζ₀ ζ hζ)
  rw [chartCoeff_mfderiv G x₀ (mem_extChartAt_source x₀) ξ₀ ζ₀] at hlim
  refine hlim.congr' ?_
  filter_upwards [hxsrc, hjsrc] with k hk hkj
  exact pullbackMetricCoefficients_extChartAt_mfderiv (g k) hK (j k) x₀
    (by rwa [extChartAt_source]) hkj (ξ k) (ζ k)


section Limit

variable [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsRiemannianManifold I N] [∀ i, CompleteSpace (M i)]

/-- **B4: pushed-field margin and norm bound (the LC50′ step of LC51).** LFR14-shaped data. A field
`V`, continuous along the compact `C`, with `G(V, v) ≤ -a` for every limit minimizing direction `v`
to `n` and `G(V, V) ≤ B²` on `C`. Then for every `α < a`, on one tail, the pushed fields satisfy
`g_i((j_i)_* V, (j_i)_* V) ≤ (2B)²` and `g_i((j_i)_* V, w) ≤ -α` for EVERY source minimizing unit
direction `w` from `j_i x` to `j_i n`. -/
theorem eventually_pushforward_inner_le_of_finite_limit {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {C : Set N} (hC : IsCompact C) (n : N) (V : ∀ x : N, TangentSpace I x)
    (hV : ContinuousOn (fun x => (⟨x, V x⟩ : TangentBundle I N)) C) {a B : ℝ} (hB : 0 < B)
    (hneg : ∀ x ∈ C, ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x, G.inner x (V x) v ≤ -a)
    (hVB : ∀ x ∈ C, G.inner x (V x) (V x) ≤ B ^ 2) {α : ℝ} (hα : α < a) :
    ∀ᶠ i in atTop, ∀ x ∈ C,
      (g i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x))
          (mfderiv I I (j i : N → M i) x (V x)) ≤ (2 * B) ^ 2 ∧
      ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) {j i n} (j i x),
        (g i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x)) w ≤ -α := by
  have hK1 : 1 ≤ K := by omega
  have hproj := FiberBundle.continuous_proj E (TangentSpace I : N → Type _)
  have hVlim : ∀ (y : ℕ → N) (y₀ : N), y₀ ∈ C → (∀ k, y k ∈ C) → Tendsto y atTop (𝓝 y₀) →
      Tendsto (fun k => (⟨y k, V (y k)⟩ : TangentBundle I N)) atTop
        (𝓝 (⟨y₀, V y₀⟩ : TangentBundle I N)) := fun y y₀ hy₀ hy hylim =>
    (hV y₀ hy₀).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hylim, Eventually.of_forall hy⟩)
  -- the norm bound
  have hnorm : ∀ᶠ i in atTop, ∀ x ∈ C,
      (g i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x))
        (mfderiv I I (j i : N → M i) x (V x)) ≤ (2 * B) ^ 2 := by
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    obtain ⟨ψ, hψ, hbad⟩ := Filter.extraction_of_frequently_atTop hcon
    have hbad' : ∀ k, ∃ x ∈ C, (2 * B) ^ 2 < (g (ψ k)).inner (j (ψ k) x)
        (mfderiv I I (j (ψ k) : N → M (ψ k)) x (V x))
        (mfderiv I I (j (ψ k) : N → M (ψ k)) x (V x)) := by
      intro k
      have h := hbad k
      push Not at h
      exact h
    choose y hyC hy using hbad'
    obtain ⟨y₀, hy₀C, φ, hφ, hylim⟩ := hC.tendsto_subseq hyC
    have hψφ := (hψ.comp hφ).tendsto_atTop
    have hL := tendsto_pushforward_inner_of_tendsto (M := fun k => M (ψ (φ k))) hr G
      (fun k => g (ψ (φ k))) hK1 (fun k => j (ψ (φ k)))
      (fun C' hC' => hψφ.eventually (hexh C' hC'))
      (fun z L hL hLt => ((hconv z L hL hLt).comp_subseq (hψ.comp hφ)).mono_order (by norm_num))
      hC (fun k => y (φ k)) (fun k => hyC (φ k)) (fun k => V (y (φ k))) (fun k => V (y (φ k)))
      y₀ (V y₀) (V y₀) (hVlim _ y₀ hy₀C (fun k => hyC (φ k)) hylim)
      (hVlim _ y₀ hy₀C (fun k => hyC (φ k)) hylim)
    have hge : (2 * B) ^ 2 ≤ G.inner y₀ (V y₀) (V y₀) :=
      ge_of_tendsto hL (Eventually.of_forall fun k => (hy (φ k)).le)
    have hle := hVB y₀ hy₀C
    nlinarith
  -- the directional margin
  have hdir : ∀ᶠ i in atTop, ∀ x ∈ C,
      ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) {j i n} (j i x),
        (g i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x)) w ≤ -α := by
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    obtain ⟨ψ, hψ, hbad⟩ := Filter.extraction_of_frequently_atTop hcon
    have hbad' : ∀ k, ∃ x ∈ C, ∃ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo
        (g (ψ k)) {j (ψ k) n} (j (ψ k) x),
        -α < (g (ψ k)).inner (j (ψ k) x) (mfderiv I I (j (ψ k) : N → M (ψ k)) x (V x)) w := by
      intro k
      have h := hbad k
      push Not at h
      exact h
    choose y hyC w hw hlt using hbad'
    have hψt := hψ.tendsto_atTop
    obtain ⟨v, hvC, hvdir, -, φ, hφ, hlim⟩ :=
      exists_subseq_inward_direction_limit_finite (M := fun k => M (ψ k)) hr G hGnorm
        (fun k => g (ψ k)) (fun k => hmetric (ψ k)) hK q (fun k => j (ψ k))
        (fun C' hC' => hψt.eventually (hexh C' hC'))
        (fun z L hL hLt => (hconv z L hL hLt).comp_subseq hψ)
        (fun R ε hε => hψt.eventually (hdist R ε hε))
        (fun a' b' ha' hab' => hψt.eventually (hcover a' b' ha' hab'))
        hC y hyC n w hw
    have hψφ := (hψ.comp hφ).tendsto_atTop
    have hylim : Tendsto (fun k => y (φ k)) atTop (𝓝 v.proj) := (hproj.tendsto v).comp hlim
    have hL := tendsto_pushforward_inner_of_tendsto (M := fun k => M (ψ (φ k))) hr G
      (fun k => g (ψ (φ k))) hK1 (fun k => j (ψ (φ k)))
      (fun C' hC' => hψφ.eventually (hexh C' hC'))
      (fun z L hL hLt => ((hconv z L hL hLt).comp_subseq (hψ.comp hφ)).mono_order (by norm_num))
      hC (fun k => y (φ k)) (fun k => hyC (φ k)) (fun k => V (y (φ k)))
      (fun k => mfderiv I I ((j (ψ (φ k))).symm : M (ψ (φ k)) → N) (j (ψ (φ k)) (y (φ k)))
        (w (φ k)))
      v.proj (V v.proj) v.snd (hVlim _ v.proj hvC (fun k => hyC (φ k)) hylim) hlim
    have hge : -α ≤ G.inner v.proj (V v.proj) v.snd := by
      refine ge_of_tendsto hL ?_
      filter_upwards [hψφ.eventually (hexh C hC)] with k hk
      have hsrc : y (φ k) ∈ (j (ψ (φ k))).source := hk (hyC (φ k))
      rw [mfderiv_apply_mfderiv_symm_of_mem_source hK1 (j (ψ (φ k))) hsrc (w (φ k))]
      exact (hlt (φ k)).le
    have := hneg v.proj hvC v.snd hvdir
    linarith
  filter_upwards [hnorm, hdir] with i hi hi'
  exact fun x hx => ⟨hi x hx, hi' x hx⟩

/-- **LC51′ (collar half) for a finite-order limit.** LFR14-shaped data with `2 ≤ r`. For a
compact model core `D` with `B̄(n, 1/2) ⊆ int D`, `D ⊆ B(n, 2)` and a field `V`, continuous on an
open `O ⊇ ∂D`, strictly negative against every limit minimizing direction to `n` along `∂D`,
there are `α, B > 0` and an open collar `U ⊇ ∂D` with compact closure in `(B(n, 3) ∖ {n}) ∩ O`
such that, on one tail, `|(j_i)_* V| ≤ 2B` and `g_i((j_i)_* V, w) ≤ -α` on `closure U` for EVERY
source minimizing unit direction `w` to `j_i n`. -/
theorem exists_uniform_collar_finite_limit {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    (n : N) {D : Set N} (hDc : IsCompact D) (hin : closedBall n (1 / 2) ⊆ interior D)
    (hout : D ⊆ ball n 2) {O : Set N} (hO : IsOpen O) (hDO : frontier D ⊆ O)
    (V : (x : N) → TangentSpace I x)
    (hV : ContinuousOn (fun x => (⟨x, V x⟩ : TangentBundle I N)) O)
    (hneg : ∀ x ∈ frontier D, ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (V x) v < 0) :
    ∃ α B : ℝ, 0 < α ∧ 0 < B ∧ ∃ U : Set N, IsOpen U ∧ frontier D ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ (ball n 3 \ {n}) ∩ O ∧
      ∀ᶠ i in atTop, ∀ x ∈ closure U,
        (g i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x))
            (mfderiv I I (j i : N → M i) x (V x)) ≤ (2 * B) ^ 2 ∧
        ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) {j i n} (j i x),
          (g i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x)) w ≤ -α := by
  obtain ⟨α, B, hα, hB, U, hUo, hDU, hcpt, hsub, hU⟩ :=
    exists_uniform_collar_of_frontier_finite hr G hGnorm n hDc hin hout hO hDO V hV hneg
  refine ⟨α, B, hα, hB, U, hUo, hDU, hcpt, hsub, ?_⟩
  exact eventually_pushforward_inner_le_of_finite_limit (one_le_two.trans hr) G hGnorm g hmetric
    hK q j hexh hconv hdist hcover hcpt n V (hV.mono fun x hx => (hsub hx).2) hB
    (fun x hx => (hU x hx).2) (fun x hx => (hU x hx).1) (by linarith : α < 2 * α)

end Limit

end DifferentialGeometry.Geometry.Collapse
