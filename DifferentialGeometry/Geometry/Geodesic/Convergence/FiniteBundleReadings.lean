import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteMinimizingLimit

/-!
# Convergence in the tangent bundle read in one chart, for a finite-order limit metric

Tools for sequence arguments around LC50′ (lane F7-DOWN). Fix `x₀ : N` and its extended chart
`ψ = extChartAt I x₀`. A sequence `⟨x k, a k⟩` of the tangent bundle converges to `⟨x₀, α⟩` exactly
when `x k → x₀` and the chart readings `dψ (a k)` converge to `α` (the reading at the centre is the
identity). Consequences:

* `tendsto_inner_of_tendsto_tangentBundle`: the `C^{r+1}` metric `G` (`1 ≤ r`) is continuous along
  such pairs of sequences over the same base points;
* `tendsto_pullback_inner_of_tendsto`: for LFR14-shaped data (exhaustion and `C⁰` convergence of
  the pulled-back chart coefficients) and indices `σ k → ∞`,
  `g_{σ k}(d j (a k), d j (b k)) → G(α, β)`;
* `exists_subseq_tendsto_tangentBundle_of_inner_le`: `G`-bounded vectors over a convergent sequence of base
  points have a convergent subsequence in `TN`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

private local instance bundleReadingsDual : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

private local instance bundleReadingsBilinNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

omit [FiniteDimensional ℝ E] in
private theorem bundleReadings_two_le {r : ℕ∞} (hr : 1 ≤ r) : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
  have h1 : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
  calc (2 : ℕ∞ω) = 1 + 1 := one_add_one_eq_two.symm
    _ ≤ (r : ℕ∞ω) + 1 := add_le_add_left h1 1

omit [FiniteDimensional ℝ E] in
private theorem tendsto_bilin_apply₂ {X : Type*} {l : Filter X}
    {B : X → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E →L[ℝ] E →L[ℝ] ℝ} {u v : X → E} {u₀ v₀ : E}
    (hB : Tendsto B l (𝓝 B₀)) (hu : Tendsto u l (𝓝 u₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => B i (u i) (v i)) l (𝓝 (B₀ u₀ v₀)) := by
  have h1 : Tendsto (fun i => B i (u i)) l (𝓝 (B₀ u₀)) :=
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ)).continuous.tendsto
      (B₀, u₀)).comp (hB.prodMk_nhds hu)
  exact ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous.tendsto
    (B₀ u₀, v₀)).comp (h1.prodMk_nhds hv)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The reading of a tangent vector at the centre of its chart is the vector itself. -/
theorem mfderiv_extChartAt_self_apply (x₀ : N) (α : TangentSpace I x₀) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x₀ α = α := by
  rw [mfderiv_extChartAt_self]
  rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **Readings of a convergent sequence.** If `⟨x k, a k⟩ → ⟨x₀, α⟩` in `TN`, then `x k → x₀` and the
readings `d(extChartAt I x₀) (a k)` converge to `α`. -/
theorem tendsto_mfderiv_extChartAt_of_tendsto {X : Type*} {l : Filter X} {x : X → N} {x₀ : N}
    {a : ∀ k, TangentSpace I (x k)} {α : TangentSpace I x₀}
    (ha : Tendsto (fun k => (⟨x k, a k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, α⟩)) :
    Tendsto x l (𝓝 x₀) ∧
      Tendsto (fun k => mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (x k) (a k)) l (𝓝 α) := by
  have hx : Tendsto x l (𝓝 x₀) :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).tendsto _).comp ha
  refine ⟨hx, ?_⟩
  set v₀ : TangentBundle I N := ⟨x₀, 0⟩ with hv₀
  have hsrc : (⟨x₀, α⟩ : TangentBundle I N) ∈ (extChartAt I.tangent v₀).source := by
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
    exact mem_chart_source H x₀
  have hcont := (continuousAt_extChartAt' hsrc).tendsto.comp ha
  have hlim : (extChartAt I.tangent v₀ (⟨x₀, α⟩ : TangentBundle I N)).2 = α := by
    rw [extChartAt_tangent_apply_eq_mfderiv v₀ _ (mem_chart_source H x₀)]
    exact mfderiv_extChartAt_self_apply x₀ α
  have hsnd := (continuous_snd.tendsto _).comp hcont
  rw [hlim] at hsnd
  refine hsnd.congr' ?_
  filter_upwards [hx ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))] with k hk
  change (extChartAt I.tangent v₀ (⟨x k, a k⟩ : TangentBundle I N)).2 = _
  rw [extChartAt_tangent_apply_eq_mfderiv v₀ (⟨x k, a k⟩ : TangentBundle I N) hk]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **Convergence from the readings.** If `x k → x₀` and the readings
`d(extChartAt I x₀) (a k)` converge to `α`, then `⟨x k, a k⟩ → ⟨x₀, α⟩` in `TN`. -/
theorem tendsto_tangentBundle_of_tendsto_mfderiv_extChartAt {X : Type*} {l : Filter X}
    {x : X → N} {x₀ : N} {a : ∀ k, TangentSpace I (x k)} {α : TangentSpace I x₀}
    (hx : Tendsto x l (𝓝 x₀))
    (ha : Tendsto (fun k => mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (x k) (a k)) l (𝓝 α)) :
    Tendsto (fun k => (⟨x k, a k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, α⟩) := by
  set v₀ : TangentBundle I N := ⟨x₀, 0⟩ with hv₀
  set e := extChartAt I.tangent v₀ with he
  have hsrc0 : (⟨x₀, α⟩ : TangentBundle I N) ∈ e.source := by
    rw [he, extChartAt_source, TangentBundle.mem_chart_source_iff]
    exact mem_chart_source H x₀
  have he0 : e (⟨x₀, α⟩ : TangentBundle I N) = (extChartAt I x₀ x₀, α) := by
    rw [he, extChartAt_tangent_apply_eq_mfderiv v₀ _ (mem_chart_source H x₀),
      mfderiv_extChartAt_self_apply]
    rfl
  have hchart : ∀ᶠ k in l, x k ∈ (chartAt H x₀).source :=
    hx ((chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀))
  have hread : Tendsto (fun k => e (⟨x k, a k⟩ : TangentBundle I N)) l
      (𝓝 (e (⟨x₀, α⟩ : TangentBundle I N))) := by
    rw [he0]
    have h1 : Tendsto (fun k => extChartAt I x₀ (x k)) l (𝓝 (extChartAt I x₀ x₀)) :=
      (continuousAt_extChartAt x₀).tendsto.comp hx
    refine (h1.prodMk_nhds ha).congr' ?_
    filter_upwards [hchart] with k hk
    rw [he, extChartAt_tangent_apply_eq_mfderiv v₀ (⟨x k, a k⟩ : TangentBundle I N) hk]
    rfl
  have hsymm := (continuousAt_extChartAt_symm'' (e.map_source hsrc0)).tendsto.comp hread
  rw [e.left_inv hsrc0] at hsymm
  refine hsymm.congr' ?_
  filter_upwards [hchart] with k hk
  have hk' : (⟨x k, a k⟩ : TangentBundle I N) ∈ e.source := by
    rw [he, extChartAt_source, TangentBundle.mem_chart_source_iff]
    exact hk
  exact e.left_inv hk'

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Scaling along a convergent sequence: `⟨x k, c • a k⟩ → ⟨x₀, c • α⟩`. -/
theorem tendsto_tangentBundle_const_smul {X : Type*} {l : Filter X} {x : X → N} {x₀ : N}
    {a : ∀ k, TangentSpace I (x k)} {α : TangentSpace I x₀} (c : ℝ)
    (ha : Tendsto (fun k => (⟨x k, a k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, α⟩)) :
    Tendsto (fun k => (⟨x k, c • a k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, c • α⟩) := by
  obtain ⟨hx, hr⟩ := tendsto_mfderiv_extChartAt_of_tendsto ha
  refine tendsto_tangentBundle_of_tendsto_mfderiv_extChartAt hx ?_
  refine (hr.const_smul c).congr fun k => ?_
  exact (map_smul (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (x k)) c (a k)).symm

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Fibrewise difference along convergent sequences over the same base points:
`⟨x k, a k - b k⟩ → ⟨x₀, α - β⟩`. -/
theorem tendsto_tangentBundle_sub {X : Type*} {l : Filter X} {x : X → N} {x₀ : N}
    {a b : ∀ k, TangentSpace I (x k)} {α β : TangentSpace I x₀}
    (ha : Tendsto (fun k => (⟨x k, a k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, α⟩))
    (hb : Tendsto (fun k => (⟨x k, b k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, β⟩)) :
    Tendsto (fun k => (⟨x k, a k - b k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, α - β⟩) := by
  obtain ⟨hx, hra⟩ := tendsto_mfderiv_extChartAt_of_tendsto ha
  obtain ⟨-, hrb⟩ := tendsto_mfderiv_extChartAt_of_tendsto hb
  refine tendsto_tangentBundle_of_tendsto_mfderiv_extChartAt hx ?_
  refine (hra.sub hrb).congr fun k => ?_
  exact (map_sub (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (x k)) (a k) (b k)).symm

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Fibrewise sum along convergent sequences over the same base points. -/
theorem tendsto_tangentBundle_add {X : Type*} {l : Filter X} {x : X → N} {x₀ : N}
    {a b : ∀ k, TangentSpace I (x k)} {α β : TangentSpace I x₀}
    (ha : Tendsto (fun k => (⟨x k, a k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, α⟩))
    (hb : Tendsto (fun k => (⟨x k, b k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, β⟩)) :
    Tendsto (fun k => (⟨x k, a k + b k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, α + β⟩) := by
  obtain ⟨hx, hra⟩ := tendsto_mfderiv_extChartAt_of_tendsto ha
  obtain ⟨-, hrb⟩ := tendsto_mfderiv_extChartAt_of_tendsto hb
  refine tendsto_tangentBundle_of_tendsto_mfderiv_extChartAt hx ?_
  refine (hra.add hrb).congr fun k => ?_
  exact (map_add (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (x k)) (a k) (b k)).symm

omit [FiniteDimensional ℝ E] in
/-- **Continuity of a finite-order metric along the tangent bundle.** If `⟨x k, a k⟩ → ⟨x₀, α⟩`
and `⟨x k, b k⟩ → ⟨x₀, β⟩`, then `G(a k, b k) → G(α, β)`. -/
theorem tendsto_inner_of_tendsto_tangentBundle {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    {X : Type*} {l : Filter X} {x : X → N} {x₀ : N} {a b : ∀ k, TangentSpace I (x k)}
    {α β : TangentSpace I x₀}
    (ha : Tendsto (fun k => (⟨x k, a k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, α⟩))
    (hb : Tendsto (fun k => (⟨x k, b k⟩ : TangentBundle I N)) l (𝓝 ⟨x₀, β⟩)) :
    Tendsto (fun k => G.inner (x k) (a k) (b k)) l (𝓝 (G.inner x₀ α β)) := by
  obtain ⟨hx, hra⟩ := tendsto_mfderiv_extChartAt_of_tendsto ha
  obtain ⟨-, hrb⟩ := tendsto_mfderiv_extChartAt_of_tendsto hb
  set ψ := extChartAt I x₀ with hψ
  have hsrc : ∀ᶠ k in l, x k ∈ ψ.source :=
    hx ((isOpen_extChartAt_source x₀).mem_nhds (mem_extChartAt_source x₀))
  have hz : Tendsto (fun k => ψ (x k)) l (𝓝 (ψ x₀)) :=
    (continuousAt_extChartAt x₀).tendsto.comp hx
  have hc : ContinuousAt (chartCoeff G x₀) (ψ x₀) :=
    ((contDiffOn_chartCoeff G (bundleReadings_two_le hr) x₀).continuousOn).continuousAt
      ((isOpen_extChartAt_target x₀).mem_nhds (mem_extChartAt_target x₀))
  have hlim := tendsto_bilin_apply₂ (hc.tendsto.comp hz) hra hrb
  have h0 : chartCoeff G x₀ (ψ x₀) α β = G.inner x₀ α β := by
    have h := chartCoeff_mfderiv G x₀ (mem_extChartAt_source x₀) α β
    rwa [mfderiv_extChartAt_self_apply, mfderiv_extChartAt_self_apply] at h
  rw [← h0]
  refine hlim.congr' ?_
  filter_upwards [hsrc] with k hk
  exact chartCoeff_mfderiv G x₀ hk (a k) (b k)

section Approximants

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']

omit [FiniteDimensional ℝ E] in
/-- Pulled-back chart coefficients of `j ∘ ψ⁻¹` read `g(d j a, d j b)`. -/
theorem pullbackMetricCoefficients_extChartAt_apply (g : SmoothRiemannianMetric I M')
    {K : ℕ} (hK : 1 ≤ K) (j : PartialDiffeomorph I I N M' K) (x₀ : N) {y : N}
    (hy : y ∈ (extChartAt I x₀).source) (hyj : y ∈ j.source) (a b : TangentSpace I y) :
    pullbackMetricCoefficients g ((j : N → M') ∘ (extChartAt I x₀).symm) (extChartAt I x₀ y)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y a) (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) y b) =
    g.inner (j y) (mfderiv I I (j : N → M') y a) (mfderiv I I (j : N → M') y b) := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  set φ := extChartAt I x₀ with hφ
  have hyφ : φ.symm (φ y) = y := φ.left_inv hy
  have hjd : MDifferentiableAt I I (j : N → M') (φ.symm (φ y)) := by
    rw [hyφ]; exact j.mdifferentiableAt hK0 hyj
  have hφd : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ y) :=
    mdifferentiableAt_extChartAt_symm_of_mem x₀ (φ.map_source hy)
  have hca := mfderiv_comp_apply (φ y) hjd hφd (mfderiv I 𝓘(ℝ, E) φ y a)
  have hcb := mfderiv_comp_apply (φ y) hjd hφd (mfderiv I 𝓘(ℝ, E) φ y b)
  have hia : mfderiv 𝓘(ℝ, E) I φ.symm (φ y) (mfderiv I 𝓘(ℝ, E) φ y a) = a :=
    mfderiv_extChartAt_symm_apply_mfderiv x₀ hy a
  have hib : mfderiv 𝓘(ℝ, E) I φ.symm (φ y) (mfderiv I 𝓘(ℝ, E) φ y b) = b :=
    mfderiv_extChartAt_symm_apply_mfderiv x₀ hy b
  refine (pullbackMetricCoefficients_apply g _ _ _ _).trans ?_
  rw [hca, hcb, hia, hib]
  change g.inner (j (φ.symm (φ y))) (mfderiv I I (j : N → M') (φ.symm (φ y)) a)
    (mfderiv I I (j : N → M') (φ.symm (φ y)) b) = _
  rw [hyφ]

end Approximants

section Pullback

variable {M : ℕ → Type*} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

/-- **Transfer of the approximating metrics along `TN`.** For LFR14-shaped data (exhaustion and
`C⁰` convergence of the pulled-back chart coefficients) and indices `σ k → ∞`: if
`⟨x k, a k⟩ → ⟨x₀, α⟩` and `⟨x k, b k⟩ → ⟨x₀, β⟩`, then
`g_{σ k}(d j_{σ k} (a k), d j_{σ k} (b k)) → G(α, β)`. -/
theorem tendsto_pullback_inner_of_tendsto {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (g : ∀ i, SmoothRiemannianMetric I (M i)) {K : ℕ} (hK : 1 ≤ K)
    (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop) {x : ℕ → N} {x₀ : N}
    {a b : ∀ k, TangentSpace I (x k)} {α β : TangentSpace I x₀}
    (ha : Tendsto (fun k => (⟨x k, a k⟩ : TangentBundle I N)) atTop (𝓝 ⟨x₀, α⟩))
    (hb : Tendsto (fun k => (⟨x k, b k⟩ : TangentBundle I N)) atTop (𝓝 ⟨x₀, β⟩)) :
    Tendsto (fun k => (g (σ k)).inner (j (σ k) (x k))
      (mfderiv I I (j (σ k) : N → M (σ k)) (x k) (a k))
      (mfderiv I I (j (σ k) : N → M (σ k)) (x k) (b k))) atTop (𝓝 (G.inner x₀ α β)) := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨hx, hra⟩ := tendsto_mfderiv_extChartAt_of_tendsto ha
  obtain ⟨-, hrb⟩ := tendsto_mfderiv_extChartAt_of_tendsto hb
  set ψ := extChartAt I x₀ with hψ
  set z₀ := ψ x₀ with hz₀
  set c := chartCoeff G x₀ with hc
  set B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ := fun i =>
    pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ ψ.symm) with hB
  have hz₀t : z₀ ∈ ψ.target := mem_extChartAt_target x₀
  have htgt : ψ.target ∈ 𝓝 z₀ := (isOpen_extChartAt_target x₀).mem_nhds hz₀t
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp htgt
  have hconvL := hconv x₀ (closedBall z₀ ρ) (isCompact_closedBall z₀ ρ) hρsub
  have hsrc : ∀ᶠ k in atTop, x k ∈ ψ.source :=
    hx ((isOpen_extChartAt_source x₀).mem_nhds (mem_extChartAt_source x₀))
  have hzlim : Tendsto (fun k => ψ (x k)) atTop (𝓝 z₀) :=
    (continuousAt_extChartAt x₀).tendsto.comp hx
  have hzball : ∀ᶠ k in atTop, ψ (x k) ∈ closedBall z₀ ρ := hzlim (closedBall_mem_nhds z₀ hρ)
  have hjsrc : ∀ᶠ k in atTop, x k ∈ (j (σ k)).source := by
    filter_upwards [hσ.eventually (hexh _ hx.isCompact_insert_range)] with k hk
    exact hk (mem_insert_of_mem _ (mem_range_self k))
  have hccont : ContinuousAt c z₀ :=
    ((contDiffOn_chartCoeff G (bundleReadings_two_le hr) x₀).continuousOn).continuousAt htgt
  have hBlim : Tendsto (fun k => B (σ k) (ψ (x k))) atTop (𝓝 (c z₀)) := by
    refine (hccont.tendsto.comp hzlim).congr_dist ?_
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := hconvL (ε / 2) (half_pos hε)
    filter_upwards [hzball, hσ.eventually (eventually_ge_atTop k₀)] with k hk hik
    have h0 := hk₀ (σ k) hik 0 (Nat.zero_le _) _ hk
    rw [mapDerivNorm, norm_iteratedFDeriv_zero] at h0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm, norm_sub_rev]
    exact h0.trans_lt (half_lt_self hε)
  have hlim := tendsto_bilin_apply₂ hBlim hra hrb
  have h0 : c z₀ α β = G.inner x₀ α β := by
    have h := chartCoeff_mfderiv G x₀ (mem_extChartAt_source x₀) α β
    rwa [mfderiv_extChartAt_self_apply, mfderiv_extChartAt_self_apply] at h
  rw [← h0]
  refine hlim.congr' ?_
  filter_upwards [hsrc, hjsrc] with k hk hkj
  exact pullbackMetricCoefficients_extChartAt_apply (g (σ k)) hK (j (σ k)) x₀ hk hkj (a k) (b k)

end Pullback

/-- **`G`-bounded vectors have convergent subsequences.** Over a convergent sequence of base points
`x k → x₀`, vectors with `G(a k, a k) ≤ B` have a subsequence converging in `TN` to a vector over
`x₀`. -/
theorem exists_subseq_tendsto_tangentBundle_of_inner_le {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    {x : ℕ → N} {x₀ : N} (hx : Tendsto x atTop (𝓝 x₀)) (a : ∀ k, TangentSpace I (x k)) {B : ℝ}
    (hB : ∀ k, G.inner (x k) (a k) (a k) ≤ B) :
    ∃ α : TangentSpace I x₀, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => (⟨x (φ k), a (φ k)⟩ : TangentBundle I N)) atTop (𝓝 ⟨x₀, α⟩) := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  set ψ := extChartAt I x₀ with hψ
  set z₀ := ψ x₀ with hz₀
  set c := chartCoeff G x₀ with hc
  set ζ : ℕ → E := fun k => mfderiv I 𝓘(ℝ, E) ψ (x k) (a k) with hζ
  have hz₀t : z₀ ∈ ψ.target := mem_extChartAt_target x₀
  have htgt : ψ.target ∈ 𝓝 z₀ := (isOpen_extChartAt_target x₀).mem_nhds hz₀t
  have hsrc : ∀ᶠ k in atTop, x k ∈ ψ.source :=
    hx ((isOpen_extChartAt_source x₀).mem_nhds (mem_extChartAt_source x₀))
  have hzlim : Tendsto (fun k => ψ (x k)) atTop (𝓝 z₀) :=
    (continuousAt_extChartAt x₀).tendsto.comp hx
  have hccont : ContinuousAt c z₀ :=
    ((contDiffOn_chartCoeff G (bundleReadings_two_le hr) x₀).continuousOn).continuousAt htgt
  have hClim : Tendsto (fun k => c (ψ (x k))) atTop (𝓝 (c z₀)) := hccont.tendsto.comp hzlim
  have hco : IsCoercive (c z₀) :=
    DifferentialGeometry.Analysis.isCoercive_of_pos_diagonal _ fun _ hv =>
      chartCoeff_pos G x₀ hz₀t hv
  obtain ⟨κ, hκ, hκu⟩ := hco
  have hnear : ∀ᶠ k in atTop, ‖c (ψ (x k)) - c z₀‖ < κ / 2 := by
    filter_upwards [hClim (Metric.ball_mem_nhds (c z₀) (half_pos hκ))] with k hk
    rwa [mem_preimage, Metric.mem_ball, dist_eq_norm] at hk
  have hread : ∀ᶠ k in atTop, c (ψ (x k)) (ζ k) (ζ k) ≤ B := by
    filter_upwards [hsrc] with k hk
    rw [hζ, hc, chartCoeff_mfderiv G x₀ hk (a k) (a k)]
    exact hB k
  have hbound : ∀ᶠ k in atTop, ζ k ∈ closedBall (0 : E) (2 * |B| / κ + 1) := by
    filter_upwards [hread, hnear] with k hk hn
    rw [mem_closedBall, dist_zero_right]
    set C := c (ψ (x k))
    set u := ζ k
    have hle : |(C - c z₀) u u| ≤ ‖C - c z₀‖ * ‖u‖ * ‖u‖ :=
      (Real.norm_eq_abs _).symm.le.trans ((C - c z₀).le_opNorm₂ u u)
    have hsplit : C u u = c z₀ u u + (C - c z₀) u u := by
      simp only [sub_apply]; ring
    have h1 := hκu u
    have hu0 := norm_nonneg u
    have h2 : ‖C - c z₀‖ * ‖u‖ * ‖u‖ ≤ κ / 2 * ‖u‖ * ‖u‖ := by
      have := mul_nonneg hu0 hu0
      nlinarith
    have hsq : κ / 2 * (‖u‖ * ‖u‖) ≤ |B| := by
      nlinarith [abs_le.mp hle, le_abs_self B]
    have hsq' : ‖u‖ * ‖u‖ ≤ 2 * |B| / κ := by
      rw [le_div_iff₀ hκ]; nlinarith
    nlinarith [sq_nonneg (‖u‖ - 1 / 2), abs_nonneg B, div_nonneg (abs_nonneg B) hκ.le]
  obtain ⟨α, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : E) (2 * |B| / κ + 1)).tendsto_subseq'
    hbound.frequently
  refine ⟨α, φ, hφ, ?_⟩
  exact tendsto_tangentBundle_of_tendsto_mfderiv_extChartAt (hx.comp hφ.tendsto_atTop) hlim

end DifferentialGeometry.Geometry.Riemannian.Geodesic
