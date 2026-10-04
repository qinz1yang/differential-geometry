import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteDirectionNeighbourhood

/-!
# LFR18: every vertical source direction converges (modulo LFR14 data)

Blueprint LFR18 (`lem:collapse-finite-vertical-directions`, master207A:26261–26309); statement frozen
by lane F8-NEW2 (sheet-F8-NEW2.md §3). The product `N = ℝ × Z` enters through a metric isometry
`Φ : N ≃ᵢ ℓ²(ℝ × W)` (L-CONS (a) supplies one for the T0 limit), so no finite-order product metric
is needed; `x⁺ = (t + ℓ, z)` is `Φ⁻¹((Φ x).1 + ℓ, (Φ x).2)` and `∂_t` is the field `V`.

* `exists_vertical_field_eventually_inverse_directions_close` (**LFR18**): there is a continuous field
  `V` with `V x` the UNIQUE minimizing unit direction from `x` to `x⁺`, and for EVERY source
  minimizing direction `w` from `j i x` to `j i x⁺`, `‖d(j i)⁻¹ w − V x‖_G → 0` uniformly on `C`.

Route: existence by CM3.a, uniqueness by B2; continuity of `V` by `G`-unit compactness at moving
base points, continuity of `exp` and of the vertical shift (the closed graph for a moving
endpoint); the uniform norm statement by contradiction with the compact-endpoint LC50′ and the
continuity of `G` along `TN`.
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
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]
  [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]

/-- **LFR18: every vertical source direction converges** (modulo LFR14 data and a metric product
structure `Φ`). For LFR14-shaped data with `G` of class `C^{r+1}`, `2 ≤ r`, a metric isometry
`Φ : N ≃ᵢ ℓ²(ℝ × W)`, `ℓ > 0` and a compact `C`: there is a continuous field `V` (the blueprint's
`∂_t`) such that `V x` is the unique minimizing unit direction from `x` to
`x⁺ = Φ⁻¹((Φ x).1 + ℓ, (Φ x).2)`, and for every `ε > 0`, eventually, for every `x ∈ C` and EVERY
minimizing `g i`-direction `w` from `j i x` to `j i x⁺`, `‖d(j i)⁻¹ w − V x‖²_G < ε²`. -/
theorem exists_vertical_field_eventually_inverse_directions_close [∀ i, CompleteSpace (M i)]
    [CompleteSpace N] {r : ℕ∞} (hr : 2 ≤ r)
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
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {C : Set N} (hC : IsCompact C) :
    ∃ V : ∀ x : N, TangentSpace I x,
      (∀ x, G.finiteMinimizingDirectionsTo
        {Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x = {V x}) ∧
      Continuous (fun x => (⟨x, V x⟩ : TangentBundle I N)) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ C,
        ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i)
          {j i (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)))} (j i x),
          let u : TangentSpace I x := mfderiv I I ((j i).symm : M i → N) (j i x) w
          G.inner x (u - V x) (u - V x) < ε ^ 2 := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set sh : N → N := fun x => Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd)) with hsh
  have hshc : Continuous sh := (isometry_vertical_shift Φ ℓ).continuous
  have hne : ∀ x, (G.finiteMinimizingDirectionsTo {sh x} x).Nonempty := fun x =>
    (ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo_nonempty_isCompact G hr hGnorm
      isClosed_singleton (singleton_nonempty _) x).1
  choose V hV using hne
  have hVset : ∀ x, G.finiteMinimizingDirectionsTo {sh x} x = {V x} := fun x =>
    Set.eq_singleton_iff_unique_mem.mpr ⟨hV x, fun u hu =>
      eq_of_mem_finiteMinimizingDirectionsTo_vertical_shift hr1 G hGnorm Φ hℓ x hu (hV x)⟩
  have hdsh : ∀ x, dist x (sh x) = ℓ := fun x => by
    rw [hsh, dist_vertical_shift Φ ℓ x, abs_of_pos hℓ]
  have hmem : ∀ (x : N) (u : TangentSpace I x), G.inner x u u = 1 →
      G.expMap (⟨x, ℓ • u⟩ : TangentBundle I N) = sh x → u = V x := by
    intro x u hu hend
    have h : u ∈ G.finiteMinimizingDirectionsTo {sh x} x :=
      ⟨hu, by rw [Metric.infDist_singleton, hdsh]; exact hend⟩
    rw [hVset x] at h
    exact h
  have hVend : ∀ x, G.expMap (⟨x, ℓ • V x⟩ : TangentBundle I N) = sh x := fun x => by
    have h := (hV x).2
    rwa [Metric.infDist_singleton, hdsh, mem_singleton_iff] at h
  have hexpc : Continuous G.expMap :=
    ContMDiffRiemannianMetric.continuous_expMap_of_completeSpace G hr hGnorm
  have hseq : ∀ (y : ℕ → N) (x : N), Tendsto y atTop (𝓝 x) →
      Tendsto (fun k => (⟨y k, V (y k)⟩ : TangentBundle I N)) atTop (𝓝 ⟨x, V x⟩) := by
    intro y x hy
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨α, φ, hφ, hlim⟩ := exists_subseq_tendsto_tangentBundle_of_inner_le hr1 G (hy.comp hns)
      (fun k => V (y (ns k))) (B := 1) (fun k => ((hV _).1).le)
    refine ⟨φ, ?_⟩
    have hunit : G.inner x α α = 1 := by
      have h := tendsto_inner_of_tendsto_tangentBundle hr1 G hlim hlim
      exact tendsto_nhds_unique h (tendsto_const_nhds.congr fun k => ((hV _).1).symm)
    have hend : G.expMap (⟨x, ℓ • α⟩ : TangentBundle I N) = sh x := by
      have h1 := (hexpc.tendsto _).comp (tendsto_tangentBundle_const_smul ℓ hlim)
      have h2 : Tendsto (fun k => sh (y (ns (φ k)))) atTop (𝓝 (sh x)) :=
        (hshc.tendsto x).comp ((hy.comp hns).comp hφ.tendsto_atTop)
      exact tendsto_nhds_unique h1 (h2.congr fun k => (hVend _).symm)
    rw [hmem x α hunit hend] at hlim
    exact hlim
  have hVc : Continuous (fun x => (⟨x, V x⟩ : TangentBundle I N)) :=
    continuous_iff_seqContinuous.mpr fun {y x} hy => hseq y x hy
  refine ⟨V, hVset, hVc, fun ε hε => ?_⟩
  by_contra hbad
  rw [Filter.not_eventually] at hbad
  obtain ⟨ψ, hψ, hψbad⟩ := Filter.extraction_of_frequently_atTop hbad
  simp only [not_forall, not_lt, exists_prop] at hψbad
  choose x hxC w hw hwbad using hψbad
  have hψt := hψ.tendsto_atTop
  obtain ⟨yInf, -, v, hvC, hvdir, -, φ, -, hy, hlim⟩ :=
    exists_subseq_minimizing_direction_limit_finite_of_isCompact (M := fun k => M (ψ k)) hr1 G
      hGnorm (fun k => g (ψ k)) (fun k => hmetric (ψ k)) hK q (fun k => j (ψ k))
      (fun C hC => hψt.eventually (hexh C hC))
      (fun z L hL hLt => (hconv z L hL hLt).comp_subseq hψ)
      (fun R ε hε => hψt.eventually (hdist R ε hε))
      (fun a b ha hab => hψt.eventually (hcover a b ha hab))
      hC x hxC (hC.image hshc) (fun k => sh (x k)) (fun k => mem_image_of_mem sh (hxC k)) w hw
  have hxlim : Tendsto (fun k => x (φ k)) atTop (𝓝 v.proj) :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).tendsto v).comp hlim
  have hyeq : yInf = sh v.proj := tendsto_nhds_unique hy ((hshc.tendsto _).comp hxlim)
  rw [hyeq, hVset, mem_singleton_iff] at hvdir
  have hlim' : Tendsto (fun k => (⟨x (φ k), mfderiv I I ((j (ψ (φ k))).symm : M (ψ (φ k)) → N)
      (j (ψ (φ k)) (x (φ k))) (w (φ k))⟩ : TangentBundle I N)) atTop (𝓝 ⟨v.proj, V v.proj⟩) := by
    rw [← hvdir]
    exact hlim
  have hVlim : Tendsto (fun k => (⟨x (φ k), V (x (φ k))⟩ : TangentBundle I N)) atTop
      (𝓝 ⟨v.proj, V v.proj⟩) := (hVc.tendsto v.proj).comp hxlim
  have hsub := tendsto_tangentBundle_sub hlim' hVlim
  have hin := tendsto_inner_of_tendsto_tangentBundle hr1 G hsub hsub
  simp only [sub_self, map_zero] at hin
  obtain ⟨k, hk⟩ := (hin.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε ^ 2))).exists
  exact absurd hk (not_lt.mpr (hwbad (φ k)))

end DifferentialGeometry.Geometry.Riemannian.Geodesic
