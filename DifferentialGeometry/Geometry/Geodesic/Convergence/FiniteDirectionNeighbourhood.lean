import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteBundleReadings
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalSegment

/-!
# LFR18, kernel and uniqueness: all-direction convergence and the vertical direction

Blueprint LFR18 (master207A:26261–26309), statements frozen by lane F8-NEW2 (sheet-F8-NEW2.md §3).

* `eventually_inverse_minimizing_directions_mem_nhds_finite` (**B1**, LFR18-K): for LFR14-shaped data
  (LC50′'s hypotheses), a compact `C`, an endpoint map `e` continuous on `C` and an open set `O` of
  `TN` containing every limit minimizing direction from `x ∈ C` to `e x`, eventually EVERY inverse
  lift `d(j i)⁻¹ w` of EVERY source minimizing direction from `j i x` to `j i (e x)` lies in `O`,
  uniformly over `x ∈ C`. By contradiction with the compact-endpoint LC50′.
* `eq_of_expMap_smul_eq_on_Icc`: two vectors at `x` whose radial geodesics agree on `[0, δ]` agree
  (uniform chart expansion of the flow, CM3).
* `eq_of_mem_finiteMinimizingDirectionsTo_vertical_shift` (**B2**, LFR18-U): in a metric product
  `ℓ²(ℝ × W)` the minimizing unit direction from `x` to its vertical shift by `ℓ > 0` is unique: both
  radial geodesics are segments (`dist_expMap_smul_eq_of_endpoint`), hence vertical
  (`eq_vertical_of_isometry_segment`), hence equal on `[0, ℓ]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

/-- **Radial geodesics determine their initial vector.** If `exp_x(s u) = exp_x(s u')` for all
`s ∈ [0, δ]`, `δ > 0`, then `u = u'`. -/
theorem eq_of_expMap_smul_eq_on_Icc {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    {x : N} {u u' : TangentSpace I x} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ s ∈ Icc 0 δ, G.expMap (⟨x, s • u⟩ : TangentBundle I N) =
      G.expMap (⟨x, s • u'⟩ : TangentBundle I N)) :
    u = u' := by
  obtain ⟨a, rfl⟩ : ∃ a : E, a = u := ⟨u, rfl⟩
  obtain ⟨a', rfl⟩ : ∃ a' : E, a' = u' := ⟨u', rfl⟩
  by_contra hne
  have hd : 0 < ‖a - a'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set ε := ‖a - a'‖ / 4 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨W, hW, δ₁, hδ₁, hexp₁⟩ :=
    ContMDiffRiemannianMetric.exists_nhds_chart_geodesicFlow_expansion G hr
      (⟨x, a⟩ : TangentBundle I N) hε0
  obtain ⟨W', hW', δ₂, hδ₂, hexp₂⟩ :=
    ContMDiffRiemannianMetric.exists_nhds_chart_geodesicFlow_expansion G hr
      (⟨x, a'⟩ : TangentBundle I N) hε0
  set s := min δ (min δ₁ δ₂) with hs
  have hs0 : 0 < s := lt_min hδ (lt_min hδ₁ hδ₂)
  have hs1 : s ∈ Icc (0 : ℝ) δ₁ := ⟨hs0.le, (min_le_right _ _).trans (min_le_left _ _)⟩
  have hs2 : s ∈ Icc (0 : ℝ) δ₂ := ⟨hs0.le, (min_le_right _ _).trans (min_le_right _ _)⟩
  have hsδ : s ∈ Icc (0 : ℝ) δ := ⟨hs0.le, min_le_left _ _⟩
  obtain ⟨hdom₁, -, hb₁⟩ := hexp₁ _ (mem_of_mem_nhds hW) s hs1
  obtain ⟨hdom₂, -, hb₂⟩ := hexp₂ _ (mem_of_mem_nhds hW') s hs2
  have hr₁ : (trivializationAt E (TangentSpace I) x (⟨x, a⟩ : TangentBundle I N)).2 = a :=
    ContMDiffRiemannianMetric.trivializationAt_mk_self_snd x a
  have hr₂ : (trivializationAt E (TangentSpace I) x (⟨x, a'⟩ : TangentBundle I N)).2 = a' :=
    ContMDiffRiemannianMetric.trivializationAt_mk_self_snd x a'
  have he₁ := (G.expMap_smul_eq_proj_geodesicFlow hr x a s hdom₁).symm
  have he₂ := (G.expMap_smul_eq_proj_geodesicFlow hr x a' s hdom₂).symm
  change ‖extChartAt I x (G.geodesicFlow (⟨x, a⟩ : TangentBundle I N) s).proj - extChartAt I x x -
    s • (trivializationAt E (TangentSpace I) x (⟨x, a⟩ : TangentBundle I N)).2‖ ≤ ε * s at hb₁
  change ‖extChartAt I x (G.geodesicFlow (⟨x, a'⟩ : TangentBundle I N) s).proj - extChartAt I x x -
    s • (trivializationAt E (TangentSpace I) x (⟨x, a'⟩ : TangentBundle I N)).2‖ ≤ ε * s at hb₂
  rw [hr₁, he₁, h s hsδ] at hb₁
  rw [hr₂, he₂] at hb₂
  set A := extChartAt I x (G.expMap (⟨x, s • a'⟩ : TangentBundle I N)) with hA
  have hkey : ‖s • a - s • a'‖ ≤ ε * s + ε * s := by
    have heq : s • a - s • a' = (A - extChartAt I x x - s • a') - (A - extChartAt I x x - s • a) := by
      abel
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add hb₂ hb₁)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at hkey
  nlinarith

section Shift

variable {W : Type*} [MetricSpace W]

/-- The vertical shift `x ↦ Φ⁻¹((Φ x).1 + ℓ, (Φ x).2)` moves every point by `|ℓ|`. -/
theorem dist_vertical_shift (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) (ℓ : ℝ) (x : N) :
    dist x (Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))) = |ℓ| := by
  have hΦx : Φ x = WithLp.toLp 2 ((Φ x).fst, (Φ x).snd) := rfl
  rw [← Φ.dist_eq, Φ.apply_symm_apply, hΦx, dist_withLp_two_prod]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self, Real.dist_eq]
  rw [show (Φ x).fst - ((Φ x).fst + ℓ) = -ℓ by ring, abs_neg]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, sq_abs]
  exact Real.sqrt_sq_eq_abs ℓ

/-- The vertical shift is an isometry of `N`. -/
theorem isometry_vertical_shift (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) (ℓ : ℝ) :
    Isometry (fun x : N => Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [← Φ.dist_eq, Φ.apply_symm_apply, Φ.apply_symm_apply, dist_withLp_two_prod,
    ← Φ.dist_eq x y, dist_withLp_two_prod]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq]
  rw [show (Φ x).fst + ℓ - ((Φ y).fst + ℓ) = (Φ x).fst - (Φ y).fst by ring]

end Shift

section Kernel

variable [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsRiemannianManifold I N]

/-- **B1 (LFR18-K): all-direction convergence to the limit direction set.** For LFR14-shaped data
(LC50′'s hypotheses), a compact `C`, an endpoint map `e` continuous on `C` and an open `O ⊆ TN`
containing every limit minimizing direction from `x ∈ C` to `e x`: eventually, for every `x ∈ C`
and EVERY minimizing `g i`-direction `w` from `j i x` to `j i (e x)`, the inverse lift
`⟨x, d(j i)⁻¹ w⟩` lies in `O`. -/
theorem eventually_inverse_minimizing_directions_mem_nhds_finite [∀ i, CompleteSpace (M i)]
    {r : ℕ∞} (hr : 1 ≤ r)
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
    {C : Set N} (hC : IsCompact C) (e : N → N) (he : ContinuousOn e C)
    {O : Set (TangentBundle I N)} (hO : IsOpen O)
    (hCO : ∀ x ∈ C, ∀ u ∈ G.finiteMinimizingDirectionsTo {e x} x,
      (⟨x, u⟩ : TangentBundle I N) ∈ O) :
    ∀ᶠ i in atTop, ∀ x ∈ C,
      ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) {j i (e x)} (j i x),
        (⟨x, mfderiv I I ((j i).symm : M i → N) (j i x) w⟩ : TangentBundle I N) ∈ O := by
  by_contra hbad
  rw [Filter.not_eventually] at hbad
  obtain ⟨ψ, hψ, hψbad⟩ := Filter.extraction_of_frequently_atTop hbad
  simp only [not_forall, exists_prop] at hψbad
  choose x hxC w hw hwO using hψbad
  have hψt := hψ.tendsto_atTop
  obtain ⟨yInf, -, v, hvC, hvdir, -, φ, -, hy, hlim⟩ :=
    exists_subseq_minimizing_direction_limit_finite_of_isCompact (M := fun k => M (ψ k)) hr G
      hGnorm (fun k => g (ψ k)) (fun k => hmetric (ψ k)) hK q (fun k => j (ψ k))
      (fun C hC => hψt.eventually (hexh C hC))
      (fun z L hL hLt => (hconv z L hL hLt).comp_subseq hψ)
      (fun R ε hε => hψt.eventually (hdist R ε hε))
      (fun a b ha hab => hψt.eventually (hcover a b ha hab))
      hC x hxC (hC.image_of_continuousOn he) (fun k => e (x k))
      (fun k => mem_image_of_mem e (hxC k)) w hw
  have hxlim : Tendsto (fun k => x (φ k)) atTop (𝓝 v.proj) :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).tendsto v).comp hlim
  have hey : Tendsto (fun k => e (x (φ k))) atTop (𝓝 (e v.proj)) :=
    (he v.proj hvC).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hxlim, Eventually.of_forall fun k => hxC (φ k)⟩)
  have hyeq : yInf = e v.proj := tendsto_nhds_unique hy hey
  rw [hyeq] at hvdir
  have hvO : v ∈ O := hCO v.proj hvC v.snd hvdir
  obtain ⟨k, hk⟩ := (hlim.eventually (hO.mem_nhds hvO)).exists
  exact hwO (φ k) hk

end Kernel

section Vertical

variable [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]

/-- **Minimizing directions to a vertical shift are vertical.** In a metric product
`Φ : N ≃ᵢ ℓ²(ℝ × W)`, a minimizing unit direction `v` from `x` to `x⁺ = Φ⁻¹((Φ x).1 + ℓ, (Φ x).2)`
has the vertical line as radial geodesic: `exp_x(s v) = Φ⁻¹((Φ x).1 + s, (Φ x).2)` on `[0, ℓ]`. -/
theorem expMap_smul_eq_vertical_of_mem [CompleteSpace N] {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : N)
    {v : TangentSpace I x}
    (hv : v ∈ G.finiteMinimizingDirectionsTo
      {Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x) :
    ∀ s ∈ Icc 0 ℓ, G.expMap (⟨x, s • v⟩ : TangentBundle I N) =
      Φ.symm (WithLp.toLp 2 ((Φ x).fst + s, (Φ x).snd)) := by
  set t := (Φ x).fst with ht
  set z := (Φ x).snd with hz
  have hΦx : Φ x = WithLp.toLp 2 (t, z) := rfl
  have hdist : dist x (Φ.symm (WithLp.toLp 2 (t + ℓ, z))) = ℓ := by
    rw [dist_vertical_shift Φ ℓ x, abs_of_pos hℓ]
  obtain ⟨hvu, hvend⟩ := hv
  rw [Metric.infDist_singleton, hdist, mem_singleton_iff] at hvend
  have hseg := fun {s t : ℝ} (hs : s ∈ Icc 0 ℓ) (ht : t ∈ Icc 0 ℓ) =>
    dist_expMap_smul_eq_of_endpoint hr G hGnorm hvu (by rw [hvend, hdist]) hs ht
  set γ : ℝ → WithLp 2 (ℝ × W) := fun s => Φ (G.expMap (⟨x, s • v⟩ : TangentBundle I N)) with hγ
  have hγseg : ∀ s ∈ Icc 0 ℓ, ∀ s' ∈ Icc 0 ℓ, dist (γ s) (γ s') = |s - s'| := by
    intro s hs s' hs'
    rw [hγ, Φ.dist_eq]
    exact hseg hs hs'
  have hγ0 : γ 0 = WithLp.toLp 2 (t, z) := by
    rw [hγ]
    simp only [zero_smul]
    rw [G.expMap_zero hr x, hΦx]
  have hγℓ : γ ℓ = WithLp.toLp 2 (t + ℓ, z) := by
    rw [hγ]
    simp only
    rw [hvend, Φ.apply_symm_apply]
  intro s hs
  have h := eq_vertical_of_isometry_segment γ hγseg hγ0 hγℓ s hs
  rw [← h]
  exact (Φ.symm_apply_apply _).symm

/-- **B2 (LFR18-U): uniqueness of the vertical direction in a metric product.** In
`Φ : N ≃ᵢ ℓ²(ℝ × W)`, the minimizing unit direction from `x` to its vertical shift by `ℓ > 0` is
unique. -/
theorem eq_of_mem_finiteMinimizingDirectionsTo_vertical_shift [CompleteSpace N] {r : ℕ∞}
    (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {ℓ : ℝ} (hℓ : 0 < ℓ) (x : N)
    {u u' : TangentSpace I x}
    (hu : u ∈ G.finiteMinimizingDirectionsTo
      {Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x)
    (hu' : u' ∈ G.finiteMinimizingDirectionsTo
      {Φ.symm (WithLp.toLp 2 ((Φ x).fst + ℓ, (Φ x).snd))} x) :
    u = u' :=
  eq_of_expMap_smul_eq_on_Icc hr G hℓ fun s hs =>
    (expMap_smul_eq_vertical_of_mem hr G hGnorm Φ hℓ x hu s hs).trans
      (expMap_smul_eq_vertical_of_mem hr G hGnorm Φ hℓ x hu' s hs).symm

end Vertical

end DifferentialGeometry.Geometry.Riemannian.Geodesic
