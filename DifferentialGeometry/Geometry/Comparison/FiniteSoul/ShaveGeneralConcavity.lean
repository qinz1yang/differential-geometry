import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveGeneralSteps
import DifferentialGeometry.Geometry.Comparison.Nonnegative.BoundaryConcavity

/-!
# General-dimension S-SHAVE, A2: concavity of the boundary distance from the orthogonal shift

Lane CMS3-SHAVE (frozen interface A2 of `build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean`).
For a complete metric `g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`) with `sec ≥ 0` in ANY dimension and a
totally convex set `C` with the orthogonal boundary shift `hshiftC` (the conclusion of A1 at every
interior point), the function `t ↦ d(γ_p t, ∂C)` is concave on every interval `[0, ℓ]` mapped into `C`
by `γ_p = π ∘ φ_·(p)` (`concaveOn_infDist_frontier_of_orthogonalShift`).

The proof is CMS-B's `ShaveConcavity.lean` with the steps `infDist_frontier_step_of_shift`
(`ShaveGeneralSteps.lean`): `concaveOn_of_linear_upper_support`; at an interior parameter either the
open arc lies on `∂C` (open core `IsTotallyConvexFinite.proj_geodesicFlow_mem_interior`), or the two
one-sided steps give the linear upper support.
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

/-- **Linear upper support of `d(γ_p ·, ∂C)` at an interior point of `C`** (any dimension, from the
orthogonal boundary shift). -/
theorem exists_upper_support_infDist_frontier_geodesicFlow_of_shift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) {C : Set M}
    (hshiftC : ∀ x ∈ interior C, ∃ ρ > 0, ∀ y : M, dist x y < ρ → ∀ u w : E, g.inner y u u = 1 →
      g.inner y w w = 1 → g.inner y u w = 0 →
      g.expMap (⟨y, infDist y (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) (frontier C) ≤
        infDist y (frontier C))
    (p : TangentBundle I M) {s : ℝ}
    (hint : (g.geodesicFlow p s).proj ∈ interior C) :
    ∃ c : ℝ, ∀ᶠ y in 𝓝 s, infDist (g.geodesicFlow p y).proj (frontier C) ≤
      infDist (g.geodesicFlow p s).proj (frontier C) + c * (y - s) := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set σ : ℝ := Real.sqrt (g.inner p.proj p.snd p.snd) with hσ
  have hlip : ∀ a b : ℝ, dist (g.geodesicFlow p a).proj (g.geodesicFlow p b).proj ≤ σ * |b - a| :=
    fun a b => g.dist_proj_geodesicFlow_le hr1 hnorm (fun τ _ => by rw [hD]; exact mem_univ _)
  rcases (frontier C).eq_empty_or_nonempty with hB | hB
  · refine ⟨0, Eventually.of_forall fun y => ?_⟩
    rw [hB, infDist_empty, infDist_empty]
    simp
  have hσnn : 0 ≤ σ := Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hσnn with hσ0 | hσpos
  · refine ⟨0, Eventually.of_forall fun y => ?_⟩
    have h := hlip s y
    rw [← hσ0, zero_mul] at h
    have heq : (g.geodesicFlow p y).proj = (g.geodesicFlow p s).proj :=
      (dist_le_zero.1 h).symm
    rw [heq]
    simp
  obtain ⟨u, hu, hfoot⟩ := exists_unit_foot_frontier g hr hnorm hB (g.geodesicFlow p s).proj
  obtain ⟨v, hvdef⟩ : ∃ v : E, v = (g.geodesicFlow p s).snd := ⟨_, rfl⟩
  have hvv : g.inner (g.geodesicFlow p s).proj v v = σ ^ 2 := by
    subst hvdef
    rw [g.inner_geodesicFlow_eq hr1 p s (by rw [hD]; exact mem_univ _), hσ,
      Real.sq_sqrt (DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g _ _)]
  have hσne : σ ≠ 0 := ne_of_gt hσpos
  obtain ⟨e, hedef⟩ : ∃ e : E, e = σ⁻¹ • v := ⟨_, rfl⟩
  have he : g.inner (g.geodesicFlow p s).proj e e = 1 := by
    rw [hedef, shaveInner_smul_left, shaveInner_smul_right, hvv]
    field_simp
  obtain ⟨e', he'def⟩ : ∃ e' : E, e' = (-1 : ℝ) • e := ⟨_, rfl⟩
  have he' : g.inner (g.geodesicFlow p s).proj e' e' = 1 := by
    rw [he'def, shaveInner_smul_left, shaveInner_smul_right, he]
    norm_num
  have hue' : g.inner (g.geodesicFlow p s).proj u e' = -g.inner (g.geodesicFlow p s).proj u e := by
    rw [he'def, shaveInner_smul_right]
    ring
  -- the geodesic read from `s`
  have hflow : ∀ y : ℝ, (g.geodesicFlow p y).proj =
      g.expMap (⟨(g.geodesicFlow p s).proj, (y - s) • v⟩ : TangentBundle I M) := by
    intro y
    have h1 := proj_geodesicFlow_add_eq_expMap g hr hnorm p s (y - s)
    rw [add_sub_cancel] at h1
    subst hvdef
    exact h1
  have hfwd : ∀ y : ℝ, (g.geodesicFlow p y).proj =
      g.expMap (⟨(g.geodesicFlow p s).proj, (σ * (y - s)) • e⟩ : TangentBundle I M) := by
    intro y
    have hv' : ((σ * (y - s)) • (σ⁻¹ • v) : E) = (y - s) • v := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [hflow y, hedef]
    exact (congrArg (fun w : E => g.expMap (⟨(g.geodesicFlow p s).proj, w⟩ : TangentBundle I M))
      hv').symm
  have hbwd : ∀ y : ℝ, (g.geodesicFlow p y).proj =
      g.expMap (⟨(g.geodesicFlow p s).proj, (σ * (s - y)) • e'⟩ : TangentBundle I M) := by
    intro y
    have hv' : ((σ * (s - y)) • ((-1 : ℝ) • (σ⁻¹ • v)) : E) = (y - s) • v := by
      rw [smul_smul, smul_smul]
      congr 1
      field_simp
      ring
    rw [hflow y, he'def, hedef]
    exact (congrArg (fun w : E => g.expMap (⟨(g.geodesicFlow p s).proj, w⟩ : TangentBundle I M))
      hv').symm
  have hstep1 := infDist_frontier_step_of_shift g hr hnorm hsec hshiftC hint hu hfoot he
  have hstep2 := infDist_frontier_step_of_shift g hr hnorm hsec hshiftC hint hu hfoot he'
  obtain ⟨δ₁, hδ₁, hP₁⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hstep1)
  obtain ⟨δ₂, hδ₂, hP₂⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hstep2)
  set c : ℝ := g.inner (g.geodesicFlow p s).proj u e with hcdef
  refine ⟨-(σ * c), ?_⟩
  have hε : 0 < min δ₁ δ₂ / σ := div_pos (lt_min hδ₁ hδ₂) hσpos
  filter_upwards [Ioo_mem_nhds (show s - min δ₁ δ₂ / σ < s by linarith)
    (show s < s + min δ₁ δ₂ / σ by linarith)] with y hy
  have hσδ : ∀ a : ℝ, 0 < a → a < min δ₁ δ₂ / σ → σ * a < min δ₁ δ₂ := by
    intro a ha hlt
    have h := mul_lt_mul_of_pos_left hlt hσpos
    rwa [mul_div_cancel₀ _ hσne] at h
  rcases lt_trichotomy y s with hlt | hyeq | hgt
  · have hh0 : 0 < σ * (s - y) := mul_pos hσpos (by linarith)
    have hlt2 := hσδ (s - y) (by linarith) (by linarith [hy.1])
    have hres : infDist (g.expMap (⟨(g.geodesicFlow p s).proj, (σ * (s - y)) • e'⟩ :
        TangentBundle I M)) (frontier C) ≤ infDist (g.geodesicFlow p s).proj (frontier C) -
          σ * (s - y) * g.inner (g.geodesicFlow p s).proj u e' :=
      hP₂ (by rw [Real.dist_eq, sub_zero, abs_of_pos hh0]; exact lt_of_lt_of_le hlt2 (min_le_right _ _))
        hh0
    rw [← hbwd y, hue'] at hres
    refine hres.trans (le_of_eq ?_)
    ring
  · rw [hyeq, sub_self, mul_zero, add_zero]
  · have hh0 : 0 < σ * (y - s) := mul_pos hσpos (by linarith)
    have hlt2 := hσδ (y - s) (by linarith) (by linarith [hy.2])
    have hres : infDist (g.expMap (⟨(g.geodesicFlow p s).proj, (σ * (y - s)) • e⟩ :
        TangentBundle I M)) (frontier C) ≤ infDist (g.geodesicFlow p s).proj (frontier C) -
          σ * (y - s) * c :=
      hP₁ (by rw [Real.dist_eq, sub_zero, abs_of_pos hh0]; exact lt_of_lt_of_le hlt2 (min_le_left _ _))
        hh0
    rw [← hfwd y] at hres
    refine hres.trans (le_of_eq ?_)
    ring

/-- **A2. Concavity from the orthogonal boundary shift** (dimension-free; `2 ≤ r`, `sec ≥ 0` for the
hinge; finite CG 1.10). The frozen D-CMS3 statement, with `IsClosed C` dropped (closedness is used
only by A1, which produces `hshiftC`). -/
theorem concaveOn_infDist_frontier_of_orthogonalShift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {C : Set M} (hconv : IsTotallyConvexFinite g C)
    (hshiftC : ∀ x ∈ interior C, ∃ ρ > 0, ∀ y : M, dist x y < ρ → ∀ u w : E, g.inner y u u = 1 →
      g.inner y w w = 1 → g.inner y u w = 0 →
      g.expMap (⟨y, infDist y (frontier C) • u⟩ : TangentBundle I M) ∈ frontier C →
      ∀ h ∈ Ico 0 ρ, infDist (g.expMap (⟨y, h • w⟩ : TangentBundle I M)) (frontier C) ≤
        infDist y (frontier C))
    (p : TangentBundle I M) (ℓ : ℝ)
    (hmaps : ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C) :
    ConcaveOn ℝ (Icc 0 ℓ) (fun t => infDist (g.geodesicFlow p t).proj (frontier C)) := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set σ : ℝ := Real.sqrt (g.inner p.proj p.snd p.snd) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hlip : ∀ a b : ℝ, dist (g.geodesicFlow p a).proj (g.geodesicFlow p b).proj ≤ σ * |b - a| :=
    fun a b => g.dist_proj_geodesicFlow_le hr1 hnorm (fun τ _ => by rw [hD]; exact mem_univ _)
  have hγc : Continuous (fun t : ℝ => (g.geodesicFlow p t).proj) := by
    refine LipschitzWith.continuous (K := ⟨σ, hσ0⟩) (LipschitzWith.of_dist_le_mul fun a b => ?_)
    rw [Real.dist_eq, abs_sub_comm]
    exact hlip a b
  refine DifferentialGeometry.Geometry.Topology.concaveOn_of_linear_upper_support (convex_Icc 0 ℓ)
    ((continuous_infDist_pt _).comp hγc).continuousOn ?_
  intro s hs
  rw [interior_Icc] at hs
  by_cases hint : (g.geodesicFlow p s).proj ∈ interior C
  · exact exists_upper_support_infDist_frontier_geodesicFlow_of_shift g hr hnorm hsec hshiftC p hint
  · have hall : ∀ t ∈ Ioo 0 ℓ, (g.geodesicFlow p t).proj ∈ frontier C := by
      intro t ht
      refine ⟨subset_closure (hmaps t (Ioo_subset_Icc_self ht)), fun htC => hint ?_⟩
      exact hconv.proj_geodesicFlow_mem_interior hr hnorm p hmaps (Ioo_subset_Icc_self ht) htC s hs
    refine ⟨0, ?_⟩
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with y hy
    rw [infDist_zero_of_mem (hall y hy), infDist_zero_of_mem (hall s hs)]
    simp

end DifferentialGeometry.Geometry.FiniteSoul

end
