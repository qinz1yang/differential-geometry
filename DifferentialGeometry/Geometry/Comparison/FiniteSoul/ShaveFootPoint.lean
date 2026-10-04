import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveOpenCore
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.FirstVariation

/-!
# S-SHAVE, R1(ii): supporting half spaces at a nearest boundary point (finite metric)

Lane CMS-B (review `review-finite-soul.md` §4 R1(ii)). The smooth template
(`Nonnegative/BoundaryShift.lean:439–447`) ASSUMES `HasSupportingHalfSpaces`; here the corresponding
fact is PROVED, for a complete metric `g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`), with no curvature
and no dimension hypothesis.

`IsTotallyConvexFinite.expMap_notMem_interior_of_foot`: let `C` be totally convex, `y ∈ C` with
`l = d(y, ∂C) > 0`, and `u` a unit vector at `y` with `p = π φ_l(y, u) ∈ ∂C` (a nearest boundary
point, reached with arrival velocity `v_p`). Then `exp_p ξ ∉ int C` for every `ξ` with
`g_p(ξ, v_p) ≥ 0` (any length).

Proof (the review's independent first-variation argument): if `exp_p ξ ∈ int C`, the perturbation
`ξ' = ξ + ε v_p` still lands in `int C` and has `g_p(ξ', v_p) > 0`; by the first variation (CM3,
`S = {y}`, minimizing direction `-v_p`) a short backward displacement `exp_p (-t ξ')` enters
`ball y l ⊆ int C`; the geodesic arc `s ↦ exp_p (s ξ')`, `s ∈ [-t, 1]`, lies in `C` by total
convexity and has both ends in `int C`, so R1(i) puts its point `p` (at `s = 0`) in `int C`,
contradicting `p ∈ ∂C`.
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

/-- Reversal of the geodesic flow: the flow from `-v` at time `t` is the flow from `v` at `-t`. -/
theorem proj_geodesicFlow_neg_snd
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (P : TangentBundle I M) (t : ℝ) :
    (g.geodesicFlow (⟨P.proj, (-1 : ℝ) • P.snd⟩ : TangentBundle I M) t).proj =
      (g.geodesicFlow P (-t)).proj := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  rw [g.geodesicFlow_smul_eq hr1 P (-1) t (by rw [hD]; exact mem_univ _)]
  change (g.geodesicFlow P (-1 * t)).proj = _
  rw [neg_one_mul]

/-- The flow from an intermediate time: `φ_{t+s}(P) = φ_s(φ_t(P))` (complete metric). -/
theorem geodesicFlow_add_of_complete
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (P : TangentBundle I M) (t s : ℝ) :
    g.geodesicFlow P (t + s) = g.geodesicFlow (g.geodesicFlow P t) s := by
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  exact g.geodesicFlow_add (one_le_two.trans hr) (by rw [hD]; exact mem_univ _)
    (by rw [hD]; exact mem_univ _)

/-- **R1(ii): supporting half spaces at a nearest boundary point** (proved, not assumed). If `y ∈ C`,
`l = d(y, ∂C) > 0` and the unit geodesic from `y` in direction `u` reaches `∂C` at time `l` in
`P = φ_l(y, u)`, then `exp_{π P} ξ ∉ int C` whenever `g(ξ, P.snd) ≥ 0`. -/
theorem IsTotallyConvexFinite.expMap_notMem_interior_of_foot [NeZero (Module.finrank ℝ E)]
    {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) {y : M} (hy : y ∈ C) {u : E}
    (hu : g.inner y u u = 1) (hl : 0 < infDist y (frontier C))
    (hfoot : (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (frontier C))).proj ∈
      frontier C) (ξ : E)
    (hξ : 0 ≤ g.inner (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (frontier C))).proj ξ
      (g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (frontier C))).snd) :
    g.expMap (⟨(g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) (infDist y (frontier C))).proj, ξ⟩ :
      TangentBundle I M) ∉ interior C := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have hmem : ∀ q : TangentBundle I M × ℝ, q ∈ g.geodesicFlowDomain := fun q => by
    rw [hD]; exact mem_univ q
  set l := infDist y (frontier C) with hldef
  set P := g.geodesicFlow (⟨y, u⟩ : TangentBundle I M) l with hP
  intro hint
  -- the arrival velocity is a unit vector
  have hvp1 : g.inner P.proj P.snd P.snd = 1 := by
    rw [hP, g.inner_geodesicFlow_eq hr1 _ l (hmem _)]
    exact hu
  -- `d(π P, y) = l`
  have hpy : dist y P.proj ≤ l := by
    have h := g.dist_proj_geodesicFlow_le hr1 hnorm (p := (⟨y, u⟩ : TangentBundle I M)) (s := 0)
      (t := l) (fun τ _ => hmem _)
    rw [g.geodesicFlow_zero hr1] at h
    change dist y P.proj ≤ Real.sqrt (g.inner y u u) * |l - 0| at h
    rwa [hu, Real.sqrt_one, one_mul, sub_zero, abs_of_nonneg hl.le] at h
  have hyp : l ≤ dist y P.proj := infDist_le_dist_of_mem hfoot
  have hdist : dist P.proj y = l := by rw [dist_comm]; exact le_antisymm hpy hyp
  have hpne : P.proj ∉ ({y} : Set M) := by
    rw [mem_singleton_iff]
    intro h
    rw [h, dist_self] at hdist
    exact (ne_of_gt hl) hdist.symm
  -- perturbation of `ξ` towards `v_p`
  set vp : E := P.snd with hvp
  have hcontξ : Continuous (fun w : E => g.expMap (⟨P.proj, w⟩ : TangentBundle I M)) :=
    (g.continuous_expMap_of_completeSpace hr hnorm).comp
      (FiberBundle.totalSpaceMk_isInducing E (TangentSpace I) P.proj).continuous
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      g.expMap (⟨P.proj, ξ + ε • vp⟩ : TangentBundle I M) ∈ interior C := by
    have hc : Continuous (fun ε : ℝ => g.expMap (⟨P.proj, ξ + ε • vp⟩ : TangentBundle I M)) :=
      hcontξ.comp (continuous_const.add (continuous_id.smul continuous_const))
    have h0 : (fun ε : ℝ => g.expMap (⟨P.proj, ξ + ε • vp⟩ : TangentBundle I M)) 0 ∈
        interior C := by
      simp only [zero_smul, add_zero]
      exact hint
    exact nhdsWithin_le_nhds ((hc.tendsto 0).eventually (isOpen_interior.mem_nhds h0))
  obtain ⟨ε, hε, hεpos⟩ := (Filter.Eventually.and hev self_mem_nhdsWithin).exists
  have hεpos' : (0 : ℝ) < ε := hεpos
  set ξ' : E := ξ + ε • vp with hξ'
  have hξ'pos : 0 < g.inner P.proj ξ' vp := by
    have h1 : g.inner P.proj (ξ + ε • vp) = g.inner P.proj ξ + g.inner P.proj (ε • vp) :=
      (g.inner P.proj).map_add ξ (ε • vp)
    have h2 : g.inner P.proj (ε • vp) = ε • g.inner P.proj vp := (g.inner P.proj).map_smul ε vp
    have h : g.inner P.proj ξ' vp = g.inner P.proj ξ vp + ε * g.inner P.proj vp vp := by
      rw [hξ', h1, h2, add_apply, smul_apply, smul_eq_mul]
    rw [h, hvp1]
    linarith
  -- first variation towards `y` along `-ξ'`
  set X : E := (-1 : ℝ) • ξ' with hX
  set γ : ℝ → M := fun s => (g.geodesicFlow (⟨P.proj, X⟩ : TangentBundle I M) s).proj with hγ
  have hγ0 : γ 0 = P.proj := by
    simp only [hγ, g.geodesicFlow_zero hr1]
  have hγd : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight X) := by
    have h := g.hasMFDerivAt_geodesicFlow_proj hr1 (p := (⟨P.proj, X⟩ : TangentBundle I M))
      (t := 0) (hmem _)
    have hX0 : (g.geodesicFlow (⟨P.proj, X⟩ : TangentBundle I M) 0).snd = X := by
      rw [g.geodesicFlow_zero hr1]
    rw [hX0] at h
    exact h
  have hdir : ((-1 : ℝ) • P.snd) ∈ g.finiteMinimizingDirectionsTo {y} P.proj := by
    refine ⟨?_, ?_⟩
    · have h : g.inner P.proj ((-1 : ℝ) • P.snd) ((-1 : ℝ) • P.snd) =
          (-1) ^ 2 * g.inner P.proj P.snd P.snd :=
        DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self g P.proj (-1) P.snd
      rw [h, hvp1]; norm_num
    · rw [infDist_singleton, hdist, mem_singleton_iff,
        g.expMap_smul_eq_proj_geodesicFlow hr1 _ _ l (hmem _)]
      have h1 : (g.geodesicFlow (⟨P.proj, (-1 : ℝ) • P.snd⟩ : TangentBundle I M) l).proj =
          (g.geodesicFlow P (-l)).proj := proj_geodesicFlow_neg_snd g hr hnorm P l
      rw [h1, hP, ← geodesicFlow_add_of_complete g hr hnorm, add_neg_cancel,
        g.geodesicFlow_zero hr1]
  have hc : -g.inner P.proj ((-1 : ℝ) • P.snd) X < -(g.inner P.proj ξ' vp) / 2 := by
    have h3 : g.inner P.proj ((-1 : ℝ) • P.snd) = (-1 : ℝ) • g.inner P.proj P.snd :=
      (g.inner P.proj).map_smul (-1) P.snd
    have h4 : g.inner P.proj P.snd X = (-1 : ℝ) • g.inner P.proj P.snd ξ' :=
      (g.inner P.proj P.snd).map_smul (-1) ξ'
    have h : g.inner P.proj ((-1 : ℝ) • P.snd) X = g.inner P.proj ξ' vp := by
      have h5 : ((-1 : ℝ) • g.inner P.proj P.snd) X = (-1 : ℝ) • g.inner P.proj P.snd X := rfl
      rw [h3, h5, h4, smul_eq_mul, smul_eq_mul, g.symm P.proj P.snd ξ', hvp]
      ring
    rw [h]
    linarith
  have hfv := g.eventually_infDist_sub_le_finite_of_eq hr hnorm isClosed_singleton
    (singleton_nonempty y) hγ0 hγd hpne hdir hc
  obtain ⟨t₁, ht₁, ht₁pos⟩ := (Filter.Eventually.and hfv self_mem_nhdsWithin).exists
  have ht₁pos' : (0 : ℝ) < t₁ := ht₁pos
  have hγt₁ : γ t₁ ∈ interior C := by
    refine ball_infDist_frontier_subset_interior g hr hnorm hy ?_
    rw [mem_ball, ← hldef]
    rw [infDist_singleton, infDist_singleton, hdist] at ht₁
    have : t₁ * (-(g.inner P.proj ξ' P.snd) / 2) < 0 := by
      have := mul_pos ht₁pos' hξ'pos
      nlinarith
    linarith
  -- the arc through `p`
  set Q : TangentBundle I M := ⟨P.proj, ξ'⟩ with hQ
  have hQback : (g.geodesicFlow Q (-t₁)).proj ∈ interior C := by
    have h : γ t₁ = (g.geodesicFlow Q (-t₁)).proj := proj_geodesicFlow_neg_snd g hr hnorm Q t₁
    rw [← h]; exact hγt₁
  have hQ1 : (g.geodesicFlow Q 1).proj ∈ interior C := hε
  have hmaps : ∀ t ∈ Icc (-t₁) 1, (g.geodesicFlow Q t).proj ∈ C := by
    intro t ht
    have hshift : ∀ τ : ℝ, g.geodesicFlow Q (-t₁ + τ) = g.geodesicFlow (g.geodesicFlow Q (-t₁)) τ :=
      fun τ => geodesicFlow_add_of_complete g hr hnorm Q (-t₁) τ
    have hend : (g.geodesicFlow (g.geodesicFlow Q (-t₁)) (1 + t₁)).proj ∈ C := by
      rw [← hshift, show -t₁ + (1 + t₁) = 1 by ring]
      exact interior_subset hQ1
    have h := hC (g.geodesicFlow Q (-t₁)) (1 + t₁) (by linarith) (interior_subset hQback) hend
      (t + t₁) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rwa [← hshift, show -t₁ + (t + t₁) = t by ring] at h
  have hp0 := hC.proj_geodesicFlow_mem_interior hr hnorm Q hmaps ⟨by linarith, le_rfl⟩ hQ1 0
    ⟨by linarith, by norm_num⟩
  rw [g.geodesicFlow_zero hr1] at hp0
  exact hfoot.2 hp0

end DifferentialGeometry.Geometry.FiniteSoul

end
