import DifferentialGeometry.Geometry.Comparison.FiniteMetric.SquaredDistance
import DifferentialGeometry.Analysis.Convex.LocalToGlobal
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.UniformNormalCharts
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.FlowLemmas
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SpeedBound
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness

/-!
# LFR55 along every geodesic of a finite metric

For a complete finite-regularity metric `g : C^{r+1}` (`2 ≤ r`) with `sec_g ≥ 0` whose length
distance is the ambient distance (`hnorm`):

* `isometric_proj_geodesicFlow_near`: every unit-speed geodesic `t ↦ π(Φ_t P)` is an isometric
  segment near each time (one uniform normal-chart radius, CM1.d, over a compact piece of the
  orbit);
* `convexOn_sq_sub_sq_dist_geodesicFlow_finite` (**LFR55**): `t ↦ t² - d(q, π(Φ_t P))²` is convex
  on `ℝ` for every unit `P` and every `q` — no minimality of the geodesic is assumed. Local
  convexity (CM-A2's `convexOn_sq_sub_sq_dist_finite` on the short isometric pieces) is
  globalized by `convexOn_of_locally`;
* the exponential forms for an ARBITRARY initial vector `u` (speed `|u|_{g_o}`):
  `t ↦ g_o(u,u) t² - d(q, exp_o (t u))²` is convex on `ℝ`
  (`convexOn_inner_mul_sq_sub_sq_dist_expMap_finite`), and the same for the flow of any `P`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.FiniteComparison

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- A unit-speed geodesic of a complete finite metric is an isometric segment near every time. -/
theorem isometric_proj_geodesicFlow_near
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (P : TangentBundle I M) (hP : g.inner P.proj P.snd P.snd = 1) (t₀ : ℝ) :
    ∃ ε > 0, ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
      dist (g.geodesicFlow P s).proj (g.geodesicFlow P t).proj = |s - t| := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have hmem : ∀ (Q : TangentBundle I M) (τ : ℝ), (Q, τ) ∈ g.geodesicFlowDomain := fun Q τ => by
    rw [hD]
    exact mem_univ _
  set σ : ℝ → M := fun τ => (g.geodesicFlow P τ).proj with hσ
  have hcont : Continuous σ := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun s t => ?_).continuous
    have h := g.dist_proj_geodesicFlow_le hr1 hnorm (p := P) (s := s) (t := t)
      (fun τ _ => hmem P τ)
    rw [hP, Real.sqrt_one, one_mul] at h
    rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_comm]
    exact h
  obtain ⟨ρ, hρ, hch⟩ := g.exists_uniform_normal_charts hr hnorm
    ((isCompact_Icc (a := t₀ - 1) (b := t₀ + 1)).image hcont)
  have hε : 0 < min 1 (ρ / 3) := lt_min one_pos (by positivity)
  refine ⟨min 1 (ρ / 3), hε, fun s hs t ht => ?_⟩
  have hm1 := min_le_left 1 (ρ / 3)
  have hm2 := min_le_right 1 (ρ / 3)
  have hsK : s ∈ Icc (t₀ - 1) (t₀ + 1) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨e, hsrc, -, hexp, -, -, hdist⟩ := hch (σ s) (mem_image_of_mem σ hsK)
  set Q : TangentBundle I M := g.geodesicFlow P s with hQ
  have hQunit : g.inner Q.proj Q.snd Q.snd = 1 :=
    (g.inner_geodesicFlow_eq hr1 P s (hmem P s)).trans hP
  have hflow : σ t = g.expMap (⟨Q.proj, (t - s) • Q.snd⟩ : TangentBundle I M) := by
    have h1 := g.geodesicFlow_add hr1 (p := P) (t := s) (s := t - s) (hmem P s) (hmem P _)
    rw [show s + (t - s) = t by ring] at h1
    rw [g.expMap_smul_eq_proj_geodesicFlow hr1 Q.proj Q.snd (t - s) (hmem _ _)]
    change (g.geodesicFlow P t).proj = (g.geodesicFlow Q (t - s)).proj
    rw [h1]
  have hts : |t - s| < ρ := by
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hinner : g.inner Q.proj ((t - s) • Q.snd) ((t - s) • Q.snd) = (t - s) ^ 2 := by
    rw [Bundle.ContMDiffRiemannianMetric.inner_smul_self_smul g Q.proj (t - s) Q.snd, hQunit, mul_one]
  have hsrcmem : (t - s) • Q.snd ∈ e.source := by
    rw [hsrc]
    change g.inner Q.proj ((t - s) • Q.snd) ((t - s) • Q.snd) < ρ ^ 2
    rw [hinner, ← sq_abs]
    exact pow_lt_pow_left₀ hts (abs_nonneg _) (by norm_num)
  have hd := hdist _ hsrcmem
  rw [(hexp _ hsrcmem).2] at hd
  change dist Q.proj (g.expMap (⟨Q.proj, (t - s) • Q.snd⟩ : TangentBundle I M)) = _ at hd
  change dist (σ s) (σ t) = |s - t|
  rw [hflow, abs_sub_comm]
  change dist Q.proj _ = _
  rw [hd]
  change Real.sqrt (g.inner Q.proj ((t - s) • Q.snd) ((t - s) • Q.snd)) = _
  rw [hinner, Real.sqrt_sq_eq_abs]

variable [SigmaCompactSpace M]

/-- **LFR55, along every unit-speed geodesic.** For a complete finite metric (`C^{r+1}`,
`2 ≤ r`) with `sec ≥ 0`, `t ↦ t² - d(q, π(Φ_t P))²` is convex on `ℝ` for every unit `P` and every
`q`; the geodesic need not be minimizing. -/
theorem convexOn_sq_sub_sq_dist_geodesicFlow_finite [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (P : TangentBundle I M) (hP : g.inner P.proj P.snd P.snd = 1) (q : M) :
    ConvexOn ℝ univ (fun t => t ^ 2 - dist q ((g.geodesicFlow P t).proj) ^ 2) := by
  refine DifferentialGeometry.Analysis.Convex.convexOn_of_locally convex_univ fun t₀ _ => ?_
  obtain ⟨ε, hε, hiso⟩ := isometric_proj_geodesicFlow_near g hr hnorm P hP t₀
  refine ⟨ε, hε, ?_⟩
  rw [univ_inter]
  exact convexOn_sq_sub_sq_dist_finite g (one_le_two.trans hr) hnorm hsec (convex_Icc _ _)
    (σ := fun τ => (g.geodesicFlow P τ).proj) hiso q

/-- **LFR55, exponential form for an arbitrary initial vector**: `t ↦ g_o(u,u) t² - d(q, exp_o (t u))²`
is convex on `ℝ` (for unit `u` this is `t² - d(q, exp_o (t u))²`; for `u = 0` it is constant). -/
theorem convexOn_inner_mul_sq_sub_sq_dist_expMap_finite [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) (u : E) (q : M) :
    ConvexOn ℝ univ (fun t => g.inner o u u * t ^ 2 -
      dist q (g.expMap (⟨o, t • u⟩ : TangentBundle I M)) ^ 2) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  rcases eq_or_ne u 0 with hu0 | hu0
  · -- `u = 0`: the function is constant
    have hi : g.inner o u u = 0 := by
      obtain ⟨B, hB⟩ : ∃ B : E →L[ℝ] E →L[ℝ] ℝ, B = g.inner o := ⟨_, rfl⟩
      have h : B u u = 0 := by rw [hu0]; simp
      subst hB
      exact h
    have hpt : ∀ t : ℝ, (⟨o, t • u⟩ : TangentBundle I M) = ⟨o, u⟩ := by
      intro t
      have h : (t • u : E) = u := by rw [hu0, smul_zero]
      exact congrArg (fun w : E => (⟨o, w⟩ : TangentBundle I M)) h
    refine (convexOn_const (-dist q (g.expMap (⟨o, u⟩ : TangentBundle I M)) ^ 2)
      convex_univ).congr fun t _ => ?_
    change -dist q (g.expMap (⟨o, u⟩ : TangentBundle I M)) ^ 2 =
      g.inner o u u * t ^ 2 - dist q (g.expMap (⟨o, t • u⟩ : TangentBundle I M)) ^ 2
    rw [hi, hpt t, zero_mul, zero_sub]
  have hpos : 0 < g.inner o u u := g.pos o u hu0
  set c : ℝ := Real.sqrt (g.inner o u u) with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr hpos
  set u₁ : E := c⁻¹ • u with hu₁
  have hunit : g.inner o u₁ u₁ = 1 := by
    refine (Bundle.ContMDiffRiemannianMetric.inner_smul_self_smul g o c⁻¹ u).trans ?_
    rw [inv_pow, hc, Real.sq_sqrt hpos.le]
    exact inv_mul_cancel₀ hpos.ne'
  have hF := convexOn_sq_sub_sq_dist_geodesicFlow_finite g hr hnorm hsec
    (⟨o, u₁⟩ : TangentBundle I M) hunit q
  have hcomp := hF.comp_linearMap (LinearMap.mulLeft ℝ c)
  rw [preimage_univ] at hcomp
  refine hcomp.congr fun t _ => ?_
  have hpt : (⟨o, t • u⟩ : TangentBundle I M) = ⟨o, (c * t) • u₁⟩ := by
    have h : (t • u : E) = (c * t) • u₁ := by
      rw [hu₁, smul_smul, mul_assoc, mul_comm t, ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
    exact congrArg (fun w : E => (⟨o, w⟩ : TangentBundle I M)) h
  change (c * t) ^ 2 - dist q ((g.geodesicFlow (⟨o, u₁⟩ : TangentBundle I M) (c * t)).proj) ^ 2 =
    g.inner o u u * t ^ 2 - dist q (g.expMap (⟨o, t • u⟩ : TangentBundle I M)) ^ 2
  have hexp := g.expMap_smul_eq_proj_geodesicFlow hr1 o u₁ (c * t) (by rw [hD]; exact mem_univ _)
  have key : g.expMap (⟨o, t • u⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨o, u₁⟩ : TangentBundle I M) (c * t)).proj :=
    (congrArg g.expMap hpt).trans hexp
  rw [key, mul_pow, hc, Real.sq_sqrt hpos.le]

/-- **LFR55, unit exponential form**: for a unit `u`, `t ↦ t² - d(q, exp_o (t u))²` is convex
on `ℝ`. -/
theorem convexOn_sq_sub_sq_dist_expMap_univ_finite [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) {u : E} (hu : g.inner o u u = 1) (q : M) :
    ConvexOn ℝ univ (fun t => t ^ 2 - dist q (g.expMap (⟨o, t • u⟩ : TangentBundle I M)) ^ 2) := by
  have h := convexOn_inner_mul_sq_sub_sq_dist_expMap_finite g hr hnorm hsec o u q
  simp only [hu, one_mul] at h
  exact h

/-- **LFR55 along the geodesic flow of an arbitrary vector** `P` (speed `|P|_g`):
`t ↦ g(P,P) t² - d(q, π(Φ_t P))²` is convex on `ℝ`. -/
theorem convexOn_inner_mul_sq_sub_sq_dist_geodesicFlow_finite [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (P : TangentBundle I M) (q : M) :
    ConvexOn ℝ univ (fun t => g.inner P.proj P.snd P.snd * t ^ 2 -
      dist q ((g.geodesicFlow P t).proj) ^ 2) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  have h := convexOn_inner_mul_sq_sub_sq_dist_expMap_finite g hr hnorm hsec P.proj P.snd q
  refine h.congr fun t _ => ?_
  have hexp := g.expMap_smul_eq_proj_geodesicFlow hr1 P.proj P.snd t (by rw [hD]; exact mem_univ _)
  exact congrArg (fun z => g.inner P.proj P.snd P.snd * t ^ 2 - dist q z ^ 2) hexp

end DifferentialGeometry.Geometry.FiniteComparison
