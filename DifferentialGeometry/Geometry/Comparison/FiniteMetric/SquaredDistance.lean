import DifferentialGeometry.Geometry.Comparison.FiniteMetric.RiemannianHinge
import DifferentialGeometry.Geometry.Comparison.GermAngle

/-!
# CM5.d: squared-distance comparison and arm-wise monotonicity for a finite metric (LFR55)

Lane CM-A2, 2026-10-04 (addition requested by the lead after the external review of the
foundations design, §2.8). For a complete finite-regularity metric with `sec_g ≥ 0` everywhere
(LFR55's setting), with the global four-point comparison of CM-A
(`fourPointComparison_zero_univ_finite`):

* `convexOn_sq_sub_sq_dist_of_fourPointComparison` (metric kernel) and
  `convexOn_sq_sub_sq_dist_finite`: along every isometric segment `σ` (unit-speed minimizing
  geodesic) and for every `q`, `t ↦ t² - d(q, σ t)²` is convex;
* `sq_dist_le_point_on_side_finite`: the point-on-side inequality it comes from;
* `sq_dist_expMap_le_finite`: the hinge in distance form,
  `d(exp_p (a v), exp_p (b w))² ≤ a² + b² - 2ab g_p(v,w) = |a v - b w|²_{g_p}` (from CM5.b);
* `comparisonAngle_expMap_antitone_finite`: the comparison angle `θ_{v,w}(s, t)` of the hinge is
  nonincreasing in EACH arm length separately while both arms stay minimizing (the tree's
  `comparisonAngleNegCurvature_antitone_on_segments`).

Not covered here: LFR55's convexity along NON-minimizing unit-speed geodesics (needs: short
geodesic arcs minimize, CM-N's CM1.d/e, and local-to-global convexity on an interval).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

/-- **Metric kernel.** Under the four-point comparison at curvature `0`, `t ↦ t² - d(q, σ t)²` is
convex along every isometric segment `σ` of the comparison set. -/
theorem convexOn_sq_sub_sq_dist_of_fourPointComparison {X : Type*} [MetricSpace X] {S : Set X}
    (hS : fourPointComparison 0 S) {J : Set ℝ} (hJ : Convex ℝ J) {σ : ℝ → X}
    (hσ : ∀ s ∈ J, ∀ t ∈ J, dist (σ s) (σ t) = |s - t|) (hmem : ∀ t ∈ J, σ t ∈ S)
    {q : X} (hq : q ∈ S) :
    ConvexOn ℝ J (fun t => t ^ 2 - dist q (σ t) ^ 2) := by
  refine ⟨hJ, fun x hx y hy a b ha hb hab => ?_⟩
  have hm : a • x + b • y ∈ J := hJ hx hy ha hb hab
  simp only [smul_eq_mul] at hm ⊢
  have ha' : a = 1 - b := by linarith
  subst ha'
  have hxm : dist (σ x) (σ ((1 - b) * x + b * y)) = b * dist (σ x) (σ y) := by
    rw [hσ x hx _ hm, hσ x hx y hy, show x - ((1 - b) * x + b * y) = b * (x - y) by ring,
      abs_mul, abs_of_nonneg hb]
  have hmy : dist (σ ((1 - b) * x + b * y)) (σ y) = (1 - b) * dist (σ x) (σ y) := by
    rw [hσ _ hm y hy, hσ x hx y hy, show (1 - b) * x + b * y - y = (1 - b) * (x - y) by ring,
      abs_mul, abs_of_nonneg ha]
  have hk := quadratic_side_comparison_of_fourPointComparison hS (hmem x hx) (hmem y hy)
    (hmem _ hm) hq ⟨hb, by linarith⟩ hxm hmy
  rw [hσ x hx y hy, sq_abs] at hk
  nlinarith

end DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.FiniteComparison

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **Point-on-side comparison** for a complete finite metric with `sec ≥ 0`: if `z` divides a
segment `[a, b]` in the ratio `t : 1 - t`, then
`(1 - t) d(v,a)² + t d(v,b)² - t(1 - t) d(a,b)² ≤ d(v,z)²`. -/
theorem sq_dist_le_point_on_side_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {a b z v : M} {t : ℝ} (ht : t ∈ Icc 0 1) (haz : dist a z = t * dist a b)
    (hzb : dist z b = (1 - t) * dist a b) :
    (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 - t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2 := by
  have hn : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
    have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
    calc (2 : ℕ∞ω) = 1 + 1 := by norm_num
      _ ≤ (r : ℕ∞ω) + 1 := by gcongr; simpa using h1
  exact quadratic_side_comparison_of_fourPointComparison
    (fourPointComparison_zero_univ_finite g hn hnorm hsec)
    (mem_univ a) (mem_univ b) (mem_univ z) (mem_univ v) ht haz hzb

/-- **LFR55, convexity of `t² - d(q, σ t)²`** along every isometric segment (unit-speed minimizing
geodesic) of a complete finite metric with `sec ≥ 0`. -/
theorem convexOn_sq_sub_sq_dist_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {J : Set ℝ} (hJ : Convex ℝ J) {σ : ℝ → M}
    (hσ : ∀ s ∈ J, ∀ t ∈ J, dist (σ s) (σ t) = |s - t|) (q : M) :
    ConvexOn ℝ J (fun t => t ^ 2 - dist q (σ t) ^ 2) := by
  have hn : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
    have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
    calc (2 : ℕ∞ω) = 1 + 1 := by norm_num
      _ ≤ (r : ℕ∞ω) + 1 := by gcongr; simpa using h1
  exact convexOn_sq_sub_sq_dist_of_fourPointComparison
    (fourPointComparison_zero_univ_finite g hn hnorm hsec) hJ hσ (fun _ _ => mem_univ _)
    (mem_univ q)

/-- **LFR55 on a minimizing exponential ray**: if `t ↦ exp_o (t u)` (unit `u`) realizes the
distance at time `a`, then `t ↦ t² - d(q, exp_o (t u))²` is convex on `[0, a]`. -/
theorem convexOn_sq_sub_sq_dist_expMap_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {o : M} {u : E} {a : ℝ} (hu : g.inner o u u = 1)
    (hmin : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a) (q : M) :
    ConvexOn ℝ (Icc 0 a)
      (fun t => t ^ 2 - dist q (g.expMap (⟨o, t • u⟩ : TangentBundle I M)) ^ 2) :=
  convexOn_sq_sub_sq_dist_finite g hr hnorm hsec (convex_Icc 0 a)
    (g.dist_expMap_smul_eq_of_dist_eq hr hnorm hu hmin).2 q

/-- **LFR55, the hinge in distance form**: for a minimizing hinge at `o` with unit initial vectors
`u, v` and arm lengths `a, b`, `d(exp_o (a u), exp_o (b v))² ≤ a² + b² - 2ab g_o(u, v)`
(`= |a u - b v|²_{g_o}`). -/
theorem sq_dist_expMap_le_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) (u v : E) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b) :
    dist (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) ^ 2
      ≤ a ^ 2 + b ^ 2 - 2 * a * b * g.inner o u v := by
  have h := comparisonAngle_le_arccos_inner_finite g hr hnorm o u v ha hb hu hv hminA hminB hsec
  have hlow := abs_dist_sub_le (g.expMap (⟨o, a • u⟩ : TangentBundle I M))
    (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) o
  rw [dist_comm _ o, dist_comm _ o, hminA, hminB] at hlow
  have hup := dist_triangle (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) o
    (g.expMap (⟨o, b • v⟩ : TangentBundle I M))
  rw [dist_comm _ o, hminA, hminB] at hup
  have hcs := DifferentialGeometry.Geometry.Collapse.abs_finite_inner_le g o u v
  rw [hu, hv, Real.sqrt_one, one_mul] at hcs
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (comparisonAngle_mem_Icc _ _ _).1
    (Real.arccos_le_pi _) h
  rw [Real.cos_arccos (abs_le.mp hcs).1 (abs_le.mp hcs).2, cos_comparisonAngle ha hb hlow hup,
    le_div_iff₀ (by positivity)] at hcos
  linarith

/-- **LFR55, arm-wise monotonicity**: the comparison angle `θ(s, t)` of a minimizing hinge
`(exp_o (s u), o, exp_o (t v))` is nonincreasing in EACH arm length separately on
`(0, a] × (0, b]` (in particular `0 < a' ≤ a'' ≤ a ⇒ θ(a'', t) ≤ θ(a', t)`, and symmetrically). -/
theorem comparisonAngle_expMap_antitone_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) (u v : E) {a b : ℝ} (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b) :
    DifferentialGeometry.Toponogov.CoordinatewiseNonincreasingOn a b
      (fun s t => comparisonAngle s t (dist (g.expMap (⟨o, s • u⟩ : TangentBundle I M))
        (g.expMap (⟨o, t • v⟩ : TangentBundle I M)))) := by
  have hn : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
    have h1 : ((1 : ℕ∞) : ℕ∞ω) ≤ (r : ℕ∞ω) := by exact_mod_cast hr
    calc (2 : ℕ∞ω) = 1 + 1 := by norm_num
      _ ≤ (r : ℕ∞ω) + 1 := by gcongr; simpa using h1
  obtain ⟨hγrad, hγmin⟩ := g.dist_expMap_smul_eq_of_dist_eq hr hnorm hu hminA
  obtain ⟨hβrad, hβmin⟩ := g.dist_expMap_smul_eq_of_dist_eq hr hnorm hv hminB
  have h := comparisonAngleNegCurvature_antitone_on_segments le_rfl
    (fourPointComparison_zero_univ_finite g hn hnorm hsec) (mem_univ o)
    (γ := fun s => g.expMap (⟨o, s • u⟩ : TangentBundle I M))
    (β := fun t => g.expMap (⟨o, t • v⟩ : TangentBundle I M))
    (fun s hs => hγrad s (Ioc_subset_Icc_self hs)) (fun t ht => hβrad t (Ioc_subset_Icc_self ht))
    (fun s hs t ht => hγmin s (Ioc_subset_Icc_self hs) t (Ioc_subset_Icc_self ht))
    (fun s hs t ht => hβmin s (Ioc_subset_Icc_self hs) t (Ioc_subset_Icc_self ht))
    (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
  simpa only [comparisonAngleNegCurvature_zero] using h

end DifferentialGeometry.Geometry.FiniteComparison
