import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveHinge
import DifferentialGeometry.Geometry.Collapse.SublevelCore.CommonOutwardDirection
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTube

/-!
# One outward direction for a point and a compact set, finite-order metric (CMS3-FLOW, POINT, G2)

Design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §0.9, §3 "POINT" (finite
LC52; the LC21 cone is dropped, review §12). On a complete manifold with a `C^(r+1)` metric (`r ≥ 2`) of
`sec ≥ 0`, for a point `p` and a compact `S` there is `A > 0` such that every `q` with `d(p, q) ≥ A`
carries one unit vector `w` with `g(w, v) < −1/2` for EVERY unit minimizing direction `v` from `q` to `p`
and EVERY one from `q` to `S`.

Route: the remote two-hinge argument of the smooth `exists_common_outward_direction`
(`Collapse/SublevelCore/CommonOutwardDirection.lean`) with the finite hinge
`dist_sq_le_hinge_finite` (CMS-B) and the real kernel `lt_neg_half_of_remote_two_hinge` (reused).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [I.Boundaryless] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- The `g_x`-unit sphere of a tangent space is compact. -/
theorem isCompact_unitSphere_outward {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M) :
    IsCompact {u : E | g.inner x u u = 1} := by
  obtain ⟨c, hc, hcoer⟩ := ContinuousLinearMap.isCoercive_of_posDef (F := E)
    (g.inner x : E →L[ℝ] E →L[ℝ] ℝ) (fun v hv => g.pos x v hv)
  have hcont : Continuous fun u : E => g.inner x u u := by
    let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner x
    exact B.continuous.clm_apply continuous_id
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq hcont continuous_const) ?_
  refine (Metric.isBounded_iff_subset_closedBall (0 : E)).mpr ⟨max 1 c⁻¹, fun u hu => ?_⟩
  rw [mem_closedBall, dist_zero_right]
  have h1 : c * ‖u‖ * ‖u‖ ≤ 1 := (hcoer u).trans_eq hu
  by_cases hu1 : ‖u‖ ≤ 1
  · exact hu1.trans (le_max_left _ _)
  · push Not at hu1
    have h2 : c * ‖u‖ ≤ 1 := by nlinarith
    have h3 : ‖u‖ ≤ 1 / c := (le_div_iff₀' hc).mpr h2
    rw [one_div] at h3
    exact h3.trans (le_max_right _ _)

/-- A unit minimizing direction from `q` to a closed `T` reaches `T` at distance `d(q, T)`. -/
theorem dist_expMap_minimizingDirection_outward
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {T : Set M} {q : M} {v : TangentSpace I q} (hv : v ∈ g.finiteMinimizingDirectionsTo T q) :
    dist q (g.expMap (⟨q, infDist q T • v⟩ : TangentBundle I M)) = infDist q T := by
  apply le_antisymm
  · have h := dist_proj_expMap_le_tube g hr hnorm (⟨q, infDist q T • v⟩ : TangentBundle I M)
    change dist q _ ≤ Real.sqrt (g.inner q (infDist q T • v) (infDist q T • v)) at h
    rw [DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self, hv.1, mul_one,
      Real.sqrt_sq infDist_nonneg] at h
    exact h
  · exact infDist_le_dist_of_mem hv.2

/-- **Finite LC52.** -/
theorem exists_common_outward_direction_finite [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (p : M) {S : Set M} (hS : IsCompact S) :
    ∃ A : ℝ, 0 < A ∧ ∀ q : M, A ≤ dist p q → ∃ w : E, g.inner q w w = 1 ∧
      ∀ v ∈ g.finiteMinimizingDirectionsTo {p} q ∪ g.finiteMinimizingDirectionsTo S q,
        g.inner q w v < -(1 / 2) := by
  classical
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨D, hD0, hSD⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ s ∈ S, dist p s ≤ D := by
    obtain ⟨C, hC⟩ := hS.isBounded.subset_closedBall p
    refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
    have := hC hs
    rw [mem_closedBall, dist_comm] at this
    exact this.trans (le_max_left _ _)
  by_contra hbad
  push Not at hbad
  choose q hq hqbad using fun n : ℕ => hbad ((n : ℝ) + 1) (by positivity)
  have hd (n : ℕ) : 0 < dist p (q n) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hq n]
  -- unit directions at `p` toward the bad points
  have hdir : ∀ n : ℕ, ∃ U : E, g.inner p U U = 1 ∧
      g.expMap (⟨p, dist p (q n) • U⟩ : TangentBundle I M) = q n := by
    intro n
    obtain ⟨U, hU⟩ := (g.finiteMinimizingDirectionsTo_nonempty_isCompact hr hnorm isClosed_singleton
      (singleton_nonempty (q n)) p).1
    refine ⟨U, hU.1, ?_⟩
    have h := hU.2
    rw [infDist_singleton] at h
    exact h
  choose U hU hUq using hdir
  obtain ⟨U0, hU0, φ, hφ, hlim⟩ := (isCompact_unitSphere_outward g p).tendsto_subseq hU
  change g.inner p U0 U0 = 1 at hU0
  have hdlim0 : Tendsto (fun n => dist p (q n)) atTop atTop :=
    tendsto_atTop.2 fun B => by
      obtain ⟨N, hN⟩ := exists_nat_gt B
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith [hq n]
  have hdlim := hdlim0.comp hφ.tendsto_atTop
  have hconv' : Tendsto (fun n => g.inner p (U (φ n)) U0) atTop (𝓝 (g.inner p U0 U0)) :=
    ((show Continuous fun u : E => g.inner p u U0 from
      (g.inner p).continuous.clm_apply continuous_const).tendsto U0).comp hlim
  rw [hU0] at hconv'
  obtain ⟨n, hn1, hn2⟩ := ((hconv'.eventually (lt_mem_nhds (by norm_num : (9 / 10 : ℝ) < 1))).and
    (hdlim.eventually (eventually_ge_atTop (10 * (D + 1))))).exists
  have hsym : 9 / 10 < g.inner p (U (φ n)) U0 := hn1
  have hconv2 : Tendsto (fun k => g.inner p (U (φ n)) (U (φ k))) atTop
      (𝓝 (g.inner p (U (φ n)) U0)) := ((g.inner p (U (φ n))).continuous.tendsto U0).comp hlim
  obtain ⟨k, hk1, hk2⟩ := ((hconv2.eventually (lt_mem_nhds hsym)).and
    (hdlim.eventually (eventually_ge_atTop (7 * dist p (q (φ n)))))).exists
  simp only [Function.comp_apply] at hn2 hk2
  set x₁ := q (φ n) with hx₁
  set x₂ := q (φ k) with hx₂
  have hr0 : 0 < dist p x₁ := hd (φ n)
  have hR0 : 0 < dist p x₂ := hd (φ k)
  -- the hinge at `p`
  have hmin1 : dist p (g.expMap (⟨p, dist p x₁ • U (φ n)⟩ : TangentBundle I M)) = dist p x₁ := by
    rw [hUq]
  have hmin2 : dist p (g.expMap (⟨p, dist p x₂ • U (φ k)⟩ : TangentBundle I M)) = dist p x₂ := by
    rw [hUq]
  have hfirst := dist_sq_le_hinge_finite g hr hnorm hsec p hr0 hR0 (hU _) (hU _) hmin1 hmin2
  rw [hUq, hUq] at hfirst
  -- the direction `w` from the bad point toward `x₂`
  have hβlow : dist p x₂ - dist p x₁ ≤ dist x₁ x₂ := by
    have := dist_triangle p x₁ x₂
    linarith
  have hβpos : 0 < dist x₁ x₂ := by linarith
  have hβR : dist x₁ x₂ ≤ dist p x₂ + dist p x₁ := by
    have := dist_triangle x₁ p x₂
    rw [dist_comm x₁ p] at this
    linarith
  obtain ⟨w, hw⟩ := (g.finiteMinimizingDirectionsTo_nonempty_isCompact hr hnorm isClosed_singleton
    (singleton_nonempty x₂) x₁).1
  have hwx : g.expMap (⟨x₁, dist x₁ x₂ • w⟩ : TangentBundle I M) = x₂ := by
    have h := hw.2
    rw [infDist_singleton] at h
    exact h
  obtain ⟨v, hv, hvw⟩ := hqbad (φ n) w hw.1
  -- the endpoint `s ∈ S ∪ {p}` of the minimizing direction `v`
  obtain ⟨s, a, hv1, hγ, hdist, hps⟩ : ∃ s : M, ∃ a : ℝ, g.inner x₁ v v = 1 ∧
      g.expMap (⟨x₁, a • v⟩ : TangentBundle I M) = s ∧ dist x₁ s = a ∧ dist p s ≤ D := by
    rcases hv with hvp | hvS
    · refine ⟨p, infDist x₁ {p}, hvp.1, hvp.2, ?_, by rw [dist_self]; exact hD0⟩
      rw [infDist_singleton]
    · refine ⟨_, _, hvS.1, rfl, dist_expMap_minimizingDirection_outward g hr1 hnorm hvS,
        hSD _ hvS.2⟩
  have har : |a - dist p x₁| ≤ D := by
    rw [← hdist, dist_comm p x₁]
    calc |dist x₁ s - dist x₁ p| ≤ dist s p := by
          rw [dist_comm x₁ s, dist_comm x₁ p]
          exact abs_dist_sub_le s p x₁
      _ ≤ D := by rw [dist_comm]; exact hps
  have ha : 0 < a := by
    have := (abs_le.mp har).1
    linarith
  -- the hinge at the bad point
  have hminA : dist x₁ (g.expMap (⟨x₁, a • v⟩ : TangentBundle I M)) = a := by rw [hγ, hdist]
  have hminB : dist x₁ (g.expMap (⟨x₁, dist x₁ x₂ • w⟩ : TangentBundle I M)) = dist x₁ x₂ := by
    rw [hwx]
  have hsecond0 := dist_sq_le_hinge_finite g hr hnorm hsec x₁ ha hβpos hv1 hw.1 hminA hminB
  have hsecond : dist s x₂ ^ 2 ≤
      a ^ 2 + dist x₁ x₂ ^ 2 - 2 * a * dist x₁ x₂ * g.inner x₁ v w := by
    have e1 : dist s x₂ = dist (g.expMap (⟨x₁, a • v⟩ : TangentBundle I M))
        (g.expMap (⟨x₁, dist x₁ x₂ • w⟩ : TangentBundle I M)) := by rw [hγ, hwx]
    rw [e1]
    exact hsecond0
  have hc : dist p x₂ - D ≤ dist s x₂ := by
    have := dist_triangle p s x₂
    linarith
  have hlt := Collapse.lt_neg_half_of_remote_two_hinge hD0 hn2 hk2 har ha hβpos (by linarith) hc
    hk1.le hfirst hsecond
  have hvw' : -(1 / 2) ≤ g.inner x₁ v w := by rw [g.symm]; exact hvw
  linarith

end DifferentialGeometry.Geometry.FiniteSoul
