import DifferentialGeometry.Geometry.Collapse.SublevelCore.F5aApplications
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.QuadraticBounds

/-!
# LC57 and LC61, compact branch: one scale, one tail, global sublevels and open balls

Master207A, A:23106 (LC57) and A:23460 (LC61), the branch of a compact model `(N, g, n)`. The maps
`j i : N → M i` are global (the LC56 exhaustion applied to `N` itself, as in the blueprint), and the
pullbacks converge to `g` in `C⁰` on `N`. The scale `R ≥ T` is chosen after the model and before the
index (LC43's diameter condition `2 diam/R + e < 1/5`); then for every family of selected radial
functions with value error `e` at that scale, one tail has: every radial sublevel `{η i ≤ ρ}`,
`ρ ≥ 1/5`, is all of `M i`; every open distance ball `B(p_i, ρ R)`, `ρ ≥ 1/5`, is all of `M i`; and
`j i` is a diffeomorphism `N ≃ M i`. In particular the open balls of LC61 have the smooth type of
`N` directly, without LC60.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
  [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [∀ i, IsRiemannianManifold I (M i)]
  [∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- **LC57 + LC61, compact branch.** For a compact model with global maps whose pullbacks converge
to `g` in `C⁰`, there is a scale `R > T` such that for every family of radial functions `η i` with
value error `e < 1/5` relative to `d_{g_i}(p_i, ·)/R` on a tail, one tail has all radial sublevels
`{η i ≤ ρ}` and all open distance balls `B(p_i, ρ R)`, `ρ ≥ 1/5`, equal to `M i`, and `j i` is a
diffeomorphism `N ≃ M i`. -/
theorem exists_scale_eventually_compact_joint_type [CompactSpace N] [Nonempty N]
    [∀ i, ConnectedSpace (M i)] (g : SmoothRiemannianMetric I N) (hNorm : IsMetricNorm g)
    (n : N) (hSeq : ℕ → SmoothRiemannianMetric I N)
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞) (hj : ∀ i, (j i).source = univ)
    (hmetric : ∀ i, ∀ x : N, ∀ v w : TangentSpace I x,
      (hSeq i).inner x v w = (gSeq i).inner (j i x)
        (mfderiv I I (j i : N → M i) x v) (mfderiv I I (j i : N → M i) x w))
    (hconv : MetricCPConvergenceOn univ 0 hSeq g g) {e T : ℝ} (he : e < 1 / 5) :
    ∃ R : ℝ, T < R ∧ 0 < R ∧ ∀ η : ∀ i, M i → ℝ,
      (∀ᶠ i in atTop, ∀ y, |η i y - dist (j i n) y / R| < e) →
      ∀ᶠ i in atTop, (∀ ρ : ℝ, 1 / 5 ≤ ρ → {y | η i y ≤ ρ} = univ) ∧
        (∀ ρ : ℝ, 1 / 5 ≤ ρ → Metric.ball (j i n) (ρ * R) = univ) ∧
        ∃ d : Diffeomorph I I N (M i) ∞, ∀ x, d x = j i x := by
  have hdN (x y : N) : riemannianEDistOf g x y = edist x y := by
    rw [riemannianEDistOf_eq_riemannianEDist g hNorm, ← IsRiemannianManifold.out (I := I)]
  have hdM (i : ℕ) (x y : M i) : riemannianEDistOf (gSeq i) x y = edist x y := by
    rw [riemannianEDistOf_eq_riemannianEDist (gSeq i) (hSeqNorm i),
      ← IsRiemannianManifold.out (I := I)]
  obtain ⟨D₀, hD₀⟩ := (isCompact_univ (X := N)).isBounded.subset_closedBall n
  set D : ℝ := max D₀ 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  have hD : ∀ x, riemannianEDistOf g n x ≤ ENNReal.ofReal D := by
    intro x
    rw [hdN, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have h := hD₀ (mem_univ x)
    rw [Metric.mem_closedBall, dist_comm] at h
    exact h.trans (le_max_left _ _)
  obtain ⟨R, hTR, hR0, hsmall⟩ := exists_scale_two_mul_div_add_lt (D := D) (R₀ := T) he
  refine ⟨R, hTR, hR0, fun η hη => ?_⟩
  have hupper : ∀ᶠ i in atTop, ∀ z (v : TangentSpace I z),
      (gSeq i).inner (j i z) (mfderiv I I (j i : N → M i) z v)
        (mfderiv I I (j i : N → M i) z v) ≤ 4 * g.inner z v v := by
    filter_upwards [hconv.eventually_quadratic_bounds isCompact_univ (by norm_num : (0 : ℝ) < 3)]
      with i hi z v
    have h := (hi z (mem_univ z) v).2
    rw [hmetric i z v v] at h
    linarith
  filter_upwards [hη, hupper] with i hηi hup
  have hη' : ∀ y, |η i y - (riemannianEDistOf (gSeq i) (j i n) y).toReal / R| < e := by
    intro y
    rw [hdM, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    exact hηi y
  obtain ⟨hsub, d, hd⟩ := compact_alternative_sublevel_type (N := N) g (gSeq i) (j i) (hj i) hup
    n hR0 hD0 hD hη' hsmall
  refine ⟨hsub, fun ρ hρ => ?_, d, hd⟩
  have he0 : 0 < e := by
    have h := hηi (j i n)
    exact (abs_nonneg _).trans_lt h
  have h2D : 2 * D < ρ * R := by
    have h1 : 2 * D / R < 1 / 5 := by linarith
    have h2 : 2 * D < 1 / 5 * R := by rwa [div_lt_iff₀ hR0] at h1
    nlinarith
  apply eq_univ_of_forall
  intro y
  obtain ⟨x, rfl⟩ : ∃ x, j i x = y := ⟨d.symm y, by rw [← hd, d.apply_symm_apply]⟩
  have hmap := riemannianEDistOf_map_le_two_mul g (gSeq i) (j i) (hj i) hup n x
  rw [hdM, hdN, edist_dist, edist_dist] at hmap
  have hle : dist (j i n) (j i x) ≤ 2 * D := by
    have h3 : ENNReal.ofReal (dist (j i n) (j i x)) ≤ ENNReal.ofReal (2 * D) := by
      calc ENNReal.ofReal (dist (j i n) (j i x)) ≤ 2 * ENNReal.ofReal (dist n x) := hmap
        _ = ENNReal.ofReal (2 * dist n x) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        _ ≤ ENNReal.ofReal (2 * D) := by
          apply ENNReal.ofReal_le_ofReal
          have h := hD₀ (mem_univ x)
          rw [Metric.mem_closedBall, dist_comm] at h
          linarith [le_max_left D₀ 0]
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  rw [Metric.mem_ball, dist_comm]
  linarith

end DifferentialGeometry.Geometry.Collapse
