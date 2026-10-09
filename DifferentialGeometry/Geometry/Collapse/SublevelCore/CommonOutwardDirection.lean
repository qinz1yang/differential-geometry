import DifferentialGeometry.Geometry.Collapse.SublevelCore.Defs
import DifferentialGeometry.Geometry.Comparison.Soul.NoncriticalDistance

/-!
# One outward direction for a point and a compact set (LC52)

Frozen blueprint master207A, lemma `lem:collapse-common-outward-direction` (LC52, lines
22729–22782). On a complete connected manifold with `sec ≥ 0`, for a point `p` and a compact set
`S` there is `A > 0` such that at every `q` with `d(p, q) ≥ A` one unit vector `w` satisfies
`g(w, v) < -1/2` for EVERY inward unit direction `v` minimizing the distance to `p` and EVERY
inward unit direction `v` realizing the distance to `S`.

Route. The blueprint proves this from the supplied LC21 cone at infinity and LC25's outward point.
We use instead the PC remote-hinge argument of `minimizing_directions_close_at_infinity`
(`Soul/SoulAngles.lean`): by contradiction take bad points `q_n → ∞`, extract converging unit
directions at `p`, and compare one bad `q` with a much farther `x` whose direction at `p` is close.
The sec ≥ 0 hinge at `p` makes `d(q, x)` short, and the hinge at `q` against any `s ∈ S ∪ {p}`
then forces the direction `w` from `q` to `x` to be almost opposite to every minimizing direction.
The arithmetic is the kernel `lt_neg_half_of_remote_two_hinge`.

This drops three hypotheses of the blueprint row: the LC21 cone package, noncompactness of the
manifold and nonemptiness of `S` (the conclusion is vacuous or trivial without them). The
verbatim-hypothesis form is recorded as an `example` at the end.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

/-- **Kernel of LC52: remote two-hinge arithmetic.** Let `q` be at distance `r` from `p`, with
`S ∪ {p}` inside the `D`-ball about `p` and `r ≥ 10 (D + 1)`. Let `x` be at distance `R ≥ 7r` from
`p`, with the hinge at `p` giving `β² ≤ r² + R² - 2 r R κ`, `κ ≥ 9/10`, where `β = d(q, x)`. Let
`s` be at distance `a` from `q` with `|a - r| ≤ D` and `d(s, x) = c ≥ R - D`, and let the hinge at `q`
give `c² ≤ a² + β² - 2 a β z`. Then `z < -1/2`. -/
theorem lt_neg_half_of_remote_two_hinge {D r R a β c κ z : ℝ} (hD : 0 ≤ D)
    (hr : 10 * (D + 1) ≤ r) (hR : 7 * r ≤ R) (har : |a - r| ≤ D) (ha : 0 < a) (hβ : 0 < β)
    (hβR : β ≤ R + r) (hc : R - D ≤ c) (hκ : 9 / 10 ≤ κ)
    (hβsq : β ^ 2 ≤ r ^ 2 + R ^ 2 - 2 * r * R * κ)
    (hcsq : c ^ 2 ≤ a ^ 2 + β ^ 2 - 2 * a * β * z) : z < -(1 / 2) := by
  by_contra hz
  push Not at hz
  have hr0 : 0 < r := by linarith
  have hR0 : 0 < R := by linarith
  have hDr : 10 * D ≤ r := by linarith
  have haub : a ≤ r + D := by linarith [(abs_le.mp har).2]
  have haβ : 0 < a * β := mul_pos ha hβ
  have h1 : -(2 * a * β * z) ≤ a * β := by nlinarith
  have h2 : (R - D) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by linarith) hc 2
  have h3 : a * β ≤ (r + D) * (R + r) :=
    mul_le_mul haub hβR hβ.le (by linarith)
  have h4 : r * R * (9 / 10) ≤ r * R * κ := mul_le_mul_of_nonneg_left hκ (by positivity)
  have h5 : a ^ 2 ≤ (r + D) ^ 2 := pow_le_pow_left₀ ha.le haub 2
  have h6 : (r + D) ^ 2 ≤ (121 / 100) * r ^ 2 := by nlinarith
  have h7 : (r + D) * (R + r) ≤ (11 / 10) * r * (R + r) := by nlinarith
  have h8 : R * D ≤ R * r / 10 := by nlinarith
  have h9 : 7 * r ^ 2 ≤ r * R := by nlinarith
  have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- The Riemannian distance of the PC setting, as a real number, is the metric distance. -/
theorem riemannianEDist_toReal_eq_dist (x y : M) :
    (riemannianEDist I x y).toReal = dist x y := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

omit [ConnectedSpace M] in
/-- A unit geodesic from `q` that ends in `S` at time `infDist q S` realizes that distance. -/
theorem dist_intrinsicGeodesic_infDist_eq
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {S : Set M} {q : M} {v : TangentSpace I q} (hv : v ∈ minimizingDirectionsTo (I := I) g hEnorm S q) :
    dist q (intrinsicGeodesic (I := I) g hEnorm q v (infDist q S)) = infDist q S := by
  apply le_antisymm
  · have hle := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm q v
      (infDist_nonneg : (0 : ℝ) ≤ infDist q S)
    rw [intrinsicGeodesic_zero, hv.1, Real.sqrt_one, one_mul, sub_zero,
      ← IsRiemannianManifold.out (I := I), edist_dist] at hle
    exact (ENNReal.ofReal_le_ofReal_iff infDist_nonneg).mp hle
  · exact infDist_le_dist_of_mem hv.2

/-- **LC52** (strengthened: no cone package, no noncompactness, `S` may be empty). On a complete
connected manifold with `sec ≥ 0`, for every compact `S` there is `A > 0` such that each `q` with
`d(p, q) ≥ A` carries one unit vector `w` with `g(w, v) < -1/2` for every inward unit direction
minimizing the distance to `p` and every one realizing the distance to `S`. -/
theorem exists_common_outward_direction
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) {S : Set M} (hS : IsCompact S) :
    ∃ A : ℝ, 0 < A ∧ ∀ q : M, A ≤ dist p q → ∃ w : TangentSpace I q, g.inner q w w = 1 ∧
      ∀ v ∈ inwardMinimizingDirections (I := I) g hEnorm p q ∪
          minimizingDirectionsTo (I := I) g hEnorm S q,
        g.inner q w v < -(1 / 2) := by
  classical
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
  choose U hU hUq using fun n => soul_unit_minimizing_initial (I := I) g hEnorm p (q n) (hd n)
  obtain ⟨U0, hU0, φ, hφ, hlim⟩ := (gUnitSphere_isCompact (I := I) g p).tendsto_subseq hU
  change g.inner p U0 U0 = 1 at hU0
  have hdlim0 : Tendsto (fun n => dist p (q n)) atTop atTop :=
    tendsto_atTop.2 fun B => by
      obtain ⟨N, hN⟩ := exists_nat_gt B
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith [hq n]
  have hdlim := hdlim0.comp hφ.tendsto_atTop
  have hconv := ((g.inner p U0).continuous.tendsto U0).comp hlim
  rw [hU0] at hconv
  obtain ⟨n, hn1, hn2⟩ := ((hconv.eventually (lt_mem_nhds (by norm_num : (9 / 10 : ℝ) < 1))).and
    (hdlim.eventually (eventually_ge_atTop (10 * (D + 1))))).exists
  have hsym : 9 / 10 < g.inner p (U (φ n)) U0 := by
    rw [g.symm]
    exact hn1
  have hconv2 := ((g.inner p (U (φ n))).continuous.tendsto U0).comp hlim
  obtain ⟨k, hk1, hk2⟩ := ((hconv2.eventually (lt_mem_nhds hsym)).and
    (hdlim.eventually (eventually_ge_atTop (7 * dist p (q (φ n)))))).exists
  simp only [Function.comp_apply] at hn1 hn2 hk1 hk2
  -- Notation: the bad point `q (φ n)` and the far point `x = q (φ k)`.
  have hr0 : 0 < dist p (q (φ n)) := hd (φ n)
  have hR0 : 0 < dist p (q (φ k)) := hd (φ k)
  -- The hinge at `p`.
  have hmin1 : (riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p (U (φ n))
      (dist p (q (φ n))))).toReal = dist p (q (φ n)) := by
    rw [hUq, riemannianEDist_toReal_eq_dist (I := I)]
  have hfirst := complete_hinge_sq (I := I) g hEnorm hsec p (U (φ n)) (U (φ k))
    (dist p (q (φ n))) (dist p (q (φ k))) hr0 hR0 (hU _) (hU _) hmin1
  rw [hUq, hUq, riemannianEDist_toReal_eq_dist (I := I)] at hfirst
  -- The direction `w` from the bad point toward `x`.
  have hβlow : dist p (q (φ k)) - dist p (q (φ n)) ≤ dist (q (φ n)) (q (φ k)) := by
    have := dist_triangle p (q (φ n)) (q (φ k))
    linarith
  have hβpos : 0 < dist (q (φ n)) (q (φ k)) := by linarith
  have hβR : dist (q (φ n)) (q (φ k)) ≤ dist p (q (φ k)) + dist p (q (φ n)) := by
    have := dist_triangle (q (φ n)) p (q (φ k))
    rw [dist_comm (q (φ n)) p] at this
    linarith
  obtain ⟨w, hw, hwx⟩ := soul_unit_minimizing_initial (I := I) g hEnorm (q (φ n)) (q (φ k)) hβpos
  obtain ⟨v, hv, hvw⟩ := hqbad (φ n) w hw
  -- The endpoint `s ∈ S ∪ {p}` of the minimizing direction `v`.
  obtain ⟨s, a, hv1, hγ, hdist, hps⟩ : ∃ s : M, ∃ a : ℝ, g.inner (q (φ n)) v v = 1 ∧
      intrinsicGeodesic (I := I) g hEnorm (q (φ n)) v a = s ∧ dist (q (φ n)) s = a ∧
      dist p s ≤ D := by
    rcases hv with hvp | hvS
    · exact ⟨p, dist p (q (φ n)), hvp.1, hvp.2, dist_comm _ _, by rw [dist_self]; exact hD0⟩
    · exact ⟨_, _, hvS.1, rfl, dist_intrinsicGeodesic_infDist_eq (I := I) g hEnorm hvS,
        hSD _ hvS.2⟩
  have har : |a - dist p (q (φ n))| ≤ D := by
    rw [← hdist, dist_comm p (q (φ n))]
    calc |dist (q (φ n)) s - dist (q (φ n)) p| ≤ dist s p := by
          rw [dist_comm (q (φ n)) s, dist_comm (q (φ n)) p]
          exact abs_dist_sub_le s p (q (φ n))
      _ ≤ D := by rw [dist_comm]; exact hps
  have ha : 0 < a := by
    have := (abs_le.mp har).1
    linarith
  -- The hinge at the bad point.
  have hmin2 : (riemannianEDist I (q (φ n)) (intrinsicGeodesic (I := I) g hEnorm (q (φ n)) v a)).toReal
      = a := by
    rw [hγ, riemannianEDist_toReal_eq_dist (I := I), hdist]
  have hsecond := complete_hinge_sq (I := I) g hEnorm hsec (q (φ n)) v w a
    (dist (q (φ n)) (q (φ k))) ha hβpos hv1 hw hmin2
  rw [hγ, hwx, riemannianEDist_toReal_eq_dist (I := I)] at hsecond
  have hc : dist p (q (φ k)) - D ≤ dist s (q (φ k)) := by
    have := dist_triangle p s (q (φ k))
    linarith
  have hlt := lt_neg_half_of_remote_two_hinge hD0 hn2 hk2 har ha hβpos (by linarith) hc
    hk1.le hfirst hsecond
  rw [g.symm] at hvw
  linarith

/-- The verbatim hypothesis list of LC52 (noncompact model, nonempty compact `S`); the LC21 cone
package of the blueprint is not needed and has no Lean counterpart here. -/
example [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hsec : ∀ y : M, metricRm04At (I := I) g y ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) {S : Set M} (hSne : S.Nonempty) (hS : IsCompact S) :
    ∃ A : ℝ, 0 < A ∧ ∀ q : M, A ≤ dist p q → ∃ w : TangentSpace I q, g.inner q w w = 1 ∧
      ∀ v ∈ inwardMinimizingDirections (I := I) g hEnorm p q ∪
          minimizingDirectionsTo (I := I) g hEnorm S q,
        g.inner q w v < -(1 / 2) :=
  hSne.elim fun _ _ => exists_common_outward_direction g hEnorm hsec p hS

end DifferentialGeometry.Geometry.Collapse
