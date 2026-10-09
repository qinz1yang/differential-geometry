import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

universe u v w

variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
variable [ProperSpace X] [ProperSpace Y] {p : X} {q : Y}

theorem exists_isometryEquiv_of_pointed_approximations
    {R ε : ℕ → ℝ} (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (f : ∀ n, PointedBallApprox p q (R n) (ε n)) :
    ∃ e : X ≃ᵢ Y, e p = q := by
  classical
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  let g (n : ℕ) (x : X) : Y :=
    if hx : dist x p ≤ R n then (f n).toFun ⟨x, hx⟩ else q
  have hg (n : ℕ) (x : BallCarrier p (R n)) : g n x.val = (f n).toFun x := by
    simp only [g, dite_eq_left x.property]
  have hdom (x : X) : ∀ᶠ n in atTop, dist x p ≤ R n :=
    hR.eventually (eventually_ge_atTop (dist x p))
  have hεone : ∀ᶠ n in atTop, ε n ≤ 1 :=
    hε.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hcompact (x : X) :
      ∃ y ∈ closedBall q (dist x p + 1), Tendsto (fun n => g n x) U (𝓝 y) := by
    apply (isCompact_closedBall q (dist x p + 1)).ultrafilter_le_nhds
      (Ultrafilter.map (fun n => g n x) U)
    apply le_principal_iff.mpr
    change ∀ᶠ n in (U : Filter ℕ), g n x ∈ closedBall q (dist x p + 1)
    apply hU
    filter_upwards [hdom x, hεone] with n hn hne
    rw [show g n x = (f n).toFun ⟨x, hn⟩ from hg n ⟨x, hn⟩]
    have hr := (f n).radial_upper ⟨x, hn⟩
    change dist ((f n).toFun ⟨x, hn⟩) q ≤ dist x p + 1
    linarith
  choose F hFball hconv using hcompact
  have hFiso : Isometry F := by
    apply Isometry.of_dist_eq
    intro x x'
    have hdist : ∀ᶠ n in (U : Filter ℕ),
        |dist (g n x) (g n x') - dist x x'| ≤ ε n := by
      apply hU
      filter_upwards [hdom x, hdom x'] with n hn hn'
      rw [show g n x = (f n).toFun ⟨x, hn⟩ from hg n ⟨x, hn⟩,
        show g n x' = (f n).toFun ⟨x', hn'⟩ from hg n ⟨x', hn'⟩]
      exact (f n).distortion _ _ |>.le
    have hzero : |dist (F x) (F x') - dist x x'| ≤ 0 :=
      le_of_tendsto_of_tendsto
        (((hconv x).dist (hconv x')).sub tendsto_const_nhds).abs
        (hε.mono_left hU) hdist
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hzero)
  have hpq : F p = q := by
    have hgp : ∀ n, g n p = q := by
      intro n
      have hp : dist p p ≤ R n := by
        rw [dist_self]
        exact le_of_lt (lt_trans (f n).error_pos (f n).error_lt_radius)
      rw [show g n p = (f n).toFun ⟨p, hp⟩ from hg n ⟨p, hp⟩]
      exact (f n).basepoint
    have hq : Tendsto (fun n => g n p) U (𝓝 q) := by
      simpa only [hgp] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => q) U (𝓝 q))
    exact tendsto_nhds_unique (hconv p) hq
  have hsurj : Function.Surjective F := by
    intro y
    let z (n : ℕ) : BallCarrier p (R n) :=
      if h : ∃ x : BallCarrier p (R n), dist y ((f n).toFun x) < ε n then h.choose
      else ⟨p, by
        rw [dist_self]
        exact le_of_lt (lt_trans (f n).error_pos (f n).error_lt_radius)⟩
    have hz : ∀ᶠ n in atTop, dist y ((f n).toFun (z n)) < ε n := by
      filter_upwards [hR.eventually (eventually_ge_atTop (dist y q + 1)), hεone]
        with n hn hne
      have hex := (f n).coverage y (by linarith)
      simpa only [z, dite_eq_left hex] using hex.choose_spec
    have hzball : ∀ᶠ n in atTop, (z n).val ∈ closedBall p (dist y q + 2) := by
      filter_upwards [hz, hεone] with n hn hne
      have hr := (f n).radial_lower (z n)
      have ht := dist_triangle ((f n).toFun (z n)) y q
      rw [dist_comm ((f n).toFun (z n)) y] at ht
      change dist (z n).val p ≤ dist y q + 2
      linarith
    obtain ⟨x, _, hx⟩ := (isCompact_closedBall p (dist y q + 2)).ultrafilter_le_nhds
      (Ultrafilter.map (fun n => (z n).val) U)
      (le_principal_iff.mpr (hU hzball))
    change Tendsto (fun n => (z n).val) U (𝓝 x) at hx
    have heU := hε.mono_left hU
    have hzU := tendsto_iff_dist_tendsto_zero.mp hx
    have hfxU := tendsto_iff_dist_tendsto_zero.mp (hconv x)
    have hsum : Tendsto
        (fun n => ε n + (dist (z n).val x + ε n) + dist (g n x) (F x))
        U (𝓝 (0 : ℝ)) := by
      simpa only [zero_add, add_zero] using (heU.add (hzU.add heU)).add hfxU
    have hle : ∀ᶠ n in (U : Filter ℕ),
        dist y (F x) ≤ ε n + (dist (z n).val x + ε n) + dist (g n x) (F x) := by
      filter_upwards [hU hz, hU (hdom x)] with n hn hnx
      have hd := (abs_lt.mp ((f n).distortion (z n) ⟨x, hnx⟩)).2
      have ht := dist_triangle4 y ((f n).toFun (z n)) (g n x) (F x)
      rw [show g n x = (f n).toFun ⟨x, hnx⟩ from hg n ⟨x, hnx⟩] at ht ⊢
      linarith only [hn, hd, ht]
    have heq : y = F x :=
      dist_le_zero.mp (le_of_tendsto_of_tendsto tendsto_const_nhds hsum hle)
    exact ⟨x, heq.symm⟩
  let e : X ≃ᵢ Y := {
    toEquiv := Equiv.ofBijective F ⟨hFiso.injective, hsurj⟩
    isometry_toFun := hFiso
  }
  exact ⟨e, hpq⟩

theorem exists_isometryEquiv_of_forall_pointed_approximation
    (h : ∀ R ε : ℝ, 0 < ε → ε < R → Nonempty (PointedBallApprox p q R ε)) :
    ∃ e : X ≃ᵢ Y, e p = q := by
  classical
  let R : ℕ → ℝ := fun n => (n : ℝ) + 2
  let ε : ℕ → ℝ := fun n => 1 / R n
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hR
  have hpos (n : ℕ) : 0 < ε n := by
    dsimp only [ε, R]
    positivity
  have hlt (n : ℕ) : ε n < R n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hle : 1 / ((n : ℝ) + 2) ≤ 1 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    dsimp only [ε, R]
    linarith
  exact exists_isometryEquiv_of_pointed_approximations hR hε
    (fun n => Classical.choice (h (R n) (ε n) (hpos n) (hlt n)))

theorem PointedGHConverges.exists_isometryEquiv
    {Z : ℕ → Type w} [∀ n, MetricSpace (Z n)] {o : ∀ n, Z n}
    (hX : PointedGHConverges o p) (hY : PointedGHConverges o q) :
    ∃ e : X ≃ᵢ Y, e p = q := by
  apply exists_isometryEquiv_of_forall_pointed_approximation
  intro R ε hε hεR
  have hη : 0 < ε / 20 := by linarith
  have hηR : ε / 20 < 4 * (R + 1) + 4 := by linarith
  obtain ⟨n, hnX, hnY⟩ :=
    ((hX.eventually_approx hη hηR).and (hY.eventually_approx hη hηR)).exists
  obtain ⟨f⟩ := hnX
  obtain ⟨g⟩ := hnY
  let fg := commonSourceComparison (j := R + 1) f g (by linarith) (by linarith)
  have hrestrict := fg.restrict (s := R) (by linarith) (by linarith)
  have he : 2 * (10 * (ε / 20)) = ε := by ring
  rw [he] at hrestrict
  exact ⟨hrestrict⟩

end GC.MetricGeometry
