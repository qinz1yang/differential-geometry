import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Topology.MetricSpace.FiniteNets
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

theorem exists_isometryEquiv_subsequence_of_pointed_approximations
    {R ε : ℕ → ℝ} (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (f : ∀ n, PointedBallApprox p q (R n) (ε n)) :
    ∃ (e : X ≃ᵢ Y) (φ : ℕ → ℕ), e p = q ∧ StrictMono φ ∧
      ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
        ∀ x : BallCarrier p (R (φ i)), dist x.val p ≤ S →
          dist ((f (φ i)).toFun x) (e x.val) < η := by
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
  have huniform (S η : ℝ) (hη : 0 < η) :
      ∀ᶠ n in (U : Filter ℕ), ∀ x : X, dist x p ≤ S → dist (g n x) (F x) < η := by
    obtain ⟨A, hA, hnet⟩ := exists_finset_net_of_isCompact (isCompact_closedBall p S)
      (by positivity : 0 < η / 5)
    have hcenters : ∀ᶠ n in (U : Filter ℕ), ∀ z ∈ A, dist (g n z) (F z) < η / 5 := by
      apply A.eventually_all.mpr
      intro z _
      exact (tendsto_iff_dist_tendsto_zero.mp (hconv z)).eventually
        (eventually_lt_nhds (by positivity : 0 < η / 5))
    filter_upwards [hU (hR.eventually (eventually_ge_atTop S)),
      hU (hε.eventually (eventually_lt_nhds (by positivity : 0 < η / 5))), hcenters]
      with n hnR hnε hn
    intro x hx
    obtain ⟨z, hz, hdist⟩ := hnet x hx
    have hxR : dist x p ≤ R n := hx.trans hnR
    have hzR : dist z p ≤ R n := (hA z hz).trans hnR
    have hd := (abs_lt.mp ((f n).distortion ⟨x, hxR⟩ ⟨z, hzR⟩)).2
    have ht := dist_triangle4 (g n x) (g n z) (F z) (F x)
    have hi := hFiso.dist_eq z x
    rw [dist_comm z x] at hi
    rw [hg n ⟨x, hxR⟩, hg n ⟨z, hzR⟩] at ht
    rw [hg n ⟨x, hxR⟩]
    have hcenter := hn z hz
    rw [hg n ⟨z, hzR⟩] at hcenter
    linarith
  let P (k n : ℕ) : Prop := ∀ x : X, dist x p ≤ (k : ℝ) →
    dist (g n x) (F x) < 1 / ((k : ℝ) + 1)
  have hP (k : ℕ) : ∀ᶠ n in (U : Filter ℕ), P k n :=
    huniform k (1 / ((k : ℝ) + 1)) (by positivity)
  have hpick (k N : ℕ) : ∃ n : ℕ, N < n ∧ P k n := by
    have hN : ∀ᶠ n in (U : Filter ℕ), N < n := hU (eventually_gt_atTop N)
    exact (hN.and (hP k)).exists
  choose next hnext using hpick
  let φ : ℕ → ℕ := fun n => Nat.rec (next 0 0) (fun k prev => next (k + 1) prev) n
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (hnext (n + 1) (φ n)).1
  have hφP (k : ℕ) : P k (φ k) := by
    cases k with
    | zero => exact (hnext 0 0).2
    | succ k => exact (hnext (k + 1) (φ k)).2
  refine ⟨e, φ, hpq, hφ, ?_⟩
  intro S η hη
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop S),
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds hη)] with i hiS hiη
  intro x hx
  have hh := hφP i x.val (hx.trans hiS)
  rw [hg (φ i) x] at hh
  exact hh.trans hiη

end GC.MetricGeometry
