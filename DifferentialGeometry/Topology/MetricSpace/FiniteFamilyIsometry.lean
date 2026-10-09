import DifferentialGeometry.Topology.MetricSpace.FiniteNets
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

variable {D Y ι : Type*} [MetricSpace D] [ProperSpace D] [MetricSpace Y] [ProperSpace Y]
variable [Finite ι] {p : D} {q : Y} {ε : ℕ → ℝ}

theorem exists_isometry_family_subsequence_of_local_distortion
    (g : ℕ → ι → D → Y) (hbase : ∀ n j, g n j p = q)
    (hε : Tendsto ε atTop (𝓝 0))
    (hdist : ∀ S : ℝ, ∀ᶠ n in atTop, ∀ j, ∀ s t : D,
      dist s p ≤ S → dist t p ≤ S → |dist (g n j s) (g n j t) - dist s t| ≤ ε n) :
    ∃ (F : ι → D → Y) (φ : ℕ → ℕ),
      (∀ j, Isometry (F j)) ∧ (∀ j, F j p = q) ∧ StrictMono φ ∧
      ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
        ∀ j x, dist x p ≤ S → dist (g (φ i) j x) (F j x) < η := by
  classical
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hcompact (j : ι) (x : D) :
      ∃ y ∈ closedBall q (dist x p + 1), Tendsto (fun n => g n j x) U (𝓝 y) := by
    apply (isCompact_closedBall q (dist x p + 1)).ultrafilter_le_nhds
      (Ultrafilter.map (fun n => g n j x) U)
    apply le_principal_iff.mpr
    change ∀ᶠ n in (U : Filter ℕ), g n j x ∈ closedBall q (dist x p + 1)
    apply hU
    filter_upwards [hdist (dist x p), hε.eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with n hn he
    have hh := hn j x p le_rfl (by simp)
    rw [hbase] at hh
    change dist (g n j x) q ≤ dist x p + 1
    linarith [(abs_le.mp hh).2]
  choose F hFball hconv using hcompact
  have hFiso (j : ι) : Isometry (F j) := by
    apply Isometry.of_dist_eq
    intro s t
    have hh : ∀ᶠ n in (U : Filter ℕ), |dist (g n j s) (g n j t) - dist s t| ≤ ε n := by
      filter_upwards [hU (hdist (max (dist s p) (dist t p)))] with n hn
      exact hn j s t (le_max_left _ _) (le_max_right _ _)
    have hzero : |dist (F j s) (F j t) - dist s t| ≤ 0 :=
      le_of_tendsto_of_tendsto (((hconv j s).dist (hconv j t)).sub tendsto_const_nhds).abs
        (hε.mono_left hU) hh
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hzero)
  have hpq (j : ι) : F j p = q := by
    have hq : Tendsto (fun n => g n j p) U (𝓝 q) := by
      simpa only [hbase] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => q) U (𝓝 q))
    exact tendsto_nhds_unique (hconv j p) hq
  have huniform (S η : ℝ) (hη : 0 < η) :
      ∀ᶠ n in (U : Filter ℕ), ∀ j x, dist x p ≤ S → dist (g n j x) (F j x) < η := by
    obtain ⟨A, hA, hnet⟩ := exists_finset_net_of_isCompact (isCompact_closedBall p S)
      (by positivity : 0 < η / 5)
    have hcenters : ∀ᶠ n in (U : Filter ℕ), ∀ j, ∀ z ∈ A, dist (g n j z) (F j z) < η / 5 := by
      apply Filter.eventually_all.mpr
      intro j
      apply A.eventually_all.mpr
      intro z _
      exact (tendsto_iff_dist_tendsto_zero.mp (hconv j z)).eventually
        (eventually_lt_nhds (by positivity : 0 < η / 5))
    filter_upwards [hU (hdist S), hU (hε.eventually
      (eventually_lt_nhds (by positivity : 0 < η / 5))), hcenters] with n hn he hc
    intro j x hx
    obtain ⟨z, hz, hzx⟩ := hnet x hx
    have hd := (abs_le.mp (hn j x z hx (hA z hz))).2
    have ht := dist_triangle4 (g n j x) (g n j z) (F j z) (F j x)
    have hi := (hFiso j).dist_eq z x
    rw [dist_comm z x] at hi
    linarith [hc j z hz]
  let P (k n : ℕ) : Prop := ∀ j x, dist x p ≤ (k : ℝ) →
    dist (g n j x) (F j x) < 1 / ((k : ℝ) + 1)
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
  refine ⟨F, φ, hFiso, hpq, hφ, ?_⟩
  intro S η hη
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop S),
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds hη)] with i hiS hiη
  intro j x hx
  exact (hφP i j x (hx.trans hiS)).trans hiη

end GC.MetricGeometry
