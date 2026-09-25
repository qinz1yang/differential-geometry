import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCompleteLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardBoundedDistance

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem StandardSolution.terminalRegularRegion_eq_bot (S : StandardSolution) :
    terminalRegularRegion S.val.metric 0 1 = ⊥ := by
  apply bot_unique
  intro p hp
  obtain ⟨U, hpU, a, ha, K, _hK, hbound⟩ := hp
  let time : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 4)
  have htime (n : ℕ) : time n ∈ Ico (0 : ℝ) 1 := by
    have hd : 0 < (n : ℝ) + 4 := by positivity
    have hdiv : 1 / ((n : ℝ) + 4) ≤ 1 := (div_le_one hd).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨by dsimp [time]; linarith, by dsimp [time]; exact sub_lt_self _ (div_pos zero_lt_one hd)⟩
  have hlate (n : ℕ) : 3 / 4 ≤ time n := by
    have hd : 0 < (n : ℝ) + 4 := by positivity
    have hdiv : 1 / ((n : ℝ) + 4) ≤ 1 / 4 := (div_le_iff₀ hd).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [time]
    linarith
  have hlim : Tendsto time atTop (𝓝 1) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop :=
      tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n : ℝ) ≤ (n : ℝ) + 4)
        tendsto_natCast_atTop_atTop
    have hz : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 4)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnat
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hz
  have hdom (n : ℕ) : time n ∈ S.val.domain := by
    apply (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos _).mpr
    rw [S.lifetime_eq_one]
    exact ⟨(htime n).1, ENNReal.ofReal_lt_one.mpr (htime n).2⟩
  have hbase : ∀ᶠ n in atTop, metricScalarAt (S.val.metric (time n)) p ≤ 9 * K := by
    filter_upwards [hlim.eventually (Ioi_mem_nhds ha.2)] with n hn
    have hrm := hbound p hpU (time n) ⟨hn.le, (htime n).2⟩
    have hsc := scalar_abs_le_rm (S.val.metric (time n)) p
    change |metricScalarAt (S.val.metric (time n)) p| ≤
      (Module.finrank ℝ E3 : ℝ) ^ 2 * _ at hsc
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at hsc
    exact (le_abs_self _).trans (hsc.trans (mul_le_mul_of_nonneg_left hrm (by norm_num)))
  have hballs : ∀ r : ℝ, 0 < r → ∃ A : ℝ, ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (S.val.metric (time n)) p r,
        metricScalarAt (S.val.metric (time n)) y ≤ A := by
    intro r hr
    obtain ⟨A, hb⟩ := exists_standard_scalar_bound_at_bounded_distance (9 * K) r hr.le
    refine ⟨A, hbase.mono fun n hn y hy => hb S.val (time n) (hdom n) (hlate n)
      (htime n).2 p y hn hy⟩
  obtain ⟨P, hcanonical, _hconn, _hpre, _hconnected, _hnested, A, hA⟩ :=
    exists_standard_complete_terminal_limit_of_bounded_scalar_on_balls
      (fun _ => S.val) time (fun _ => p) (by norm_num : (0 : ℝ) < 3 / 4)
      (fun n => ⟨hdom n, hlate n, (htime n).2⟩) hballs
  exact S.not_exists_complete_bounded_terminal_limit time p htime hlim ⟨P, hcanonical, A, hA⟩

theorem exists_standard_scalar_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : StandardSolution) (x : E3),
      ∀ t ∈ Ico (0 : ℝ) 1, c / (1 - t) ≤ metricScalarAt (S.val.metric t) x := by
  obtain ⟨c, hc, hb⟩ := exists_standard_scalar_lower_bound_at_nonregular_point
  refine ⟨c, hc, fun S x t ht => hb S.val S.one_le_lifetime x ?_ t ht⟩
  rw [S.terminalRegularRegion_eq_bot]
  simp

end DifferentialGeometry.PDE.RicciFlow
