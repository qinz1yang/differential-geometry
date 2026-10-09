import DifferentialGeometry.Geometry.Comparison.LineCoordinate
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem exists_calibrated_ray [ProperSpace X]
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X} (hγ : Isometry γ)
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (x : X) : ∃ r : ℝ≥0 → X, Isometry r ∧ r 0 = x ∧
      ∀ t, lineCoordinate γ (r t) = lineCoordinate γ x + t := by
  classical
  let b := lineCoordinate γ
  let e (n : ℕ) := γ (b x + ((n : ℝ) + 1))
  let L (n : ℕ) := dist x (e n)
  let h := dist x (γ (b x))
  have hh : 0 ≤ h := dist_nonneg
  have hN (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hbelow (n : ℕ) : (n : ℝ) + 1 ≤ L n := by
    have hl := (lipschitzWith_lineCoordinate hs hγ).dist_le_mul (e n) x
    dsimp [e, b] at hl
    rw [lineCoordinate_apply_isometry hγ] at hl
    simp only [one_mul, Real.dist_eq] at hl
    rw [show lineCoordinate γ x + ((n : ℝ) + 1) - lineCoordinate γ x = (n : ℝ) + 1 by ring,
      abs_of_pos (hN n), dist_comm] at hl
    exact hl
  have habove (n : ℕ) : L n ≤ (n : ℝ) + 1 + h := by
    have ht := dist_triangle x (γ (b x)) (e n)
    dsimp [e] at ht
    rw [hγ.dist_eq, Real.dist_eq] at ht
    rw [show b x - (b x + ((n : ℝ) + 1)) = -((n : ℝ) + 1) by ring,
      abs_neg, abs_of_pos (hN n)] at ht
    dsimp [L, e, h]
    linarith
  let q (n : ℕ) := L n / ((n : ℝ) + 1)
  have hqnonneg (n : ℕ) : 0 ≤ q n := div_nonneg dist_nonneg (hN n).le
  have hqbound (n : ℕ) : q n ≤ 1 + h := by
    apply (div_le_iff₀ (hN n)).2
    have hn : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hm := mul_le_mul_of_nonneg_left hn hh
    nlinarith [habove n]
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hq : Tendsto q atTop (𝓝 1) := by
    have hlim : Tendsto (fun n : ℕ => h / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnat
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (1 : ℝ)))
      (show Tendsto (fun n : ℕ => 1 + h / ((n : ℝ) + 1)) atTop (𝓝 1) by
        simpa using tendsto_const_nhds.add hlim)
    · intro n
      exact (le_div_iff₀ (hN n)).2 (by simpa using hbelow n)
    · intro n
      apply (div_le_iff₀ (hN n)).2
      have he : (1 + h / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = (n : ℝ) + 1 + h := by
        field_simp
      rw [he]
      exact habove n
  choose σ hcont hzero hone hdist using fun n => hsegments x (e n)
  let τ (n : ℕ) (t : ℝ≥0) : Icc (0 : ℝ) 1 :=
    ⟨min ((t : ℝ) / ((n : ℝ) + 1)) 1,
      le_min (div_nonneg t.property (hN n).le) (by norm_num), min_le_right _ _⟩
  let f (n : ℕ) (t : ℝ≥0) := σ n (τ n t)
  have hrad (n : ℕ) (t : ℝ≥0) : dist (f n t) x = L n * (τ n t : ℝ) := by
    rw [← hzero n, hdist n]
    change L n * |(τ n t : ℝ) - 0| = _
    rw [sub_zero, abs_of_nonneg (τ n t).property.1]
  have hball (n : ℕ) (t : ℝ≥0) : f n t ∈ closedBall x ((1 + h) * t) := by
    change dist (f n t) x ≤ _
    rw [hrad]
    calc
      L n * (τ n t : ℝ) ≤ L n * ((t : ℝ) / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) dist_nonneg
      _ = q n * t := by dsimp [q]; ring
      _ ≤ (1 + h) * t := mul_le_mul_of_nonneg_right (hqbound n) t.property
  have hτ (t : ℝ≥0) : ∀ᶠ n : ℕ in atTop, (τ n t : ℝ) = (t : ℝ) / ((n : ℝ) + 1) := by
    filter_upwards [hnat.eventually (eventually_ge_atTop (t : ℝ))] with n hn
    exact min_eq_left ((div_le_one (hN n)).2 hn)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hcompact (t : ℝ≥0) : ∃ y ∈ closedBall x ((1 + h) * t),
      Tendsto (fun n => f n t) U (𝓝 y) := by
    apply (isCompact_closedBall x ((1 + h) * t)).ultrafilter_le_nhds
      (Ultrafilter.map (fun n => f n t) U)
    apply le_principal_iff.mpr
    change ∀ᶠ n in (U : Filter ℕ), f n t ∈ closedBall x ((1 + h) * t)
    exact Eventually.of_forall (fun n => hball n t)
  choose r hrball hr using hcompact
  have hpair (s t : ℝ≥0) :
      ∀ᶠ n in atTop, dist (f n s) (f n t) = q n * dist s t := by
    filter_upwards [hτ s, hτ t] with n hns hnt
    rw [hdist n]
    change L n * |(τ n s : ℝ) - (τ n t : ℝ)| = _
    rw [hns, hnt, ← sub_div, abs_div, abs_of_pos (hN n)]
    dsimp [q]
    change L n * (|(s : ℝ) - t| / ((n : ℝ) + 1)) =
      L n / ((n : ℝ) + 1) * |(s : ℝ) - t|
    ring
  have hiso : Isometry r := by
    apply Isometry.of_dist_eq
    intro s t
    have hlim : Tendsto (fun n => dist (f n s) (f n t)) atTop (𝓝 (dist s t)) := by
      apply Tendsto.congr' (Filter.EventuallyEq.symm (hpair s t))
      simpa using hq.mul_const (dist s t)
    exact tendsto_nhds_unique ((hr s).dist (hr t)) (hlim.mono_left hU)
  refine ⟨r, hiso, ?_, ?_⟩
  · have hz := hrball 0
    simpa using hz
  · intro t
    have hbcont := (lipschitzWith_lineCoordinate hs hγ).continuous
    have hlim := (hbcont.tendsto (r t)).comp (hr t)
    have hevent : ∀ᶠ n in atTop, b (f n t) = b x + t := by
      filter_upwards [hτ t] with n hn
      have hleft : dist x (f n t) = (τ n t : ℝ) * dist x (e n) := by
        rw [dist_comm, hrad]
        exact mul_comm _ _
      have hright : dist (f n t) (e n) = (1 - (τ n t : ℝ)) * dist x (e n) := by
        rw [← hone n, hdist n]
        rw [hone n]
        change L n * |(τ n t : ℝ) - 1| = _
        rw [abs_of_nonpos (sub_nonpos.mpr (τ n t).property.2)]
        ring
      have hc := lineCoordinate_affine_of_dist hs hγ (τ n t).property hleft hright
      change b (f n t) = (1 - (τ n t : ℝ)) * b x + (τ n t : ℝ) * b (e n) at hc
      have he : b (e n) = b x + ((n : ℝ) + 1) := lineCoordinate_apply_isometry hγ _
      rw [he, hn] at hc
      rw [hc]
      field_simp
      ring
    exact tendsto_nhds_unique hlim ((tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hevent)).mono_left hU)

end DifferentialGeometry.Geometry.Comparison.Toponogov
