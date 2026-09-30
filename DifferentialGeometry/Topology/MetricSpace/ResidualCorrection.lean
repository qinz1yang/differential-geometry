import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem exists_preimage_of_local_residual_correction
    {f : X → Y} {q : X} {y : Y} {r μ ρ : ℝ}
    (hμ : 0 < μ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcomplete : IsComplete (closedBall q r))
    (hf : ContinuousOn f (closedBall q r))
    (herror : dist (f q) y ≤ μ * r)
    (hstep : ∀ x ∈ closedBall q r, 0 < dist (f x) y → dist (f x) y ≤ dist (f q) y →
      ∃ z : X, dist (f z) y ≤ ρ * dist (f x) y ∧
        μ * dist x z ≤ dist (f x) y - dist (f z) y) :
    ∃ z ∈ closedBall q r, f z = y ∧ dist q z ≤ dist (f q) y / μ := by
  classical
  let e : X → ℝ := fun x => dist (f x) y
  let S : Set X := {x | μ * dist x q + e x ≤ e q}
  have hqS : q ∈ S := by simp [S]
  have hnonneg (x : X) : 0 ≤ e x := dist_nonneg
  have hsub (x : S) : (x : X) ∈ closedBall q r := by
    have hx := x.property
    change μ * dist (x : X) q + e x ≤ e q at hx
    change dist (x : X) q ≤ r
    dsimp [e] at hx
    nlinarith [dist_nonneg (x := f x) (y := y)]
  have herr (x : S) : e x ≤ e q := by
    have hx := x.property
    change μ * dist (x : X) q + e x ≤ e q at hx
    nlinarith [dist_nonneg (x := (x : X)) (y := q)]
  have hmove (x : S) : ∃ z : S, e z ≤ ρ * e x ∧
      μ * dist (x : X) (z : X) ≤ e x - e z := by
    by_cases he : e x = 0
    · exact ⟨x, by simp [he], by simp⟩
    obtain ⟨z, hz, hbudget⟩ := hstep x (hsub x)
      (lt_of_le_of_ne (hnonneg x) (Ne.symm he)) (herr x)
    have hzS : z ∈ S := by
      have hx := x.property
      change μ * dist (x : X) q + e x ≤ e q at hx
      change μ * dist z q + e z ≤ e q
      have htri := mul_le_mul_of_nonneg_left (dist_triangle z (x : X) q) hμ.le
      rw [dist_comm z (x : X)] at htri
      change μ * dist (x : X) z ≤ e x - e z at hbudget
      linarith
    exact ⟨⟨z, hzS⟩, hz, hbudget⟩
  choose g hgerr hgbudget using hmove
  let u : ℕ → S := fun n => Nat.rec ⟨q, hqS⟩ (fun _ x => g x) n
  have hu0 : u 0 = ⟨q, hqS⟩ := rfl
  have husucc (n : ℕ) : u (n + 1) = g (u n) := rfl
  have hedec (n : ℕ) : e (u n).val ≤ e q * ρ ^ n := by
    induction n with
    | zero => simp [hu0]
    | succ n ih =>
      rw [husucc]
      calc
        e (g (u n)).val ≤ ρ * e (u n).val := hgerr (u n)
        _ ≤ ρ * (e q * ρ ^ n) := mul_le_mul_of_nonneg_left ih hρ0
        _ = e q * ρ ^ (n + 1) := by rw [pow_succ]; ring
  have hdist (n : ℕ) : dist (u n).val (u (n + 1)).val ≤ (e q / μ) * ρ ^ n := by
    have hb := hgbudget (u n)
    rw [← husucc n] at hb
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hμ).mpr
    nlinarith [hedec n, hnonneg (u (n + 1)).val]
  have hC : CauchySeq (fun n => (u n).val) :=
    cauchySeq_of_le_geometric ρ (e q / μ) hρ1 hdist
  obtain ⟨z, hz, huz⟩ := cauchySeq_tendsto_of_isComplete hcomplete (fun n => hsub (u n)) hC
  have hfuz : Tendsto (fun n => f (u n).val) atTop (𝓝 (f z)) :=
    (hf z hz).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨huz, Eventually.of_forall (fun n => hsub (u n))⟩)
  have heto : Tendsto (fun n => e (u n).val) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => hnonneg (u n).val) hedec
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul (e q)
  have hfz : f z = y := dist_eq_zero.mp
    (tendsto_nhds_unique (hfuz.dist tendsto_const_nhds) heto)
  refine ⟨z, hz, hfz, ?_⟩
  have hdto : Tendsto (fun n => dist q (u n).val) atTop (𝓝 (dist q z)) :=
    tendsto_const_nhds.dist huz
  apply le_of_tendsto hdto
  apply Eventually.of_forall
  intro n
  apply (le_div_iff₀ hμ).mpr
  have hn := (u n).property
  change μ * dist (u n).val q + e (u n).val ≤ e q at hn
  rw [dist_comm q (u n).val]
  nlinarith [hnonneg (u n).val]

theorem ball_subset_image_ball_of_local_residual_correction
    {f : X → Y} {q : X} {r μ ρ : ℝ}
    (hμ : 0 < μ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcomplete : IsComplete (closedBall q r))
    (hf : ContinuousOn f (closedBall q r))
    (hstep : ∀ y ∈ ball (f q) (μ * r),
      ∀ x ∈ closedBall q r, 0 < dist (f x) y → dist (f x) y ≤ dist (f q) y →
        ∃ z : X, dist (f z) y ≤ ρ * dist (f x) y ∧
          μ * dist x z ≤ dist (f x) y - dist (f z) y) :
    ball (f q) (μ * r) ⊆ f '' ball q r := by
  intro y hy
  have hy' : dist (f q) y < μ * r := by simpa only [mem_ball, dist_comm] using hy
  obtain ⟨z, _, hfz, hdist⟩ := exists_preimage_of_local_residual_correction
    hμ hρ0 hρ1 hcomplete hf hy'.le (hstep y hy)
  refine ⟨z, ?_, hfz⟩
  rw [mem_ball, dist_comm]
  exact hdist.trans_lt ((div_lt_iff₀ hμ).mpr (by nlinarith))

theorem isOpenMap_of_local_residual_correction {f : X → Y} (hf : Continuous f)
    (hlocal : ∀ q : X, ∀ ε : ℝ, 0 < ε →
      ∃ r μ ρ : ℝ, 0 < r ∧ r ≤ ε ∧ 0 < μ ∧ 0 ≤ ρ ∧ ρ < 1 ∧
        IsComplete (closedBall q r) ∧
        ∀ y ∈ ball (f q) (μ * r),
          ∀ x ∈ closedBall q r, 0 < dist (f x) y → dist (f x) y ≤ dist (f q) y →
            ∃ z : X, dist (f z) y ≤ ρ * dist (f x) y ∧
              μ * dist x z ≤ dist (f x) y - dist (f z) y) : IsOpenMap f := by
  intro U hU
  rw [Metric.isOpen_iff]
  rintro y ⟨q, hq, rfl⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU q hq
  obtain ⟨r, μ, ρ, hr, hrε, hμ, hρ0, hρ1, hcomplete, hstep⟩ := hlocal q ε hε
  refine ⟨μ * r, mul_pos hμ hr, ?_⟩
  exact (ball_subset_image_ball_of_local_residual_correction hμ hρ0 hρ1 hcomplete
    hf.continuousOn hstep).trans (image_mono ((ball_subset_ball hrε).trans hεU))

end Metric
