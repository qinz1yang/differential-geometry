import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter Metric Topology

namespace Metric

theorem exists_relative_almost_minimum_of_complete_closedBall
    {X : Type*} [MetricSpace X] {r : X → ℝ} {o : X} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hpos : ∀ x, 0 < r x)
    (hcomplete : IsComplete (closedBall o (r o / ε ^ 2)))
    (hlower : ∀ x ∈ closedBall o (r o / ε ^ 2),
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ y in 𝓝 x, c ≤ r y) :
    ∃ p ∈ closedBall o (r o / ε ^ 2), r p ≤ r o ∧
      ∀ q : X, dist p q ≤ r p / ε → (1 - ε) * r p < r q := by
  classical
  by_contra hnot
  push Not at hnot
  let S : Set X := {x | ε ^ 2 * dist x o + r x ≤ r o}
  have ho : o ∈ S := by simp [S]
  have hsub (x : S) : (x : X) ∈ closedBall o (r o / ε ^ 2) := by
    have hx := x.property
    change ε ^ 2 * dist (x : X) o + r x ≤ r o at hx
    change dist (x : X) o ≤ r o / ε ^ 2
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith [hpos x]
  have hrad (x : S) : r x ≤ r o := by
    have hx := x.property
    change ε ^ 2 * dist (x : X) o + r x ≤ r o at hx
    nlinarith [mul_nonneg (sq_nonneg ε) (dist_nonneg (x := (x : X)) (y := o))]
  have hmove (x : S) : ∃ y : S, r y ≤ (1 - ε) * r x ∧
      dist (x : X) (y : X) ≤ r x / ε := by
    obtain ⟨y, hxy, hy⟩ := hnot x (hsub x) (hrad x)
    have hbudget : ε ^ 2 * dist (x : X) y ≤ r x - r y := by
      have hd := (le_div_iff₀ hε).mp hxy
      have hm := mul_le_mul_of_nonneg_left hd hε.le
      nlinarith
    have hyS : y ∈ S := by
      have hx := x.property
      change ε ^ 2 * dist (x : X) o + r x ≤ r o at hx
      change ε ^ 2 * dist y o + r y ≤ r o
      have ht := mul_le_mul_of_nonneg_left (dist_triangle y (x : X) o) (sq_nonneg ε)
      rw [dist_comm y (x : X)] at ht
      nlinarith
    exact ⟨⟨y, hyS⟩, hy, hxy⟩
  choose g hg hdist using hmove
  let u : ℕ → S := fun n => Nat.rec ⟨o, ho⟩ (fun _ x => g x) n
  have hu0 : u 0 = ⟨o, ho⟩ := rfl
  have husucc (n : ℕ) : u (n + 1) = g (u n) := rfl
  have hdec (n : ℕ) : r (u n).val ≤ r o * (1 - ε) ^ n := by
    induction n with
    | zero => simp [hu0]
    | succ n ih =>
      rw [husucc]
      calc
        r (g (u n)).val ≤ (1 - ε) * r (u n).val := hg (u n)
        _ ≤ (1 - ε) * (r o * (1 - ε) ^ n) :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hε1.le)
        _ = r o * (1 - ε) ^ (n + 1) := by rw [pow_succ]; ring
  have hstep (n : ℕ) : dist (u n).val (u (n + 1)).val ≤
      (r o / ε) * (1 - ε) ^ n := by
    rw [husucc]
    calc
      dist (u n).val (g (u n)).val ≤ r (u n).val / ε := hdist (u n)
      _ ≤ (r o * (1 - ε) ^ n) / ε := div_le_div_of_nonneg_right (hdec n) hε.le
      _ = (r o / ε) * (1 - ε) ^ n := by ring
  have hC : CauchySeq (fun n => (u n).val) :=
    cauchySeq_of_le_geometric (1 - ε) (r o / ε) (by linarith) hstep
  obtain ⟨x, hx, hux⟩ := cauchySeq_tendsto_of_isComplete hcomplete (fun n => hsub (u n)) hC
  have hrzero : Tendsto (fun n => r (u n).val) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (hpos (u n).val).le) hdec
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hε1.le)
        (show 1 - ε < 1 by linarith)).const_mul (r o)
  obtain ⟨c, hc, hcx⟩ := hlower x hx
  have hcz : c ≤ 0 := ge_of_tendsto hrzero (hux.eventually hcx)
  exact (not_le_of_gt hc) hcz

end Metric
