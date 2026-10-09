import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

set_option autoImplicit false


open Set Filter Metric Topology

namespace Metric

theorem exists_relative_almost_minimum_with_budget
    {X : Type*} [MetricSpace X] {r : X → ℝ} {o : X} {a θ : ℝ}
    (ha : 0 < a) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hpos : ∀ x, 0 < r x)
    (hcomplete : IsComplete (closedBall o (a * r o / (1 - θ))))
    (hlower : ∀ x ∈ closedBall o (a * r o / (1 - θ)),
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ y in 𝓝 x, c ≤ r y) :
    ∃ p : X, (1 - θ) * dist p o + a * r p ≤ a * r o ∧ r p ≤ r o ∧
      ∀ q : X, dist p q ≤ a * r p → θ * r p < r q := by
  classical
  by_contra hnot
  push Not at hnot
  let S : Set X := {x | (1 - θ) * dist x o + a * r x ≤ a * r o}
  have ho : o ∈ S := by simp [S]
  have hsub (x : S) : (x : X) ∈ closedBall o (a * r o / (1 - θ)) := by
    have hx := x.property
    change (1 - θ) * dist (x : X) o + a * r x ≤ a * r o at hx
    change dist (x : X) o ≤ a * r o / (1 - θ)
    apply (le_div_iff₀ (sub_pos.mpr hθ1)).mpr
    nlinarith [mul_pos ha (hpos x)]
  have hrad (x : S) : r x ≤ r o := by
    have hx := x.property
    change (1 - θ) * dist (x : X) o + a * r x ≤ a * r o at hx
    have hd := mul_nonneg (sub_nonneg.mpr hθ1.le) (dist_nonneg (x := (x : X)) (y := o))
    nlinarith
  have hmove (x : S) : ∃ y : S, r y ≤ θ * r x ∧ dist (x : X) (y : X) ≤ a * r x := by
    obtain ⟨y, hxy, hy⟩ := hnot x x.property (hrad x)
    have hbudget : (1 - θ) * dist (x : X) y ≤ a * (r x - r y) := by
      have hm := mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr hθ1.le)
      have hy' := mul_le_mul_of_nonneg_left hy ha.le
      nlinarith
    have hyS : y ∈ S := by
      have hx := x.property
      change (1 - θ) * dist (x : X) o + a * r x ≤ a * r o at hx
      change (1 - θ) * dist y o + a * r y ≤ a * r o
      have ht := mul_le_mul_of_nonneg_left (dist_triangle y (x : X) o) (sub_nonneg.mpr hθ1.le)
      rw [dist_comm y (x : X)] at ht
      nlinarith
    exact ⟨⟨y, hyS⟩, hy, hxy⟩
  choose g hg hdist using hmove
  let u : ℕ → S := fun n => Nat.rec ⟨o, ho⟩ (fun _ x => g x) n
  have hu0 : u 0 = ⟨o, ho⟩ := rfl
  have husucc (n : ℕ) : u (n + 1) = g (u n) := rfl
  have hdec (n : ℕ) : r (u n).val ≤ r o * θ ^ n := by
    induction n with
    | zero => simp [hu0]
    | succ n ih =>
      rw [husucc]
      calc
        r (g (u n)).val ≤ θ * r (u n).val := hg (u n)
        _ ≤ θ * (r o * θ ^ n) := mul_le_mul_of_nonneg_left ih hθ
        _ = r o * θ ^ (n + 1) := by rw [pow_succ]; ring
  have hstep (n : ℕ) : dist (u n).val (u (n + 1)).val ≤ (a * r o) * θ ^ n := by
    rw [husucc]
    calc
      dist (u n).val (g (u n)).val ≤ a * r (u n).val := hdist (u n)
      _ ≤ a * (r o * θ ^ n) := mul_le_mul_of_nonneg_left (hdec n) ha.le
      _ = (a * r o) * θ ^ n := by ring
  have hC : CauchySeq (fun n => (u n).val) := cauchySeq_of_le_geometric θ (a * r o) hθ1 hstep
  obtain ⟨x, hx, hux⟩ := cauchySeq_tendsto_of_isComplete hcomplete (fun n => hsub (u n)) hC
  have hrzero : Tendsto (fun n => r (u n).val) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (hpos (u n).val).le) hdec
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).const_mul (r o)
  obtain ⟨c, hc, hcx⟩ := hlower x hx
  have hcz : c ≤ 0 := ge_of_tendsto hrzero (hux.eventually hcx)
  exact (not_le_of_gt hc) hcz

end Metric
