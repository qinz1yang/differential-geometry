import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace WithLp

private theorem vertical_sq_le_of_almost_opposite
    {v w : WithLp 2 (ℝ × ℝ)} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hv : ‖v‖ ≤ 1 + ε) (hw : ‖w‖ ≤ 1 + ε)
    (hd : 2 - ε ≤ dist v w) (hv0 : 0 ≤ v.snd) (hw0 : 0 ≤ w.snd) :
    v.snd ^ 2 ≤ 15 * ε := by
  have hpar := parallelogram_law_with_norm ℝ v w
  have hvs := pow_le_pow_left₀ (norm_nonneg v) hv 2
  have hws := pow_le_pow_left₀ (norm_nonneg w) hw 2
  have hds := pow_le_pow_left₀ (by linarith : 0 ≤ 2 - ε) hd 2
  rw [dist_eq_norm] at hds
  have hsum := prod_norm_sq_eq_of_L2 (v + w)
  simp only [add_fst, add_snd, Real.norm_eq_abs, sq_abs] at hsum
  nlinarith [sq_nonneg (v.fst + w.fst), sq_nonneg w.snd, mul_nonneg hv0 hw0]

theorem not_approximate_orthogonal_cross_in_half_plane
    (q : Fin 2 × Bool → WithLp 2 (ℝ × ℝ)) {ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000)
    (hheight : ∀ i, 0 ≤ (q i).snd)
    (hnorm : ∀ i, |‖q i‖ - 1| ≤ ε)
    (hopposite : ∀ i : Fin 2, |dist (q (i, false)) (q (i, true)) - 2| ≤ ε)
    (hcross : ∀ s t : Bool, |dist (q (0, s)) (q (1, t)) - Real.sqrt 2| ≤ ε) : False := by
  classical
  have hε1 : ε ≤ 1 := by linarith
  have hupper (i : Fin 2 × Bool) : ‖q i‖ ≤ 1 + ε := by linarith [(abs_le.mp (hnorm i)).2]
  have hvertical (i : Fin 2 × Bool) : (q i).snd ^ 2 ≤ 15 * ε := by
    rcases i with ⟨i, t⟩
    cases t with
    | false =>
        exact vertical_sq_le_of_almost_opposite (w := q (i, true)) hε hε1 (hupper _) (hupper _)
          (by linarith [(abs_le.mp (hopposite i)).1]) (hheight _) (hheight _)
    | true =>
        apply vertical_sq_le_of_almost_opposite (w := q (i, false)) hε hε1 (hupper _) (hupper _)
        · rw [dist_comm]; linarith [(abs_le.mp (hopposite i)).1]
        · exact hheight _
        · exact hheight _
  have hhorizontal (i : Fin 2 × Bool) : 1 - 17 * ε ≤ |(q i).fst| ∧ |(q i).fst| ≤ 1 + ε := by
    have heq := prod_norm_sq_eq_of_L2 (q i)
    simp only [Real.norm_eq_abs, sq_abs] at heq
    have hn := abs_le.mp (hnorm i)
    have hlo : (1 - ε) ^ 2 ≤ ‖q i‖ ^ 2 :=
      pow_le_pow_left₀ (by linarith : 0 ≤ 1 - ε) (by linarith) 2
    have hhi := pow_le_pow_left₀ (norm_nonneg (q i)) (hupper i) 2
    have habs : |(q i).fst| ^ 2 = (q i).fst ^ 2 := sq_abs _
    constructor
    · nlinarith [hvertical i, abs_nonneg (q i).fst]
    · nlinarith [sq_nonneg (q i).snd, abs_nonneg (q i).fst]
  have hsqrt : 1 + ε < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hop (i : Fin 2) : 1 < dist (q (i, false)) (q (i, true)) := by
    linarith [(abs_le.mp (hopposite i)).1]
  have hcr (s t : Bool) : 1 < dist (q (0, s)) (q (1, t)) := by
    linarith [(abs_le.mp (hcross s t)).1]
  have hpair (i j : Fin 2 × Bool) (hij : i ≠ j) : 1 < dist (q i) (q j) := by
    rcases i with ⟨i, s⟩
    rcases j with ⟨j, t⟩
    fin_cases i <;> fin_cases j <;> cases s <;> cases t
    all_goals
      first
      | exact (hij rfl).elim
      | exact hop 0
      | exact hop 1
      | exact hcr false false
      | exact hcr false true
      | exact hcr true false
      | exact hcr true true
      | exact (dist_comm (q (0, true)) (q (0, false))) ▸ hop 0
      | exact (dist_comm (q (1, true)) (q (1, false))) ▸ hop 1
      | exact (dist_comm (q (1, false)) (q (0, false))) ▸ hcr false false
      | exact (dist_comm (q (1, true)) (q (0, false))) ▸ hcr false true
      | exact (dist_comm (q (1, false)) (q (0, true))) ▸ hcr true false
      | exact (dist_comm (q (1, true)) (q (0, true))) ▸ hcr true true
  let sign : Fin 2 × Bool → Bool := fun i => decide (0 ≤ (q i).fst)
  have hinj : Function.Injective sign := by
    intro i j hij
    by_contra hne
    have hd := hpair i j hne
    have hi := hhorizontal i
    have hj := hhorizontal j
    have hsign : (0 ≤ (q i).fst) ↔ (0 ≤ (q j).fst) := by
      simpa only [sign, decide_eq_decide] using hij
    have hxdiff : |(q i).fst - (q j).fst| ≤ 18 * ε := by
      by_cases hi0 : 0 ≤ (q i).fst
      · have hj0 := hsign.mp hi0
        rw [abs_of_nonneg hi0] at hi
        rw [abs_of_nonneg hj0] at hj
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · have hj0 : (q j).fst < 0 := lt_of_not_ge (fun h => hi0 (hsign.mpr h))
        rw [abs_of_neg (lt_of_not_ge hi0)] at hi
        rw [abs_of_neg hj0] at hj
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hydiff : ((q i).snd - (q j).snd) ^ 2 ≤ 15 * ε := by
      rcases le_total (q i).snd (q j).snd with hij | hji
      · nlinarith [hvertical j, hheight i, hheight j,
          mul_nonneg (hheight i) (sub_nonneg.mpr hij)]
      · nlinarith [hvertical i, hheight i, hheight j,
          mul_nonneg (hheight j) (sub_nonneg.mpr hji)]
    have hx2 := pow_le_pow_left₀ (abs_nonneg _) hxdiff 2
    rw [sq_abs] at hx2
    have heq := prod_norm_sq_eq_of_L2 (q i - q j)
    simp only [sub_fst, sub_snd, Real.norm_eq_abs, sq_abs] at heq
    rw [dist_eq_norm] at hd
    nlinarith
  have hcard := Fintype.card_le_of_injective sign hinj
  norm_num at hcard

end WithLp
