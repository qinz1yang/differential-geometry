import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry

variable {X : Type*} [PseudoMetricSpace X]

theorem ball_subset_zero_core_of_support_meeting {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z)
    {L T R θ : ℝ} (hL : 0 < L) (hθ : θ < 1) (hΛ : L * Λ ≤ 1 / 4)
    (hT : 40 * L < T) (hTθ : 40 * L / (1 - θ) < T) (hR : T * ρ z ≤ R)
    (hlocal : dist z p ≤ 10 * R → T / 20 ≤ R / ρ p)
    (hmeet : (closedBall z (θ * R) ∩ ball p (L * ρ p)).Nonempty) :
    dist z p < 2 * R ∧ ball p (L * ρ p) ⊆ ball z R := by
  have hT0 : 0 < T := by linarith
  have hR0 : 0 < R := (mul_pos hT0 hz).trans_le hR
  obtain ⟨q, hqz, hqp⟩ := hmeet
  have hdist : dist z p < θ * R + L * ρ p := by
    have ht := dist_triangle z q p
    rw [dist_comm z q] at ht
    change dist q z ≤ θ * R at hqz
    change dist q p < L * ρ p at hqp
    linarith
  have hlip : ρ p ≤ ρ z + Λ * dist z p := by
    have hh := hρ.dist_le_mul p z
    rw [Real.dist_eq, dist_comm p z] at hh
    linarith [(abs_le.mp hh).2]
  have hsmall : L * ρ z < R / 40 := by
    nlinarith [mul_lt_mul_of_pos_right hT hz]
  have hpre : dist z p < 2 * R := by
    have h1 := mul_le_mul_of_nonneg_left hlip hL.le
    have h2 := mul_le_mul_of_nonneg_right hΛ (dist_nonneg (x := z) (y := p))
    have h3 := mul_lt_mul_of_pos_right hθ hR0
    nlinarith
  have hratio := hlocal (by linarith)
  have hratio' : T * ρ p ≤ 20 * R := by
    have hh := (le_div_iff₀ hp).mp hratio
    linarith
  have hTθ' : 40 * L < T * (1 - θ) := (div_lt_iff₀ (by linarith)).mp hTθ
  have hmargin : θ * R + 2 * L * ρ p < R := by
    have h1 := mul_lt_mul_of_pos_right hTθ' hp
    have h2 := mul_le_mul_of_nonneg_left hratio' (show 0 ≤ 1 - θ by linarith)
    nlinarith
  refine ⟨hpre, ?_⟩
  intro x hx
  have ht := dist_triangle x p z
  rw [dist_comm p z] at ht
  change dist x p < L * ρ p at hx
  change dist x z < R
  linarith

theorem subsingleton_zero_supports_meeting_ball {ι : Type*} {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hpos : ∀ x, 0 < ρ x)
    (z : ι → X) (R : ι → ℝ) (S : ι → Set X) {p : X} {L T θ : ℝ}
    (hL : 0 < L) (hθ : θ < 1) (hΛ : L * Λ ≤ 1 / 4)
    (hT : 40 * L < T) (hTθ : 40 * L / (1 - θ) < T)
    (hR : ∀ i, T * ρ (z i) ≤ R i)
    (hlocal : ∀ i q, dist (z i) q ≤ 10 * R i → T / 20 ≤ R i / ρ q)
    (hsupport : ∀ i, S i ⊆ closedBall (z i) (θ * R i))
    (hdisjoint : Pairwise fun i j => Disjoint (ball (z i) (R i)) (ball (z j) (R j))) :
    {i | (S i ∩ ball p (L * ρ p)).Nonempty}.Subsingleton := by
  have hsub (i : ι) (hi : (S i ∩ ball p (L * ρ p)).Nonempty) :
      ball p (L * ρ p) ⊆ ball (z i) (R i) := by
    apply (ball_subset_zero_core_of_support_meeting hρ (hpos p) (hpos (z i)) hL hθ hΛ hT hTθ
      (hR i) (hlocal i p) _).2
    obtain ⟨q, hq, hqp⟩ := hi
    exact ⟨q, hsupport i hq, hqp⟩
  intro i hi j hj
  by_contra hij
  have hp : p ∈ ball p (L * ρ p) := mem_ball_self (mul_pos hL (hpos p))
  exact Set.disjoint_left.mp (hdisjoint hij) (hsub i hi hp) (hsub j hj hp)

end GC.MetricGeometry
