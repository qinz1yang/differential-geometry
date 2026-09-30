import DifferentialGeometry.Geometry.Metric.HalfPlanePacking
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open Set Metric

namespace GC.MetricGeometry

private def orthogonalCross (i : Fin 2 × Bool) : WithLp 2 (ℝ × ℝ) :=
  let t : ℝ := if i.2 then 1 else -1
  if i.1 = 0 then WithLp.toLp 2 (t, 0) else WithLp.toLp 2 (0, t)

private theorem orthogonalCross_norm (i : Fin 2 × Bool) : ‖orthogonalCross i‖ = 1 := by
  rcases i with ⟨i, b⟩
  fin_cases i <;> cases b <;> norm_num [orthogonalCross, WithLp.prod_norm_eq_of_L2]

private theorem orthogonalCross_opposite (i : Fin 2) :
    dist (orthogonalCross (i, false)) (orthogonalCross (i, true)) = 2 := by
  fin_cases i <;> norm_num [orthogonalCross, dist_eq_norm, WithLp.prod_norm_eq_of_L2]
  all_goals nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_nonneg (4 : ℝ)]

private theorem orthogonalCross_cross (s t : Bool) :
    dist (orthogonalCross (0, s)) (orthogonalCross (1, t)) = Real.sqrt 2 := by
  cases s <;> cases t <;> norm_num [orthogonalCross, dist_eq_norm, WithLp.prod_norm_eq_of_L2]

private theorem orthogonalCross_height (i : Fin 2 × Bool) : |(orthogonalCross i).snd| ≤ 1 := by
  rcases i with ⟨i, b⟩
  fin_cases i <;> cases b <;> norm_num [orthogonalCross]

variable {X : Type*} [PseudoMetricSpace X]

theorem strip_height_lt_of_local_half_plane_model_of_bounded_mark {p z : X} {R S r t δ ε C K : ℝ}
    (ht : 0 < t) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hbuffer : R + 2 * δ + t < S) (htop : R + K + δ + t < C)
    (hlocal : t + 3 * δ < r) (hsmall : 5 * δ + ε ≤ t / 1000)
    (Q W : X → WithLp 2 (ℝ × ℝ)) (hQp : ‖Q p‖ ≤ K) (hWz : W z = 0)
    (hQdist : ∀ x ∈ ball p S, ∀ y ∈ ball p S,
      |dist (Q x) (Q y) - dist x y| ≤ δ)
    (hcover : ∀ y : WithLp 2 (ℝ × ℝ), y.snd ∈ Icc 0 C → dist y (Q p) < S - δ →
      infDist y (Q '' ball p S) ≤ δ)
    (hWheight : ∀ x ∈ ball z r, 0 ≤ (W x).snd)
    (hWdist : ∀ x ∈ ball z r, ∀ y ∈ ball z r, |dist (W x) (W y) - dist x y| ≤ ε)
    (hz : z ∈ ball p R) : (Q z).snd < t := by
  by_contra! hhigh
  have hR : 0 < R := (dist_nonneg (x := z) (y := p)).trans_lt hz
  have hpD : p ∈ ball p S := mem_ball_self (by linarith)
  have hzD : z ∈ ball p S := by
    change dist z p < S
    exact (show dist z p < R from hz).trans (by linarith)
  have hnormz : ‖Q z‖ < R + K + δ := by
    have hh := (abs_le.mp (hQdist z hzD p hpD)).2
    have hn : ‖Q z‖ ≤ dist (Q z) (Q p) + ‖Q p‖ := by
      simpa only [dist_zero_right] using dist_triangle (Q z) (Q p) 0
    change dist z p < R at hz
    linarith
  let target (i : Fin 2 × Bool) := Q z + t • orthogonalCross i
  have htargetradial (i : Fin 2 × Bool) : dist (target i) (Q z) = t := by
    dsimp [target]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      orthogonalCross_norm, mul_one]
  have htargetheight (i : Fin 2 × Bool) : (target i).snd ∈ Icc 0 C := by
    have hi := abs_le.mp (orthogonalCross_height i)
    have hsnd := WithLp.norm_snd_le ℝ (Q z)
    rw [Real.norm_eq_abs] at hsnd
    change 0 ≤ (Q z).snd + t * (orthogonalCross i).snd ∧
      (Q z).snd + t * (orthogonalCross i).snd ≤ C
    have hlo := mul_le_mul_of_nonneg_left hi.1 ht.le
    have hhi := mul_le_mul_of_nonneg_left hi.2 ht.le
    constructor <;> linarith [le_abs_self (Q z).snd]
  have htargets (i : Fin 2 × Bool) : dist (target i) (Q p) < S - δ := by
    have hd := (abs_le.mp (hQdist z hzD p hpD)).2
    have hh := dist_triangle (target i) (Q z) (Q p)
    rw [htargetradial] at hh
    change dist z p < R at hz
    linarith
  have himage : (Q '' ball p S).Nonempty := ⟨Q p, p, hpD, rfl⟩
  have hlift (i : Fin 2 × Bool) : ∃ x ∈ ball p S, dist (Q x) (target i) < 2 * δ := by
    have hc : infDist (target i) (Q '' ball p S) < 2 * δ :=
      (hcover (target i) (htargetheight i) (htargets i)).trans_lt (by linarith)
    obtain ⟨y, hy, hdy⟩ := (infDist_lt_iff himage).mp hc
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, by simpa only [dist_comm] using hdy⟩
  choose lift hliftD hlifterror using hlift
  have hliftradial (i : Fin 2 × Bool) : |dist (lift i) z - t| ≤ 3 * δ := by
    have h1 := abs_le.mp (hQdist (lift i) (hliftD i) z hzD)
    have h2 := abs_le.mp (abs_dist_sub_le (Q (lift i)) (target i) (Q z))
    rw [htargetradial] at h2
    have h3 := hlifterror i
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hliftW (i : Fin 2 × Bool) : lift i ∈ ball z r := by
    change dist (lift i) z < r
    have hh := (abs_le.mp (hliftradial i)).2
    linarith
  have hzW : z ∈ ball z r := mem_ball_self (by linarith)
  have hWnorm (i : Fin 2 × Bool) : |‖W (lift i)‖ - t| ≤ 3 * δ + ε := by
    have h1 := abs_le.mp (hWdist (lift i) (hliftW i) z hzW)
    rw [hWz, dist_zero_right] at h1
    have h2 := abs_le.mp (hliftradial i)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htargetdist (i j : Fin 2 × Bool) : dist (target i) (target j) =
      t * dist (orthogonalCross i) (orthogonalCross j) := by
    dsimp [target]
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, ← dist_eq_norm]
  have hWpair (i j : Fin 2 × Bool) :
      |dist (W (lift i)) (W (lift j)) - t * dist (orthogonalCross i) (orthogonalCross j)| ≤ 5 * δ + ε := by
    have h1 := abs_le.mp (hWdist (lift i) (hliftW i) (lift j) (hliftW j))
    have h2 := abs_le.mp (hQdist (lift i) (hliftD i) (lift j) (hliftD j))
    have h3 := dist_dist_dist_le (Q (lift i)) (Q (lift j)) (target i) (target j)
    rw [Real.dist_eq, htargetdist] at h3
    have h4 := abs_le.mp h3
    have hi := hlifterror i
    have hj := hlifterror j
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  let e : ℝ := (5 * δ + ε) / t
  have he : 0 ≤ e := by positivity
  have hesmall : e ≤ 1 / 1000 := by
    apply (div_le_iff₀ ht).mpr
    linarith
  let A (i : Fin 2 × Bool) := t⁻¹ • W (lift i)
  apply WithLp.not_approximate_orthogonal_cross_in_half_plane A he hesmall
  · intro i
    change 0 ≤ t⁻¹ * (W (lift i)).snd
    exact mul_nonneg (inv_nonneg.mpr ht.le) (hWheight (lift i) (hliftW i))
  · intro i
    have heq : ‖A i‖ - 1 = (‖W (lift i)‖ - t) / t := by
      dsimp [A]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      field_simp
    rw [heq, abs_div, abs_of_pos ht]
    exact div_le_div_of_nonneg_right ((hWnorm i).trans (by linarith)) ht.le
  · intro i
    have heq : dist (A (i, false)) (A (i, true)) - 2 =
        (dist (W (lift (i, false))) (W (lift (i, true))) - 2 * t) / t := by
      dsimp [A]
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),
        ← dist_eq_norm]
      field_simp
    rw [heq, abs_div, abs_of_pos ht]
    have hh := hWpair (i, false) (i, true)
    rw [orthogonalCross_opposite] at hh
    exact div_le_div_of_nonneg_right (by simpa only [mul_comm t] using hh) ht.le
  · intro s r
    have heq : dist (A (0, s)) (A (1, r)) - Real.sqrt 2 =
        (dist (W (lift (0, s))) (W (lift (1, r))) - t * Real.sqrt 2) / t := by
      dsimp [A]
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),
        ← dist_eq_norm]
      field_simp
    rw [heq, abs_div, abs_of_pos ht]
    have hh := hWpair (0, s) (1, r)
    rw [orthogonalCross_cross] at hh
    exact div_le_div_of_nonneg_right hh ht.le

theorem strip_height_lt_of_local_half_plane_model {p z : X} {R S r t δ ε C : ℝ}
    (ht : 0 < t) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hbuffer : R + 2 * δ + t < S) (htop : R + δ + t < C)
    (hlocal : t + 3 * δ < r) (hsmall : 5 * δ + ε ≤ t / 1000)
    (Q W : X → WithLp 2 (ℝ × ℝ)) (hQp : Q p = 0) (hWz : W z = 0)
    (hQdist : ∀ x ∈ ball p S, ∀ y ∈ ball p S,
      |dist (Q x) (Q y) - dist x y| ≤ δ)
    (hcover : ∀ y : WithLp 2 (ℝ × ℝ), y.snd ∈ Icc 0 C → ‖y‖ < S - δ →
      infDist y (Q '' ball p S) ≤ δ)
    (hWheight : ∀ x ∈ ball z r, 0 ≤ (W x).snd)
    (hWdist : ∀ x ∈ ball z r, ∀ y ∈ ball z r, |dist (W x) (W y) - dist x y| ≤ ε)
    (hz : z ∈ ball p R) : (Q z).snd < t := by
  apply strip_height_lt_of_local_half_plane_model_of_bounded_mark (K := 0)
    ht hδ hε hbuffer
    (by simpa only [add_zero] using htop) hlocal hsmall Q W
    (by rw [hQp, norm_zero]) hWz hQdist ?_ hWheight hWdist hz
  intro y hy hd
  exact hcover y hy (by simpa only [hQp, dist_zero_right] using hd)

theorem padded_strip_height_lt_of_half_plane_model {p z : X} {Δ δ C : ℝ}
    (hΔ : 0 < Δ) (hδ : 0 < δ) (hδsmall : δ ≤ Δ / 1000000) (hC : 200 * Δ < C)
    (Q W : X → WithLp 2 (ℝ × ℝ)) (hQp : Q p = 0) (hWz : W z = 0)
    (hQdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ δ)
    (hcover : ∀ y : WithLp 2 (ℝ × ℝ), y.snd ∈ Icc 0 C → ‖y‖ < 200 * Δ - δ →
      infDist y (Q '' ball p (200 * Δ)) ≤ δ)
    (hWheight : ∀ x ∈ ball z Δ, 0 ≤ (W x).snd)
    (hWdist : ∀ x ∈ ball z Δ, ∀ y ∈ ball z Δ, |dist (W x) (W y) - dist x y| ≤ δ)
    (hz : z ∈ ball p (120 * Δ)) : (Q z).snd < Δ / 10 := by
  have h := strip_height_lt_of_local_half_plane_model (R := 120 * Δ) (S := 200 * Δ)
    (r := Δ) (t := Δ / 100) (δ := δ) (ε := δ) (C := C)
    (by positivity) hδ hδ.le (by linarith) (by linarith) (by linarith) (by linarith)
    Q W hQp hWz hQdist hcover hWheight hWdist hz
  exact h.trans (by linarith)

end GC.MetricGeometry
