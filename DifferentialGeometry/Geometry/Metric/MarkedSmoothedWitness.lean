import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Every marked smoothed point has an original full-marker witness (CGP05, kernel steps)

Blueprint 207B, CGP05 (`lem:fibration-marked-smoothed-witness`, B:4084–4128). For `w ∈ V_i⁰`
(marker `v_i(w) > .9 R_i`, vector `|u_i(w)| < 5.5 ℓ R_i`) choose a selected `y` with
`|w - y| < 20 b r(y)` and a CFS14 witness `z ∈ S̃_j` with `|w - z| < ε r(z)`:

* `dist_lt_of_selected_and_witness`: `|z - y| < 128 b max(r z, r y)` (the CFS07 input);
* `witness_dist_lt_of_scale_chain`: with `σ_z ≤ (5/3) σ_y` (CFS07), `σ_y ≤ 16 R_i` (CGP04),
  `Σ ≤ ε/640`, `ε ≤ 1/10`, the first proximity `|w - z| < R_i/2400`;
* `marker_vector_of_close_block`: the block of any preimage `q` of `z` is `(R ζ η, R ζ)`; being
  within `R_i/1000` of `w`'s block forces `ζ > .899` (so `q ∈ U_i`) and `|η| < 6.2 ℓ`;
* `witness_dist_lt_of_full_scale`: with `σ_z ≤ 25 R_i/12`, the improved bound (MW).
-/

set_option autoImplicit false

namespace GC.MetricGeometry

theorem dist_lt_of_selected_and_witness {X : Type*} [PseudoMetricSpace X] {w y z : X}
    {b ε ry rz : ℝ} (hb : 1 ≤ b) (hε : ε ≤ 1 / 10) (hry : 0 ≤ ry) (hrz : 0 ≤ rz)
    (hy : dist w y < 20 * b * ry) (hz : dist w z < ε * rz) :
    dist z y < 128 * b * max rz ry := by
  have htri := dist_triangle z w y
  rw [dist_comm z w] at htri
  have h1 : 20 * b * ry ≤ 20 * b * max rz ry :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hm : 0 ≤ max rz ry := le_trans hrz (le_max_left _ _)
  have h2 : ε * rz ≤ b * max rz ry := by
    have : ε * rz ≤ 1 * rz := mul_le_mul_of_nonneg_right (by linarith) hrz
    nlinarith [le_max_left rz ry]
  nlinarith

theorem witness_dist_lt_of_scale_chain {d ε S σz σy R : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 10)
    (hS : S ≤ ε / 640) (hσz : 0 ≤ σz) (hzy : σz ≤ 5 / 3 * σy)
    (hyR : σy ≤ 16 * R) (hd : d < ε * (S * σz)) : d < R / 2400 := by
  have hR : 0 ≤ R := by linarith
  have h1 : σz ≤ 80 / 3 * R := by linarith
  have h2 : S * σz ≤ (ε / 640) * (80 / 3 * R) :=
    mul_le_mul hS h1 hσz (by positivity)
  have h3 : ε * (S * σz) ≤ ε * ((ε / 640) * (80 / 3 * R)) :=
    mul_le_mul_of_nonneg_left h2 hε0.le
  have h4 : ε * ε ≤ 1 / 10 * (1 / 10) := mul_le_mul hε hε hε0.le (by norm_num)
  have h5 := mul_le_mul_of_nonneg_right h4 hR
  have h6 : ε * ((ε / 640) * (80 / 3 * R)) = ε * ε * R / 24 := by ring
  linarith

theorem marker_vector_of_close_block {R ℓ ζ η uw vw d : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ)
    (hu : |R * ζ * η - uw| ≤ d) (hv : |R * ζ - vw| ≤ d) (hd : d < R / 1000)
    (hvw : 9 / 10 * R < vw) (huw : |uw| < 11 / 2 * ℓ * R) :
    899 / 1000 < ζ ∧ |η| < 31 / 5 * ℓ := by
  have hRζ : 899 / 1000 * R < R * ζ := by
    have := (abs_le.mp hv).1
    linarith
  have hζ : 899 / 1000 < ζ := by nlinarith
  refine ⟨hζ, ?_⟩
  have hRζ0 : 0 < R * ζ := by nlinarith
  have hprod : |η| * (R * ζ) < 11 / 2 * ℓ * R + R / 1000 := by
    have h1 : |R * ζ * η| ≤ |uw| + d := by
      have := abs_sub_abs_le_abs_sub (R * ζ * η) uw
      linarith
    rw [abs_mul, abs_of_pos hRζ0] at h1
    linarith
  by_contra hcon
  have hge : 31 / 5 * ℓ ≤ |η| := le_of_not_gt hcon
  have h2 : 31 / 5 * ℓ * (899 / 1000 * R) ≤ |η| * (R * ζ) :=
    mul_le_mul hge hRζ.le (by positivity) (abs_nonneg η)
  nlinarith

theorem witness_dist_lt_of_full_scale {d ε S σz R : ℝ} (hε0 : 0 ≤ ε) (hS0 : 0 ≤ S)
    (hσz : σz ≤ 25 * R / 12) (hd : d < ε * (S * σz)) : d < 25 / 12 * ε * S * R := by
  have h := mul_le_mul_of_nonneg_left hσz (mul_nonneg hε0 hS0)
  nlinarith

end GC.MetricGeometry
