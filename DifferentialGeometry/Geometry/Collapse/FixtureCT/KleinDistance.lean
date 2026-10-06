import DifferentialGeometry.Geometry.Collapse.FixtureCT.KleinCarrierExamples

/-!
# Two-sided distance formula of the edge carrier (lane O-FIXTURE-CT, kernel K-H)

The collapsed picture of `S¹_a × K_{b,L}` is the flat annulus `S¹_a × [0, b/2]` with coordinates
`δx = dist(x - x', aℤ)` and the strip coordinate `Y = dist(y, bℤ) ∈ [0, b/2]` (the two boundary
circles `Y = 0`, `Y = b/2` are the reflection lines). The carrier distance differs from the
collapsed one by at most the fibre:
`√(δx² + (Y u - Y v)²) ≤ d(π u, π v) ≤ √(δx² + (Y u - Y v)² + (L/2)²)`.

* `perDist_OFT c u = |u - c · round(u / c)|` (distance from `u` to `cℤ`): minimality, `≤ c/2`,
  1-Lipschitz, invariance under `u ↦ ±u + n c`;
* `collapsed_le_norm_sub_smul_OFT` and `le_dist_kleinPi_collapsed_OFT` (lower bound, over every
  lift);
* `exists_smul_norm_le_collapsed_OFT` and `dist_kleinPi_le_collapsed_OFT` (upper bound: a lift
  matching the strip side, the `x`-period and the `t`-fibre up to `L/2`);
* consumers: `abs_dist_kleinPi_sub_collapsed_le_OFT` (carrier distance within `L/2` of the
  collapsed one), `abs_perDist_sub_le_dist_OFT` (the strip coordinate is 1-Lipschitz on the
  carrier) and the closed example `kleinUnit_strip_dist_OFT` at `kleinUnit_OFT`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] kleinMS_OFT

/-- The distance from `u` to the lattice `cℤ`. -/
def perDist_OFT (c u : ℝ) : ℝ := |u - c * round (u / c)|

theorem perDist_nonneg_OFT (c u : ℝ) : 0 ≤ perDist_OFT c u := abs_nonneg _

theorem perDist_le_OFT {c : ℝ} (hc : 0 < c) (u : ℝ) (n : ℤ) :
    perDist_OFT c u ≤ |u - (n : ℝ) * c| := by
  have h := round_le (u / c) n
  have e1 : u - c * (round (u / c) : ℝ) = c * (u / c - (round (u / c) : ℝ)) := by
    field_simp
  have e2 : u - (n : ℝ) * c = c * (u / c - (n : ℝ)) := by
    field_simp
  rw [perDist_OFT, e1, e2, abs_mul, abs_mul, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left h hc.le

theorem perDist_le_half_OFT {c : ℝ} (hc : 0 < c) (u : ℝ) : perDist_OFT c u ≤ c / 2 := by
  have h := abs_sub_round (u / c)
  have e1 : u - c * (round (u / c) : ℝ) = c * (u / c - (round (u / c) : ℝ)) := by
    field_simp
  rw [perDist_OFT, e1, abs_mul, abs_of_pos hc]
  nlinarith

theorem perDist_lipschitz_OFT {c : ℝ} (hc : 0 < c) (u v : ℝ) :
    |perDist_OFT c u - perDist_OFT c v| ≤ |u - v| := by
  have h1 : perDist_OFT c u ≤ |u - v| + perDist_OFT c v := by
    have := perDist_le_OFT hc u (round (v / c))
    have h' : |u - (round (v / c) : ℝ) * c| ≤ |u - v| + |v - c * (round (v / c) : ℝ)| := by
      have e : (round (v / c) : ℝ) * c = c * (round (v / c) : ℝ) := mul_comm _ _
      have := abs_sub_le u v ((round (v / c) : ℝ) * c)
      rw [e] at this
      rw [e]
      exact this
    unfold perDist_OFT at this ⊢
    linarith
  have h2 : perDist_OFT c v ≤ |u - v| + perDist_OFT c u := by
    have := perDist_le_OFT hc v (round (u / c))
    have h' : |v - (round (u / c) : ℝ) * c| ≤ |v - u| + |u - c * (round (u / c) : ℝ)| := by
      have e : (round (u / c) : ℝ) * c = c * (round (u / c) : ℝ) := mul_comm _ _
      have := abs_sub_le v u ((round (u / c) : ℝ) * c)
      rw [e] at this
      rw [e]
      exact this
    rw [abs_sub_comm v u] at h'
    unfold perDist_OFT at this ⊢
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Invariance under `u ↦ s u + n c`, `s = ±1`. -/
theorem perDist_shift_OFT {c : ℝ} (hc : 0 < c) (u : ℝ) (s : ℝ) (hs : s * s = 1)
    (hs' : s = 1 ∨ s = -1) (n : ℤ) : perDist_OFT c (s * u + (n : ℝ) * c) = perDist_OFT c u := by
  have hsabs : |s| = 1 := by rcases hs' with h | h <;> simp [h]
  apply le_antisymm
  · rcases hs' with h | h
    · have := perDist_le_OFT hc (s * u + (n : ℝ) * c) (round (u / c) + n)
      rw [h] at this ⊢
      push_cast at this
      unfold perDist_OFT
      calc |1 * u + (n : ℝ) * c - c * (round ((1 * u + (n : ℝ) * c) / c) : ℝ)|
          ≤ |1 * u + (n : ℝ) * c - ((round (u / c) : ℝ) + n) * c| := by
            have := perDist_le_OFT hc (1 * u + (n : ℝ) * c) (round (u / c) + n)
            push_cast at this
            exact this
        _ = |u - c * (round (u / c) : ℝ)| := by ring_nf
    · unfold perDist_OFT
      calc |s * u + (n : ℝ) * c - c * (round ((s * u + (n : ℝ) * c) / c) : ℝ)|
          ≤ |s * u + (n : ℝ) * c - ((-round (u / c) + n : ℤ) : ℝ) * c| :=
            perDist_le_OFT hc (s * u + (n : ℝ) * c) (-round (u / c) + n)
        _ = |u - c * (round (u / c) : ℝ)| := by
            rw [h]
            push_cast
            rw [show -1 * u + (n : ℝ) * c - (-(round (u / c) : ℝ) + n) * c =
              -(u - c * (round (u / c) : ℝ)) by ring, abs_neg]
  · set w := s * u + (n : ℝ) * c with hw
    have hu : u = s * w + ((-(s * n) : ℝ)) * c := by
      rw [hw]
      linear_combination (-u) * hs
    have hint : ∃ m : ℤ, (m : ℝ) = -(s * n) := by
      rcases hs' with h | h
      · exact ⟨-n, by rw [h]; push_cast; ring⟩
      · exact ⟨n, by rw [h]; ring⟩
    obtain ⟨m, hm⟩ := hint
    have key : ∀ (z : ℝ) (k : ℤ), perDist_OFT c (s * z + (k : ℝ) * c) ≤ perDist_OFT c z := by
      intro z k
      rcases hs' with h | h
      · calc perDist_OFT c (s * z + (k : ℝ) * c)
            ≤ |s * z + (k : ℝ) * c - ((round (z / c) + k : ℤ) : ℝ) * c| :=
              perDist_le_OFT hc _ _
          _ = perDist_OFT c z := by
              rw [h, perDist_OFT]
              push_cast
              ring_nf
      · calc perDist_OFT c (s * z + (k : ℝ) * c)
            ≤ |s * z + (k : ℝ) * c - ((-round (z / c) + k : ℤ) : ℝ) * c| :=
              perDist_le_OFT hc _ _
          _ = perDist_OFT c z := by
              rw [h, perDist_OFT]
              push_cast
              rw [show -1 * z + (k : ℝ) * c - (-(round (z / c) : ℝ) + k) * c =
                -(z - c * (round (z / c) : ℝ)) by ring, abs_neg]
    have := key w m
    rw [hm, ← hu] at this
    exact this

theorem kSign_one_OFT : kSign_OFT 1 = -1 := by simp [kSign_OFT]

theorem kSign_two_mul_OFT (j : ℤ) : kSign_OFT (2 * j) = 1 := by
  simp [kSign_OFT, Int.negOnePow_two_mul]

theorem kSign_cases_OFT (k : ℤ) : (kSign_OFT k : ℝ) = 1 ∨ (kSign_OFT k : ℝ) = -1 := by
  rcases Int.isUnit_iff.mp (Int.negOnePow k).isUnit with h | h
  · left
    rw [kSign_OFT, h]
    norm_num
  · right
    rw [kSign_OFT, h]
    norm_num

/-- The squared norm of a vector of `ℝ³`. -/
theorem norm_sq_three_OFT (w : E3) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]

/-- **Lower bound, every lift.** -/
theorem collapsed_le_norm_sub_smul_OFT (P : KleinPeriods_OFT) (u v : E3) (g : KleinGroup_OFT P) :
    Real.sqrt (perDist_OFT P.a (u 0 - v 0) ^ 2 +
      (perDist_OFT P.b (u 1) - perDist_OFT P.b (v 1)) ^ 2) ≤ ‖u - g • v‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (u - g • v)), norm_sq_three_OFT]
  apply Real.sqrt_le_sqrt
  simp only [PiLp.sub_apply, kleinSmul_zero_OFT, kleinSmul_one_OFT, kleinSmul_two_OFT]
  have h0 : perDist_OFT P.a (u 0 - v 0) ≤ |u 0 - (v 0 + (g.m : ℝ) * P.a)| := by
    have := perDist_le_OFT P.a_pos (u 0 - v 0) g.m
    rwa [show u 0 - v 0 - (g.m : ℝ) * P.a = u 0 - (v 0 + (g.m : ℝ) * P.a) by ring] at this
  have hY : perDist_OFT P.b ((kSign_OFT g.k : ℝ) * v 1 + (g.n : ℝ) * P.b) =
      perDist_OFT P.b (v 1) :=
    perDist_shift_OFT P.b_pos (v 1) _ (kSign_real_mul_self_OFT g.k) (kSign_cases_OFT g.k) g.n
  have h1 := perDist_lipschitz_OFT P.b_pos (u 1)
    ((kSign_OFT g.k : ℝ) * v 1 + (g.n : ℝ) * P.b)
  rw [hY] at h1
  have hp0 := perDist_nonneg_OFT P.a (u 0 - v 0)
  have s0 : perDist_OFT P.a (u 0 - v 0) ^ 2 ≤ (u 0 - (v 0 + (g.m : ℝ) * P.a)) ^ 2 := by
    rw [← sq_abs (u 0 - (v 0 + (g.m : ℝ) * P.a))]
    exact pow_le_pow_left₀ hp0 h0 2
  have s1 : (perDist_OFT P.b (u 1) - perDist_OFT P.b (v 1)) ^ 2 ≤
      (u 1 - ((kSign_OFT g.k : ℝ) * v 1 + (g.n : ℝ) * P.b)) ^ 2 := by
    rw [← sq_abs (perDist_OFT P.b (u 1) - perDist_OFT P.b (v 1)),
      ← sq_abs (u 1 - ((kSign_OFT g.k : ℝ) * v 1 + (g.n : ℝ) * P.b))]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [sq_nonneg (u 2 - (v 2 + (g.k : ℝ) * (P.L / 2)))]

/-- **Lower bound of the carrier distance by the collapsed distance.** -/
theorem le_dist_kleinPi_collapsed_OFT (P : KleinPeriods_OFT) (u v : E3) :
    Real.sqrt (perDist_OFT P.a (u 0 - v 0) ^ 2 +
      (perDist_OFT P.b (u 1) - perDist_OFT P.b (v 1)) ^ 2) ≤
      dist (kleinPi_OFT P u) (kleinPi_OFT P v) :=
  le_dist_kleinPi_OFT P u v _ (collapsed_le_norm_sub_smul_OFT P u v)

/-- Matching the strip side: a sign `(-1)^{k₀}` (`k₀ ∈ {0, 1}`) and a shift `n` with
`|u - ((-1)^{k₀} v + n c)| = |Y u - Y v|`. -/
theorem exists_strip_match_OFT (c u v : ℝ) :
    ∃ k₀ : ℤ, (k₀ = 0 ∨ k₀ = 1) ∧ ∃ n : ℤ,
      |u - ((kSign_OFT k₀ : ℝ) * v + (n : ℝ) * c)| = |perDist_OFT c u - perDist_OFT c v| := by
  set ru := round (u / c)
  set rv := round (v / c)
  have h0 : (kSign_OFT 0 : ℝ) = 1 := by rw [kSign_zero_OFT]; norm_num
  have h1 : (kSign_OFT 1 : ℝ) = -1 := by rw [kSign_one_OFT]; norm_num
  unfold perDist_OFT
  rcases le_or_gt 0 (u - c * ru) with hu | hu <;> rcases le_or_gt 0 (v - c * rv) with hv | hv
  · refine ⟨0, Or.inl rfl, ru - rv, ?_⟩
    rw [h0, abs_of_nonneg hu, abs_of_nonneg hv]
    push_cast
    ring_nf
  · refine ⟨1, Or.inr rfl, ru + rv, ?_⟩
    rw [h1, abs_of_nonneg hu, abs_of_neg hv]
    push_cast
    ring_nf
  · refine ⟨1, Or.inr rfl, ru + rv, ?_⟩
    rw [h1, abs_of_neg hu, abs_of_nonneg hv]
    push_cast
    rw [show u - (-1 * v + ((ru : ℝ) + rv) * c) = -(-(u - c * ru) - (v - c * rv)) by ring,
      abs_neg]
  · refine ⟨0, Or.inl rfl, ru - rv, ?_⟩
    rw [h0, abs_of_neg hu, abs_of_neg hv]
    push_cast
    rw [show u - (1 * v + ((ru : ℝ) - rv) * c) = -(-(u - c * ru) - -(v - c * rv)) by ring,
      abs_neg]

/-- **Upper bound, an explicit lift.** -/
theorem exists_smul_norm_le_collapsed_OFT (P : KleinPeriods_OFT) (u v : E3) :
    ∃ g : KleinGroup_OFT P, ‖u - g • v‖ ≤ Real.sqrt (perDist_OFT P.a (u 0 - v 0) ^ 2 +
      (perDist_OFT P.b (u 1) - perDist_OFT P.b (v 1)) ^ 2 + (P.L / 2) ^ 2) := by
  obtain ⟨k₀, hk₀, n, hn⟩ := exists_strip_match_OFT P.b (u 1) (v 1)
  have hL := P.L_pos
  set j : ℤ := round ((u 2 - v 2 - (k₀ : ℝ) * (P.L / 2)) / P.L)
  have hj : |u 2 - (v 2 + ((k₀ + 2 * j : ℤ) : ℝ) * (P.L / 2))| ≤ P.L / 2 := by
    have h := abs_sub_round ((u 2 - v 2 - (k₀ : ℝ) * (P.L / 2)) / P.L)
    have e : u 2 - (v 2 + ((k₀ + 2 * j : ℤ) : ℝ) * (P.L / 2)) =
        P.L * ((u 2 - v 2 - (k₀ : ℝ) * (P.L / 2)) / P.L - (j : ℝ)) := by
      push_cast
      field_simp
      ring
    rw [e, abs_mul, abs_of_pos hL]
    nlinarith
  set m : ℤ := round ((u 0 - v 0) / P.a)
  refine ⟨⟨m, n, k₀ + 2 * j⟩, ?_⟩
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_three_OFT]
  apply Real.sqrt_le_sqrt
  simp only [PiLp.sub_apply, kleinSmul_zero_OFT, kleinSmul_one_OFT, kleinSmul_two_OFT]
  have hks : kSign_OFT (k₀ + 2 * j) = kSign_OFT k₀ := by
    rw [kSign_add_OFT, kSign_two_mul_OFT, mul_one]
  have e0 : u 0 - (v 0 + (m : ℝ) * P.a) = (u 0 - v 0) - P.a * (round ((u 0 - v 0) / P.a) : ℝ) := by
    ring
  rw [e0, hks]
  have s0 : ((u 0 - v 0) - P.a * (round ((u 0 - v 0) / P.a) : ℝ)) ^ 2 =
      perDist_OFT P.a (u 0 - v 0) ^ 2 := by
    rw [perDist_OFT, sq_abs]
  have s1 : (u 1 - ((kSign_OFT k₀ : ℝ) * v 1 + (n : ℝ) * P.b)) ^ 2 =
      (perDist_OFT P.b (u 1) - perDist_OFT P.b (v 1)) ^ 2 := by
    rw [← sq_abs, hn, sq_abs]
  have s2 : (u 2 - (v 2 + ((k₀ + 2 * j : ℤ) : ℝ) * (P.L / 2))) ^ 2 ≤ (P.L / 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hj 2
  linarith

/-- **Upper bound of the carrier distance by the collapsed distance plus the fibre.** -/
theorem dist_kleinPi_le_collapsed_OFT (P : KleinPeriods_OFT) (u v : E3) :
    dist (kleinPi_OFT P u) (kleinPi_OFT P v) ≤ Real.sqrt (perDist_OFT P.a (u 0 - v 0) ^ 2 +
      (perDist_OFT P.b (u 1) - perDist_OFT P.b (v 1)) ^ 2 + (P.L / 2) ^ 2) := by
  obtain ⟨g, hg⟩ := exists_smul_norm_le_collapsed_OFT P u v
  exact (dist_kleinPi_le_smul_OFT P u v g).trans hg

/-- **Consumer.** The fibre error is at most `L/2`: the carrier distance is within `L/2` of the
collapsed distance. -/
theorem abs_dist_kleinPi_sub_collapsed_le_OFT (P : KleinPeriods_OFT) (u v : E3) :
    |dist (kleinPi_OFT P u) (kleinPi_OFT P v) - Real.sqrt (perDist_OFT P.a (u 0 - v 0) ^ 2 +
      (perDist_OFT P.b (u 1) - perDist_OFT P.b (v 1)) ^ 2)| ≤ P.L / 2 := by
  have hlo := le_dist_kleinPi_collapsed_OFT P u v
  have hup := dist_kleinPi_le_collapsed_OFT P u v
  have hL := half_pos P.L_pos
  set A := perDist_OFT P.a (u 0 - v 0) ^ 2 + (perDist_OFT P.b (u 1) - perDist_OFT P.b (v 1)) ^ 2
  have hA : 0 ≤ A := by positivity
  have hsq : Real.sqrt (A + (P.L / 2) ^ 2) ≤ Real.sqrt A + P.L / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hA, Real.sqrt_nonneg A]
  rw [abs_le]
  constructor <;> linarith

/-- **Consumer.** The strip coordinate `Y = dist(y, bℤ)` is 1-Lipschitz on the carrier. -/
theorem abs_perDist_sub_le_dist_OFT (P : KleinPeriods_OFT) (u v : E3) :
    |perDist_OFT P.b (u 1) - perDist_OFT P.b (v 1)| ≤ dist (kleinPi_OFT P u) (kleinPi_OFT P v) := by
  refine le_trans ?_ (le_dist_kleinPi_collapsed_OFT P u v)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (perDist_OFT P.a (u 0 - v 0))])

/-- **Closed example** on `S¹_1 × K_{1,1}`: the points `π(0, 0, 0)` (on a reflection line) and
`π(0, 1/4, 0)` (strip coordinate `1/4`) are at distance at least `1/4` and at most
`√(1/16 + 1/4)`. -/
theorem kleinUnit_strip_dist_OFT :
    1 / 4 ≤ dist (kleinPi_OFT kleinUnit_OFT (WithLp.toLp 2 ![0, 0, 0]))
        (kleinPi_OFT kleinUnit_OFT (WithLp.toLp 2 ![0, 1 / 4, 0])) ∧
      dist (kleinPi_OFT kleinUnit_OFT (WithLp.toLp 2 ![0, 0, 0]))
        (kleinPi_OFT kleinUnit_OFT (WithLp.toLp 2 ![0, 1 / 4, 0])) ≤
        Real.sqrt (1 / 16 + 1 / 4) := by
  have hr : round ((1 / 4 : ℝ) / 1) = 0 := by
    rw [round_eq_zero_iff]
    norm_num
  have hY0 : perDist_OFT 1 0 = 0 := by simp [perDist_OFT]
  have hY1 : perDist_OFT 1 (1 / 4) = 1 / 4 := by
    rw [perDist_OFT, hr]
    norm_num
  have hx : perDist_OFT 1 (0 - 0) = 0 := by simp [perDist_OFT]
  have hlo := le_dist_kleinPi_collapsed_OFT kleinUnit_OFT (WithLp.toLp 2 ![0, 0, 0])
    (WithLp.toLp 2 ![0, 1 / 4, 0])
  have hup := dist_kleinPi_le_collapsed_OFT kleinUnit_OFT (WithLp.toLp 2 ![0, 0, 0])
    (WithLp.toLp 2 ![0, 1 / 4, 0])
  simp only [kleinUnit_OFT, Matrix.cons_val_zero, Matrix.cons_val_one] at hlo hup
  rw [hx, hY0, hY1] at hlo hup
  refine ⟨?_, ?_⟩
  · refine le_trans (le_of_eq ?_) hlo
    rw [show (0 : ℝ) ^ 2 + (0 - 1 / 4) ^ 2 = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · refine hup.trans (le_of_eq ?_)
    norm_num

end DifferentialGeometry.Geometry.Collapse
