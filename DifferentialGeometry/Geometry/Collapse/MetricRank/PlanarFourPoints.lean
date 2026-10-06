import DifferentialGeometry.Geometry.Collapse.MetricRank.PlanarCone
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Four points in the plane (review 75, section C.3, S-X144 group G5)

`not_four_points_plane_ratio_SMR`: four points of `ℝ²` cannot have all six distances in `[a, b]`
with `b² < 2 a²` (max / min distance of four planar points is `≥ √2`). Proof: every angle of every
triangle among the four points is strictly acute (`cos ≥ (2 a² - b²) / (2 b²) > 0`); but the three
vectors from one point are linearly dependent in `ℝ²`
(`(v × w) u + (w × u) v + (u × v) w = 0`), and the sign pattern of the three cross products gives
either a convex-hull relation (`all_same_sign_SMR`) or a cone relation (`cone_of_relation_SMR`),
both impossible for acute configurations (`PlanarCone.lean`).
With `a = 5 - e`, `b = 5 + e`, `e ≤ 19/25`: `(5 + e) / (5 - e) ≤ 144/106 < √2`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

theorem pos_or_of_nonneg_ne_zero_SMR {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) : 0 < a ∨ 0 < b ∨ 0 < c := by
  by_contra hcon
  rw [not_or, not_or, not_lt, not_lt, not_lt] at hcon
  exact hne ⟨le_antisymm hcon.1 ha, le_antisymm hcon.2.1 hb, le_antisymm hcon.2.2 hc⟩

/-- Sign analysis of the planar relation `a (P 0 - P 3) + b (P 1 - P 3) + c (P 2 - P 3) = 0` among
four acute points. -/
theorem no_relation_acute_four_SMR {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : Fin 4 → V)
    (hP : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < inner ℝ (P j - P i) (P k - P i))
    {a b c : ℝ} (hrel : a • (P 0 - P 3) + b • (P 1 - P 3) + c • (P 2 - P 3) = 0)
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) : False := by
  have hneg : ∀ x y z : V, (-a) • x + (-b) • y + (-c) • z = -(a • x + b • y + c • z) :=
    fun x y z => by module
  have hrel' : (-a) • (P 0 - P 3) + (-b) • (P 1 - P 3) + (-c) • (P 2 - P 3) = 0 := by
    rw [hneg, hrel, neg_zero]
  have hne' : ¬ (-a = 0 ∧ -b = 0 ∧ -c = 0) := fun h =>
    hne ⟨neg_eq_zero.1 h.1, neg_eq_zero.1 h.2.1, neg_eq_zero.1 h.2.2⟩
  have hrel1 : b • (P 1 - P 3) + c • (P 2 - P 3) + a • (P 0 - P 3) = 0 := by
    rw [← hrel]; abel
  have hrel1' : (-b) • (P 1 - P 3) + (-c) • (P 2 - P 3) + (-a) • (P 0 - P 3) = 0 := by
    rw [← hrel']; abel
  have hrel2 : c • (P 2 - P 3) + a • (P 0 - P 3) + b • (P 1 - P 3) = 0 := by
    rw [← hrel]; abel
  have hrel2' : (-c) • (P 2 - P 3) + (-a) • (P 0 - P 3) + (-b) • (P 1 - P 3) = 0 := by
    rw [← hrel']; abel
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h02 : (0 : Fin 4) ≠ 2 := by decide
  have h03 : (0 : Fin 4) ≠ 3 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  rcases lt_trichotomy a 0 with ha | ha | ha <;> rcases lt_trichotomy b 0 with hb | hb | hb <;>
    rcases lt_trichotomy c 0 with hc | hc | hc <;>
    first
      | exact all_same_sign_SMR P hP h01 h02 h03 h12 h13 h23 (by linarith) (by linarith)
          (by linarith) (pos_or_of_nonneg_ne_zero_SMR (by linarith) (by linarith) (by linarith) hne)
          hrel
      | exact all_same_sign_SMR P hP h01 h02 h03 h12 h13 h23 (α := -a) (β := -b) (γ := -c)
          (by linarith) (by linarith) (by linarith)
          (pos_or_of_nonneg_ne_zero_SMR (by linarith) (by linarith) (by linarith) hne') hrel'
      | exact cone_of_relation_SMR P hP (i := 0) (j := 1) (k := 2) (l := 3) h01 h02 h03 h12 h13
          h23 (by linarith) (by linarith) (by linarith) hrel
      | exact cone_of_relation_SMR P hP (i := 0) (j := 1) (k := 2) (l := 3) h01 h02 h03 h12 h13
          h23 (α := -a) (β := -b) (γ := -c) (by linarith) (by linarith) (by linarith) hrel'
      | exact cone_of_relation_SMR P hP (i := 1) (j := 2) (k := 0) (l := 3) h12 h01.symm h13
          h02.symm h23 h03 (α := b) (β := c) (γ := a) (by linarith) (by linarith)
          (by linarith) hrel1
      | exact cone_of_relation_SMR P hP (i := 1) (j := 2) (k := 0) (l := 3) h12 h01.symm h13
          h02.symm h23 h03 (α := -b) (β := -c) (γ := -a) (by linarith) (by linarith)
          (by linarith) hrel1'
      | exact cone_of_relation_SMR P hP (i := 2) (j := 0) (k := 1) (l := 3) h02.symm h12.symm h23
          h01 h03 h13 (α := c) (β := a) (γ := b) (by linarith) (by linarith) (by linarith)
          hrel2
      | exact cone_of_relation_SMR P hP (i := 2) (j := 0) (k := 1) (l := 3) h02.symm h12.symm h23
          h01 h03 h13 (α := -c) (β := -a) (γ := -b) (by linarith) (by linarith)
          (by linarith) hrel2'

theorem inner_fin_two_SMR (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- Three vectors of `ℝ²` are linearly dependent through their cross products. -/
theorem rel_fin_two_SMR (u v w : EuclideanSpace ℝ (Fin 2)) :
    (v 0 * w 1 - v 1 * w 0) • u + (w 0 * u 1 - w 1 * u 0) • v + (u 0 * v 1 - u 1 * v 0) • w =
      0 := by
  ext k
  fin_cases k <;> simp <;> ring

/-- Two parallel vectors `u`, `w` of `ℝ²` (`w × u = 0`) satisfy `⟪u, w⟫ u = ‖u‖² w`. -/
theorem rel_deg_SMR (u w v : EuclideanSpace ℝ (Fin 2)) (hb : w 0 * u 1 - w 1 * u 0 = 0) :
    (u 0 * w 0 + u 1 * w 1) • u + (0 : ℝ) • v + (-(u 0 ^ 2 + u 1 ^ 2)) • w = 0 := by
  ext k
  fin_cases k
  · simp
    linear_combination (-(u 1)) * hb
  · simp
    linear_combination (u 0) * hb

/-- **Four points of the plane with all angles of all triangles strictly acute do not exist.** -/
theorem not_acute_four_points_plane_SMR (P : Fin 4 → EuclideanSpace ℝ (Fin 2))
    (hP : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k → 0 < inner ℝ (P j - P i) (P k - P i)) :
    False := by
  by_cases hdeg : (P 1 - P 3) 0 * (P 2 - P 3) 1 - (P 1 - P 3) 1 * (P 2 - P 3) 0 = 0 ∧
      (P 2 - P 3) 0 * (P 0 - P 3) 1 - (P 2 - P 3) 1 * (P 0 - P 3) 0 = 0 ∧
      (P 0 - P 3) 0 * (P 1 - P 3) 1 - (P 0 - P 3) 1 * (P 1 - P 3) 0 = 0
  · have huw : 0 < (P 0 - P 3) 0 * (P 2 - P 3) 0 + (P 0 - P 3) 1 * (P 2 - P 3) 1 := by
      have := hP 3 0 2 (by decide) (by decide) (by decide)
      rwa [inner_fin_two_SMR] at this
    have hu : 0 < (P 0 - P 3) 0 ^ 2 + (P 0 - P 3) 1 ^ 2 := by
      by_contra hcon
      rw [not_lt] at hcon
      have h0 : (P 0 - P 3) 0 ^ 2 = 0 := by
        nlinarith [sq_nonneg ((P 0 - P 3) 0), sq_nonneg ((P 0 - P 3) 1)]
      have h1 : (P 0 - P 3) 1 ^ 2 = 0 := by
        nlinarith [sq_nonneg ((P 0 - P 3) 0), sq_nonneg ((P 0 - P 3) 1)]
      have e0 := pow_eq_zero_iff (two_ne_zero) |>.mp h0
      have e1 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
      rw [e0, e1] at huw
      simp at huw
    exact cone_of_relation_SMR P hP (i := 0) (j := 1) (k := 2) (l := 3) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) huw.le le_rfl (by linarith)
      (rel_deg_SMR (P 0 - P 3) (P 2 - P 3) (P 1 - P 3) hdeg.2.1)
  · exact no_relation_acute_four_SMR P hP
      (rel_fin_two_SMR (P 0 - P 3) (P 1 - P 3) (P 2 - P 3)) hdeg

/-- In an inner product space, the inner product at the apex of a triangle is controlled by the
three side lengths. -/
theorem inner_pos_of_dist_bounds_SMR {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a b : ℝ} (hab : b ^ 2 < 2 * a ^ 2) {x y z : V} (hxy : a ≤ ‖y - x‖ ∧ ‖y - x‖ ≤ b)
    (hxz : a ≤ ‖z - x‖ ∧ ‖z - x‖ ≤ b) (hyz : a ≤ ‖y - z‖ ∧ ‖y - z‖ ≤ b)
    (ha : 0 < a) : 0 < inner ℝ (y - x) (z - x) := by
  have h := norm_sub_sq_real (y - x) (z - x)
  rw [sub_sub_sub_cancel_right] at h
  have h1 : a ^ 2 ≤ ‖y - x‖ ^ 2 := pow_le_pow_left₀ ha.le hxy.1 2
  have h2 : a ^ 2 ≤ ‖z - x‖ ^ 2 := pow_le_pow_left₀ ha.le hxz.1 2
  have h3 : ‖y - z‖ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyz.2 2
  nlinarith

/-- **C.3, the planar four-point lemma**: four points of `ℝ²` do not have all six distances in
`[a, b]` when `b² < 2 a²` (max / min distance of four planar points is `≥ √2`). -/
theorem not_four_points_plane_ratio_SMR {a b : ℝ} (ha : 0 < a) (hab : b ^ 2 < 2 * a ^ 2)
    (z : Fin 4 → EuclideanSpace ℝ (Fin 2))
    (hz : ∀ i j, i ≠ j → a ≤ dist (z i) (z j) ∧ dist (z i) (z j) ≤ b) : False := by
  refine not_acute_four_points_plane_SMR z (fun i j k hij hik hjk => ?_)
  have h1 := hz j i hij.symm
  have h2 := hz k i hik.symm
  have h3 := hz j k hjk
  rw [dist_eq_norm] at h1 h2 h3
  exact inner_pos_of_dist_bounds_SMR hab h1 h2 h3 ha

/-- The numerical form of C.3: `5 - e ≤ d ≤ 5 + e` with `e ≤ 19/25` for all six distances of
four planar points is impossible, because `(5 + e)/(5 - e) ≤ 144/106 < √2`. -/
theorem not_four_points_plane_five_SMR {e : ℝ} (he : e ≤ 19 / 25)
    (z : Fin 4 → EuclideanSpace ℝ (Fin 2))
    (hz : ∀ i j, i ≠ j → 5 - e ≤ dist (z i) (z j) ∧ dist (z i) (z j) ≤ 5 + e) : False := by
  have h01 := hz 0 1 (by decide)
  have he0 : 0 ≤ e := by linarith [h01.1, h01.2]
  refine not_four_points_plane_ratio_SMR (a := 5 - e) (b := 5 + e) (by linarith) ?_ z hz
  nlinarith

/-- The review's last inequality: `144 / 106 < √2` (equivalently `144² < 2 · 106²`). -/
theorem ratio_lt_sqrt_two_SMR : (144 : ℝ) / 106 < Real.sqrt 2 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- The ratio form: `(5 + e) / (5 - e) ≤ 144/106` for `0 ≤ e ≤ 19/25`. -/
theorem ratio_five_le_SMR {e : ℝ} (he : e ≤ 19 / 25) :
    (5 + e) / (5 - e) ≤ 144 / 106 := by
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- The distance between two points given by coordinates. -/
theorem dist_pair_SMR (x y c d : ℝ) :
    dist (!₂[x, y] : EuclideanSpace ℝ (Fin 2)) !₂[c, d] =
      Real.sqrt ((x - c) ^ 2 + (y - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

/-- **Consumer (explicit numbers, `ℝ²`).** The equilateral triangle `(0, 0)`, `(5, 0)`,
`(5/2, 5 √3 / 2)` of side `5` has no fourth point of the plane whose distances to the three
vertices all lie in `[106/25, 144/25] = [5 - 19/25, 5 + 19/25]`. -/
theorem plane_no_fourth_point_SMR (D : EuclideanSpace ℝ (Fin 2))
    (hA : 106 / 25 ≤ dist D !₂[0, 0] ∧ dist D !₂[0, 0] ≤ 144 / 25)
    (hB : 106 / 25 ≤ dist D !₂[5, 0] ∧ dist D !₂[5, 0] ≤ 144 / 25)
    (hC : 106 / 25 ≤ dist D !₂[5 / 2, 5 * Real.sqrt 3 / 2] ∧
      dist D !₂[5 / 2, 5 * Real.sqrt 3 / 2] ≤ 144 / 25) : False := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have dAB : dist (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) !₂[5, 0] = 5 := by
    rw [dist_pair_SMR, show ((0 : ℝ) - 5) ^ 2 + (0 - 0) ^ 2 = 5 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have dAC : dist (!₂[0, 0] : EuclideanSpace ℝ (Fin 2)) !₂[5 / 2, 5 * Real.sqrt 3 / 2] = 5 := by
    rw [dist_pair_SMR, show ((0 : ℝ) - 5 / 2) ^ 2 + (0 - 5 * Real.sqrt 3 / 2) ^ 2 = 5 ^ 2 by
      nlinarith]
    exact Real.sqrt_sq (by norm_num)
  have dBC : dist (!₂[5, 0] : EuclideanSpace ℝ (Fin 2)) !₂[5 / 2, 5 * Real.sqrt 3 / 2] = 5 := by
    rw [dist_pair_SMR, show ((5 : ℝ) - 5 / 2) ^ 2 + (0 - 5 * Real.sqrt 3 / 2) ^ 2 = 5 ^ 2 by
      nlinarith]
    exact Real.sqrt_sq (by norm_num)
  have mk : ∀ x y : EuclideanSpace ℝ (Fin 2), 106 / 25 ≤ dist x y ∧ dist x y ≤ 144 / 25 →
      5 - 19 / 25 ≤ dist x y ∧ dist x y ≤ 5 + 19 / 25 := fun x y h => by
    constructor <;> linarith [h.1, h.2]
  have mk5 : ∀ x y : EuclideanSpace ℝ (Fin 2), dist x y = 5 →
      5 - 19 / 25 ≤ dist x y ∧ dist x y ≤ 5 + 19 / 25 := fun x y h => by
    rw [h]; norm_num
  refine not_four_points_plane_five_SMR (e := 19 / 25) le_rfl
    ![!₂[0, 0], !₂[5, 0], !₂[5 / 2, 5 * Real.sqrt 3 / 2], D] (fun i j hij => ?_)
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact mk5 _ _ dAB
      | exact mk5 _ _ (by rw [dist_comm]; exact dAB)
      | exact mk5 _ _ dAC
      | exact mk5 _ _ (by rw [dist_comm]; exact dAC)
      | exact mk5 _ _ dBC
      | exact mk5 _ _ (by rw [dist_comm]; exact dBC)
      | exact mk _ _ hA
      | exact mk _ _ (by rw [dist_comm]; exact hA)
      | exact mk _ _ hB
      | exact mk _ _ (by rw [dist_comm]; exact hB)
      | exact mk _ _ hC
      | exact mk _ _ (by rw [dist_comm]; exact hC)

end GC.MetricGeometry
