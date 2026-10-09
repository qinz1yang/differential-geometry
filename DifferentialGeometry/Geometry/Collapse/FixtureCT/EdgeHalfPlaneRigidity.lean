import DifferentialGeometry.Geometry.Collapse.FixtureC1.NoEdgeOfSplitting

/-!
# Pointed half-plane rigidity of edge points (lane O-FIXTURE-CT, kernel K-PR)

`isEdgePoint p Δ b s` gives (review 75 section C.5, as in `NoEdgeOfSplitting`) a map
`π : X → ℝ²` into the closed upper half plane with `π p = 0` and additive distortion `≤ b + s` on
`B(p, 6)`. Dually to C.5 (which excludes a rank-two splitting at an edge point), the SOURCE side is
used here: three points of `B(p, r)` with mutual distance `D` cannot exist when
`2 (r + b + s)² < (D - (b + s))²`, because two of their images have first coordinates of the same
sign, hence a non-negative inner product, hence distance at most `√2 (r + b + s)`.

This is the kernel that locates the actual strong / weak edge sets of an explicit fixture: a point
at height `h` above a reflection line of a flat collapsed region carries three such points at
distance `2h` (angles 90°, 210°, 330°), so it is not an edge point once `h > 5 (b + s)`.

* `exists_halfPlane_map_of_isEdgePoint_OFT`: the map `π` (factored out of
  `not_isEdgePoint_of_hasEuclideanSplitting_two_FXC1`);
* `normSq_sub_le_of_halfPlane_OFT`: two half-plane vectors with first coordinates of equal sign;
* `not_isEdgePoint_of_three_points_OFT`: the three-point obstruction;
* `not_isEdgePoint_sup_plane_OFT`: consumer — the origin of `(ℝ × ℝ, sup metric)` is not an edge
  point for `b, s ≤ 1/200` (non-vacuity of the hypotheses).
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

universe u v

/-- **The half-plane map of an edge point** (review 75 C.5): `π = (F.fst, G ∘ F.snd)` with
`π p = 0`, values in the closed upper half plane and distortion `≤ b + s` on `B(p, 6)`. -/
theorem exists_halfPlane_map_of_isEdgePoint_OFT {X : Type u} [MetricSpace X] {p : X}
    {Δ b s : ℝ} (hb : b ≤ 1 / 6) (hs : s ≤ 1 / 7) (he : isEdgePoint.{u, v} p Δ b s) :
    0 < b ∧ 0 < s ∧ ∃ π : X → EuclideanSpace ℝ (Fin 2), π p = 0 ∧ (∀ x, 0 ≤ π x 1) ∧
      ∀ x ∈ ball p 6, ∀ y ∈ ball p 6, |(dist x y - ‖π x - π y‖)| ≤ b + s := by
  obtain ⟨Y, mY, q, C, hC, -, ⟨F⟩, ⟨G⟩⟩ := he
  have hb0 := F.error_pos
  have hs0 := G.error_pos
  have hb6 : 6 ≤ b⁻¹ := (le_inv_comm₀ (by norm_num) hb0).mpr (by simpa using hb)
  have hs7 : 7 ≤ s⁻¹ := (le_inv_comm₀ (by norm_num) hs0).mpr (by simpa using hs)
  let π : X → EuclideanSpace ℝ (Fin 2) := fun x =>
    !₂[(F.toFun x).fst, ((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ)]
  refine ⟨hb0, hs0, π, ?_, fun x => (G.toFun (F.toFun x).snd).2.1, ?_⟩
  · have hFp : F.toFun p = WithLp.toLp 2 ((0 : ℝ), q) := F.basepoint
    have hGq : G.toFun q = ⟨0, le_rfl, hC⟩ := G.basepoint
    ext i
    fin_cases i <;> simp [π, hFp, hGq]
  intro x hx y hy
  have hxb : x ∈ ball p b⁻¹ := ball_subset_ball hb6 hx
  have hyb : y ∈ ball p b⁻¹ := ball_subset_ball hb6 hy
  have hFd := F.distortion x hxb y hyb
  have hsq := WithLp.prod_dist_sq_eq_add_sq (F.toFun x) (F.toFun y)
  have hy1 : (F.toFun x).snd ∈ ball q s⁻¹ := by
    have h1 := WithLp.dist_snd_le (F.toFun x) (WithLp.toLp 2 ((0 : ℝ), q))
    have h2 := F.radial_error x hxb
    have h3 : dist x p < 6 := hx
    rw [mem_ball]
    simp only [WithLp.toLp_snd] at h1
    rw [abs_le] at h2
    linarith [h2.2]
  have hy2 : (F.toFun y).snd ∈ ball q s⁻¹ := by
    have h1 := WithLp.dist_snd_le (F.toFun y) (WithLp.toLp 2 ((0 : ℝ), q))
    have h2 := F.radial_error y hyb
    have h3 : dist y p < 6 := hy
    rw [mem_ball]
    simp only [WithLp.toLp_snd] at h1
    rw [abs_le] at h2
    linarith [h2.2]
  have hGd := G.distortion _ hy1 _ hy2
  have hGe : dist (G.toFun (F.toFun x).snd) (G.toFun (F.toFun y).snd) =
      |((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ) -
        ((G.toFun (F.toFun y).snd : Icc (0 : ℝ) C) : ℝ)| := by
    rw [Subtype.dist_eq, Real.dist_eq]
  rw [hGe] at hGd
  have hnorm : ‖π x - π y‖ ^ 2 = ((F.toFun x).fst - (F.toFun y).fst) ^ 2 +
      (((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ) -
        ((G.toFun (F.toFun y).snd : Icc (0 : ℝ) C) : ℝ)) ^ 2 := by
    have : π x - π y = !₂[(F.toFun x).fst - (F.toFun y).fst,
        ((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ) -
          ((G.toFun (F.toFun y).snd : Icc (0 : ℝ) C) : ℝ)] := by
      ext i
      fin_cases i <;> simp [π]
    rw [this, norm_sq_mk_SMR]
  have hd1 : dist (F.toFun x).fst (F.toFun y).fst ^ 2 =
      ((F.toFun x).fst - (F.toFun y).fst) ^ 2 := by
    rw [Real.dist_eq, sq_abs]
  generalize hg1 : ((G.toFun (F.toFun x).snd : Icc (0 : ℝ) C) : ℝ) = g₁ at hnorm hGd
  generalize hg2 : ((G.toFun (F.toFun y).snd : Icc (0 : ℝ) C) : ℝ) = g₂ at hnorm hGd
  generalize hdd : dist (F.toFun x).snd (F.toFun y).snd = d at hsq hGd
  have hd0 : 0 ≤ d := hdd ▸ dist_nonneg
  have hP := abs_sub_le_of_sq_FXC1 (P := dist (F.toFun x) (F.toFun y))
    (Q := ‖π x - π y‖) (A := (F.toFun x).fst - (F.toFun y).fst) (d := d) (e := |g₁ - g₂|)
    dist_nonneg (norm_nonneg _) hd0 (abs_nonneg _) (by rw [hsq, hd1]) (by rw [hnorm, sq_abs])
  have hGd' : |(d - |g₁ - g₂|)| ≤ s := by
    rw [abs_sub_comm]
    exact hGd
  have h6 := abs_sub_le (dist x y) (dist (F.toFun x) (F.toFun y)) ‖π x - π y‖
  rw [abs_sub_comm (dist x y) (dist (F.toFun x) (F.toFun y))] at h6
  linarith

/-- Two vectors of the closed upper half plane whose first coordinates have the same sign are at
most as far apart as the root of the sum of their squared norms. -/
theorem normSq_sub_le_of_halfPlane_OFT (z w : EuclideanSpace ℝ (Fin 2)) (h0 : 0 ≤ z 0 * w 0)
    (hz : 0 ≤ z 1) (hw : 0 ≤ w 1) : ‖z - w‖ ^ 2 ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [norm_sq_fin_two_SMR, norm_sq_fin_two_SMR, norm_sq_fin_two_SMR]
  simp only [PiLp.sub_apply]
  nlinarith [mul_nonneg hz hw]

/-- Among three reals, two have a non-negative product. -/
theorem exists_pair_mul_nonneg_OFT (a₁ a₂ a₃ : ℝ) :
    0 ≤ a₁ * a₂ ∨ 0 ≤ a₁ * a₃ ∨ 0 ≤ a₂ * a₃ := by
  by_contra h
  simp only [not_or, not_le] at h
  obtain ⟨h12, h13, h23⟩ := h
  nlinarith [mul_pos_of_neg_of_neg h13 h23, sq_nonneg a₃, mul_nonneg (sq_nonneg a₃)
    (le_of_lt (neg_pos.mpr h12))]

/-- **Pointed half-plane rigidity (K-PR).** If `B(p, r)` (`r < 6`) contains three points at
mutual distance at least `D` with `b + s ≤ D` and `2 (r + b + s)² < (D - (b + s))²`, then `p` is
not a `(Δ, b, s)` edge point (`b ≤ 1/6`, `s ≤ 1/7`). -/
theorem not_isEdgePoint_of_three_points_OFT {X : Type u} [MetricSpace X] {p x₁ x₂ x₃ : X}
    {Δ b s r D : ℝ} (hb : b ≤ 1 / 6) (hs : s ≤ 1 / 7) (hr : r < 6)
    (h₁ : dist x₁ p ≤ r) (h₂ : dist x₂ p ≤ r) (h₃ : dist x₃ p ≤ r)
    (h₁₂ : D ≤ dist x₁ x₂) (h₁₃ : D ≤ dist x₁ x₃) (h₂₃ : D ≤ dist x₂ x₃)
    (hD : b + s ≤ D) (hgap : 2 * (r + (b + s)) ^ 2 < (D - (b + s)) ^ 2) :
    ¬ isEdgePoint.{u, v} p Δ b s := by
  intro he
  obtain ⟨hb0, hs0, π, hp, hH, hπ⟩ := exists_halfPlane_map_of_isEdgePoint_OFT hb hs he
  have hpb : p ∈ ball p 6 := mem_ball_self (by norm_num)
  have hmem : ∀ x : X, dist x p ≤ r → x ∈ ball p 6 := fun x hx => by
    rw [mem_ball]
    linarith
  -- norms of the images
  have hnorm : ∀ x : X, dist x p ≤ r → ‖π x‖ ^ 2 ≤ (r + (b + s)) ^ 2 := by
    intro x hx
    have h := hπ x (hmem x hx) p hpb
    rw [hp, sub_zero, abs_le] at h
    have h0 := norm_nonneg (π x)
    have h1 : ‖π x‖ ≤ r + (b + s) := by linarith [h.1]
    exact pow_le_pow_left₀ h0 h1 2
  -- distances of the images
  have hdist : ∀ x y : X, dist x p ≤ r → dist y p ≤ r → D ≤ dist x y →
      (D - (b + s)) ^ 2 ≤ ‖π x - π y‖ ^ 2 := by
    intro x y hx hy hxy
    have h := hπ x (hmem x hx) y (hmem y hy)
    rw [abs_le] at h
    have h1 : D - (b + s) ≤ ‖π x - π y‖ := by linarith [h.2]
    exact pow_le_pow_left₀ (by linarith) h1 2
  have key : ∀ x y : X, dist x p ≤ r → dist y p ≤ r → D ≤ dist x y →
      0 ≤ π x 0 * π y 0 → False := by
    intro x y hx hy hxy h0
    have h1 := normSq_sub_le_of_halfPlane_OFT (π x) (π y) h0 (hH x) (hH y)
    have h2 := hdist x y hx hy hxy
    have h3 := hnorm x hx
    have h4 := hnorm y hy
    linarith
  rcases exists_pair_mul_nonneg_OFT (π x₁ 0) (π x₂ 0) (π x₃ 0) with h | h | h
  · exact key x₁ x₂ h₁ h₂ h₁₂ h
  · exact key x₁ x₃ h₁ h₃ h₁₃ h
  · exact key x₂ x₃ h₂ h₃ h₂₃ h

/-- **Consumer (non-vacuity).** The origin of `ℝ × ℝ` with the sup metric is not a `(Δ, b, s)`
edge point for `b, s ≤ 1/200`: the points `(1, 0)`, `(-1, 1)`, `(-1, -1)` are at distance `1` from
the origin and at mutual distance `2`. -/
theorem not_isEdgePoint_sup_plane_OFT {Δ b s : ℝ} (hb : b ≤ 1 / 200) (hs : s ≤ 1 / 200) :
    ¬ isEdgePoint.{0, v} ((0, 0) : ℝ × ℝ) Δ b s := by
  intro he
  have hb6 : b ≤ 1 / 6 := by linarith
  have hs7 : s ≤ 1 / 7 := by linarith
  obtain ⟨hb0, hs0, -⟩ := exists_halfPlane_map_of_isEdgePoint_OFT hb6 hs7 he
  refine not_isEdgePoint_of_three_points_OFT (x₁ := ((1, 0) : ℝ × ℝ)) (x₂ := ((-1, 1) : ℝ × ℝ))
    (x₃ := ((-1, -1) : ℝ × ℝ)) (r := 1) (D := 2) hb6 hs7 (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_
    (by linarith) ?_ he
  · simp [Prod.dist_eq]
  · simp [Prod.dist_eq]
  · simp [Prod.dist_eq]
  · norm_num [Prod.dist_eq, Real.dist_eq]
  · norm_num [Prod.dist_eq, Real.dist_eq]
  · norm_num [Prod.dist_eq, Real.dist_eq]
  · nlinarith [hb0, hs0]

end GC.MetricGeometry
