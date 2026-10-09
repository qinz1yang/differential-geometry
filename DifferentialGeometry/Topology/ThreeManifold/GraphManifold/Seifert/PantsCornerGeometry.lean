import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsBridges

/-!
# Elementary inequalities at the corners of the pants hexagon

Packet K16f, tier 2 (real inequalities). On the horocycle `heightOne x y = 3/5` about the cusp
`0` one has `x² + y² = 5y/12`, `x = -(5/3) X y` and `y (25 X² + 9) = 15/4` for
`X = holeX x y`, so the disc of radius `12/125` about `1/4 + 37i/100` cuts out an interval of
`X`, and `horocycle_zero_cases` sorts the points outside it. `lens_arc_inside`,
`lens_boundary_heightHalf` and `middle_box_inside` locate the lens between the semicircles
`|z| = 1/2`, `|z - 1/2| = 1/2`, the wall `wallTwo = 1/25` and the horoballs of level `3/5`;
`heightHalf_lt_of_heightOne` is the disjointness of the horoballs about `0` and `1/2` at level
`599/1000`. The last statements compare the radial profiles `bridgeSigma` and `bridgeRho`.
-/

set_option autoImplicit false

namespace GC.Seifert

private theorem horo_relations {x y : ℝ} (hy : 0 < y) (hh : heightOne x y = 3 / 5) :
    x ^ 2 + y ^ 2 = 5 * y / 12 ∧ x = -(5 / 3) * holeX x y * y ∧
      y * (25 * holeX x y ^ 2 + 9) = 15 / 4 := by
  have hS0 : 0 < x ^ 2 + y ^ 2 := by positivity
  have hX : holeX x y * (4 * (x ^ 2 + y ^ 2)) = -x := by
    unfold holeX
    field_simp
  unfold heightOne at hh
  rw [div_eq_iff (by positivity)] at hh
  have hS : x ^ 2 + y ^ 2 = 5 * y / 12 := by linarith
  have hx : x = -(5 / 3) * holeX x y * y := by
    rw [hS] at hX
    linear_combination hX
  refine ⟨hS, hx, ?_⟩
  have h' : y * (y * (25 * holeX x y ^ 2 + 9) - 15 / 4) = 0 := by
    rw [hx] at hS
    linear_combination 9 * hS
  rcases mul_eq_zero.1 h' with h' | h'
  · linarith
  · linarith

private theorem horo_quadratic {x y X : ℝ} (hS : x ^ 2 + y ^ 2 = 5 * y / 12)
    (hx : x = -(5 / 3) * X * y) (hyX : y * (25 * X ^ 2 + 9) = 15 / 4)
    (hout : (12 / 125) ^ 2 < (x - 1 / 4) ^ 2 + (y - 37 / 100) ^ 2) :
    0 < 23773 / 5000 * X ^ 2 + 25 / 8 * X + 23773 * 9 / 125000 - 97 / 80 := by
  have e : (x - 1 / 4) ^ 2 + (y - 37 / 100) ^ 2 = (5 / 6 * X - 97 / 300) * y + 997 / 5000 := by
    linear_combination hS - (1 / 2) * hx
  have hP : (0 : ℝ) < 25 * X ^ 2 + 9 := by positivity
  have h2 : 0 < ((5 / 6 * X - 97 / 300) * y + 997 / 5000 - (12 / 125) ^ 2) *
      (25 * X ^ 2 + 9) := mul_pos (by linarith) hP
  have e2 : 23773 / 5000 * X ^ 2 + 25 / 8 * X + 23773 * 9 / 125000 - 97 / 80 =
      ((5 / 6 * X - 97 / 300) * y + 997 / 5000 - (12 / 125) ^ 2) * (25 * X ^ 2 + 9) := by
    linear_combination (-(5 / 6 * X - 97 / 300)) * hyX
  rw [e2]
  exact h2

private theorem horo_le_nine {X : ℝ}
    (hq : 0 < 23773 / 5000 * X ^ 2 + 25 / 8 * X + 23773 * 9 / 125000 - 97 / 80)
    (hA : X < -(3 / 10)) : X ≤ -(9 / 25) := by
  by_contra hn
  have hn' : -(9 / 25) < X := lt_of_not_ge hn
  nlinarith [mul_pos (sub_pos.2 hn') (sub_pos.2 hA)]

private theorem horo_y_le {y X : ℝ} (hy : 0 < y) (hyX : y * (25 * X ^ 2 + 9) = 15 / 4) :
    y ≤ 5 / 12 := by
  nlinarith [mul_nonneg hy.le (sq_nonneg X)]

private theorem horo_x_le {x y X : ℝ} (hy : 0 < y) (hx : x = -(5 / 3) * X * y)
    (hy5 : y ≤ 5 / 12) (hA : -(3 / 10) ≤ X) : x ≤ 11 / 50 := by
  have h := mul_nonneg (by linarith : (0 : ℝ) ≤ X + 3 / 10) hy.le
  rw [hx]
  nlinarith

private theorem horo_wall_gt {y X : ℝ} (hy : 0 < y) (hyX : y * (25 * X ^ 2 + 9) = 15 / 4)
    (hA : -(3 / 10) ≤ X) (hB : X ≤ -(1 / 4)) : 11 / 250 < 5 / 12 * y * (1 + 2 * X) := by
  have hX2 : X ^ 2 ≤ 9 / 100 := by nlinarith
  have hy3 : 1 / 3 ≤ y := by nlinarith [mul_le_mul_of_nonneg_left hX2 hy.le]
  nlinarith [mul_nonneg (sub_nonneg.2 hy3) (by linarith : (0 : ℝ) ≤ 1 + 2 * X - 2 / 5)]

private theorem horo_wall_lt {y X : ℝ} (hyX : y * (25 * X ^ 2 + 9) = 15 / 4)
    (hB : X ≤ -(9 / 25)) : 5 / 12 * y * (1 + 2 * X) < 9 / 250 := by
  have hP : (0 : ℝ) < 25 * X ^ 2 + 9 := by positivity
  have key : 5 / 12 * y * (1 + 2 * X) * (25 * X ^ 2 + 9) < 9 / 250 * (25 * X ^ 2 + 9) := by
    have e : 5 / 12 * y * (1 + 2 * X) * (25 * X ^ 2 + 9) = 25 / 16 * (1 + 2 * X) := by
      linear_combination 5 / 12 * (1 + 2 * X) * hyX
    rw [e]
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : X + 9 / 25 ≤ 0)
      (by linarith : 9 / 10 * X - 3449 / 1000 ≤ 0)]
  exact lt_of_mul_lt_mul_right key hP.le

theorem horocycle_zero_cases {x y : ℝ} (hy : 0 < y) (hh : heightOne x y = 3 / 5)
    (hout : (12 / 125) ^ 2 < (x - 1 / 4) ^ 2 + (y - 37 / 100) ^ 2) :
    (-(3 / 10) ≤ holeX x y ∧ x ≤ 11 / 50 ∧ y ≤ 47 / 100 ∧
        (11 / 250 < wallTwo x y ∨ -(1 / 4) < holeX x y)) ∨
      (holeX x y ≤ -(9 / 25) ∧ wallTwo x y < 9 / 250 ∧ holeX x y < -(1 / 4)) := by
  obtain ⟨hS, hx, hyX⟩ := horo_relations hy hh
  have hq := horo_quadratic hS hx hyX hout
  have hW : wallTwo x y = 5 / 12 * y * (1 + 2 * holeX x y) := by
    unfold wallTwo
    linear_combination hS - (1 / 2) * hx
  have hy5 := horo_y_le hy hyX
  rw [hW]
  rcases le_or_gt (-(3 / 10)) (holeX x y) with hA | hA
  · refine Or.inl ⟨hA, horo_x_le hy hx hy5 hA, by linarith, ?_⟩
    rcases lt_or_ge (-(1 / 4)) (holeX x y) with hB | hB
    · exact Or.inr hB
    · exact Or.inl (horo_wall_gt hy hyX hA hB)
  · have hB := horo_le_nine hq hA
    exact Or.inr ⟨hB, horo_wall_lt hyX hB, by linarith⟩

theorem wallTwo_mirror (x y : ℝ) : wallTwo (1 / 2 - x) y = wallTwo x y := by
  unfold wallTwo
  ring

theorem bridgeSigma_three_fifths_lt : bridgeSigma (3 / 5) < 3 / 2 := by
  unfold bridgeSigma
  norm_num

theorem bridgeSigma_add_lt_bridgeRho : 3 / 2 + bridgeSigma (3 / 5) < bridgeRho (11 / 25) := by
  unfold bridgeSigma bridgeRho
  norm_num

theorem strictAntiOn_bridgeSigma : StrictAntiOn bridgeSigma (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  unfold bridgeSigma
  have h : 2 / (1 + 4 * b ^ 2) < 2 / (1 + 4 * a ^ 2) :=
    div_lt_div_of_pos_left (by norm_num) (by positivity) (by nlinarith)
  linarith

theorem strictMonoOn_bridgeRho : StrictMonoOn bridgeRho (Set.Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  unfold bridgeRho
  have h : 2 / (1 + 4 * b ^ 2) < 2 / (1 + 4 * a ^ 2) :=
    div_lt_div_of_pos_left (by norm_num) (by positivity) (by nlinarith)
  linarith

theorem heightHalf_lt_of_heightOne {x y : ℝ} (hy : 0 < y) (h : 599 / 1000 ≤ heightOne x y) :
    heightOne (1 / 2 - x) y < 599 / 1000 := by
  unfold heightOne at h ⊢
  rw [le_div_iff₀ (by positivity)] at h
  rw [div_lt_iff₀ (by positivity)]
  by_contra hc
  have hc' := not_lt.1 hc
  have hs : 4 * (599 / 1000) * (2 * y ^ 2 + 1 / 8) ≤ 2 * y := by
    nlinarith [sq_nonneg (x - 1 / 4)]
  nlinarith [sq_nonneg (8 * (599 / 1000) * y - 1)]

theorem lens_boundary_heightHalf {x y : ℝ} (hy : 0 < y) (h : x ^ 2 + y ^ 2 = 1 / 4)
    (hw : wallTwo x y ≤ 1 / 25) : 3 / 5 < heightOne (1 / 2 - x) y := by
  unfold wallTwo at hw
  unfold heightOne
  have hx1 : 21 / 50 ≤ x := by linarith
  have hx2 : x < 1 / 2 := by nlinarith
  have hS : (1 / 2 - x) ^ 2 + y ^ 2 = 1 / 2 - x := by nlinarith
  rw [hS, lt_div_iff₀ (by linarith)]
  have hy2 : (12 / 5 * (1 / 2 - x)) ^ 2 < y ^ 2 := by nlinarith
  nlinarith

theorem middle_box_inside {x y : ℝ} (hy : 0 < y) (h1 : 23 / 100 < x) (h2 : x < 27 / 100)
    (h3 : y ≤ 11 / 25) (hw : 1 / 25 ≤ wallTwo x y) :
    (x - 1 / 4) ^ 2 + (y - 37 / 100) ^ 2 < (12 / 125) ^ 2 := by
  unfold wallTwo at hw
  have hy2 : (31 / 100) ^ 2 ≤ y ^ 2 := by nlinarith
  have hy3 : 31 / 100 ≤ y := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hy3) (sub_nonneg.2 h3), mul_pos (sub_pos.2 h1) (sub_pos.2 h2)]

theorem lens_arc_inside {x y : ℝ} (hy : 0 < y) (hw : wallTwo x y = 1 / 25)
    (h1 : x ^ 2 + y ^ 2 < 1 / 4) (h2 : (x - 1 / 2) ^ 2 + y ^ 2 < 1 / 4)
    (h3 : heightOne x y ≤ 3 / 5) (h4 : heightOne (1 / 2 - x) y ≤ 3 / 5) :
    (x - 1 / 4) ^ 2 + (y - 37 / 100) ^ 2 < (12 / 125) ^ 2 := by
  unfold wallTwo at hw
  unfold heightOne at h3 h4
  rw [div_le_iff₀ (by positivity)] at h3 h4
  have hc : (x - 1 / 4) ^ 2 + y ^ 2 = 41 / 400 := by nlinarith
  have hu : (x - 1 / 4) ^ 2 ≤ (3 / 40) ^ 2 := by
    rcases le_total (1 / 4) x with hx | hx
    · have k : y ≤ 99 / 250 - 6 / 5 * (x - 1 / 4) := by nlinarith
      have k2 : y ^ 2 ≤ (99 / 250 - 6 / 5 * (x - 1 / 4)) ^ 2 := by nlinarith
      have k3 : x - 1 / 4 < 17 / 100 := by nlinarith
      by_contra hn
      have hn' := lt_of_not_ge hn
      have k4 : 3 / 40 < x - 1 / 4 := by nlinarith
      nlinarith [mul_pos (sub_pos.2 k4) (sub_pos.2 k3)]
    · have k : y ≤ 99 / 250 + 6 / 5 * (x - 1 / 4) := by nlinarith
      have k2 : y ^ 2 ≤ (99 / 250 + 6 / 5 * (x - 1 / 4)) ^ 2 := by nlinarith
      have k3 : -(17 / 100) < x - 1 / 4 := by nlinarith
      by_contra hn
      have hn' := lt_of_not_ge hn
      have k4 : x - 1 / 4 < -(3 / 40) := by nlinarith
      nlinarith [mul_pos (sub_pos.2 k4) (sub_pos.2 k3)]
  have hy2 : 3111 / 10000 < y := by nlinarith
  nlinarith

end GC.Seifert
