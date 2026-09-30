import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Prism

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def zigzagHeight (x : ℝ) : ℝ := x - 3 / 2 * max (-1) (min 1 x)

noncomputable def zigzagArc (t : ℝ) : ℝ × ℝ :=
  (4 * t - 2, zigzagHeight (4 * t - 2))

noncomputable def straightCrossingArc (t : ℝ) : ℝ × ℝ := (4 * t - 2, t - 1 / 2)

def crossingRectangle : Set (ℝ × ℝ) := Icc (-2) 2 ×ˢ Icc (-1) 1

theorem zigzagHeight_eq_zero_iff (x : ℝ) :
    zigzagHeight x = 0 ↔ x = -3 / 2 ∨ x = 0 ∨ x = 3 / 2 := by
  unfold zigzagHeight
  by_cases hleft : x ≤ -1
  · rw [min_eq_right (by linarith : x ≤ 1), max_eq_left hleft]
    constructor
    · intro h
      exact Or.inl (by linarith)
    · rintro (rfl | rfl | rfl) <;> norm_num at *
  · by_cases hright : 1 ≤ x
    · rw [min_eq_left hright, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
      constructor
      · intro h
        exact Or.inr (Or.inr (by linarith))
      · rintro (rfl | rfl | rfl) <;> norm_num at *
    · rw [min_eq_right (le_of_not_ge hright), max_eq_right (le_of_not_ge hleft)]
      constructor
      · intro h
        exact Or.inr (Or.inl (by linarith))
      · rintro (rfl | rfl | rfl) <;> norm_num at *

theorem zigzagHeight_bounds {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) 2) :
    zigzagHeight x ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
  unfold zigzagHeight
  by_cases hleft : x ≤ -1
  · rw [min_eq_right (by linarith : x ≤ 1), max_eq_left hleft]
    exact ⟨by linarith [hx.1], by linarith⟩
  · by_cases hright : 1 ≤ x
    · rw [min_eq_left hright, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
      exact ⟨by linarith, by linarith [hx.2]⟩
    · rw [min_eq_right (le_of_not_ge hright), max_eq_right (le_of_not_ge hleft)]
      exact ⟨by linarith, by linarith⟩

theorem isPiecewiseAffineOn_zigzagHeight :
    IsPiecewiseAffineOn zigzagHeight univ := by
  have hx := isPiecewiseAffineOn_id (E := ℝ) isOpen_univ
  have hm := (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ ℝ (1 : ℝ)) isOpen_univ).min hx
  have hc := (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ ℝ (-1 : ℝ)) isOpen_univ).max hm
  have h := hx.add (hc.affine_comp (LinearMap.lsmul ℝ ℝ (-3 / 2 : ℝ)).toAffineMap)
  convert h using 1
  ext x
  simp [zigzagHeight, smul_eq_mul]
  ring

theorem isPLHomeomorphOn_zigzagArc :
    IsPLHomeomorphOn zigzagArc (Icc 0 1) (zigzagArc '' Icc 0 1) := by
  let a : ℝ →ᵃ[ℝ] ℝ := 4 • AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 2
  have ha : IsPiecewiseAffineOn a univ := isPiecewiseAffineOn_of_affine a isOpen_univ
  have hg := isPiecewiseAffineOn_zigzagHeight.comp ha
  rw [preimage_univ, inter_univ] at hg
  have hp : IsPiecewiseAffineOn zigzagArc univ := by
    apply (ha.prod_mk hg).congr
    intro x _
    simp [a, zigzagArc]
  have hi : InjOn zigzagArc (Icc 0 1) := by
    intro s _ t _ hst
    have heq := congrArg Prod.fst hst
    change 4 * s - 2 = 4 * t - 2 at heq
    linarith
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (hp.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (subset_univ _)) hi.bijOn_image

theorem isPLHomeomorphOn_straightCrossingArc :
    IsPLHomeomorphOn straightCrossingArc (Icc 0 1) (straightCrossingArc '' Icc 0 1) := by
  let a : ℝ →ᵃ[ℝ] ℝ × ℝ :=
    (4 • AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 2).prod
      (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ (1 / 2))
  have hp : IsPiecewiseAffineOn straightCrossingArc univ := by
    apply (isPiecewiseAffineOn_of_affine a isOpen_univ).congr
    intro x _
    simp [a, straightCrossingArc]
  have hi : InjOn straightCrossingArc (Icc 0 1) := by
    intro s _ t _ hst
    have heq := congrArg Prod.fst hst
    change 4 * s - 2 = 4 * t - 2 at heq
    linarith
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (hp.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (subset_univ _)) hi.bijOn_image

theorem zigzagArc_endpoints :
    zigzagArc 0 = straightCrossingArc 0 ∧
      zigzagArc 1 = straightCrossingArc 1 := by
  norm_num [zigzagArc, zigzagHeight, straightCrossingArc]

theorem zigzagArc_three_crossings :
    (zigzagArc '' Icc 0 1) ∩ {p : ℝ × ℝ | p.2 = 0} =
      {(-3 / 2, 0), (0, 0), (3 / 2, 0)} := by
  apply Subset.antisymm
  · rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
    have h := (zigzagHeight_eq_zero_iff (4 * t - 2)).mp hz
    rcases h with h | h | h
    · left
      exact Prod.ext h hz
    · right
      left
      exact Prod.ext h hz
    · right
      right
      exact Prod.ext h hz
  · rintro p (rfl | rfl | rfl)
    · refine ⟨⟨1 / 8, by norm_num, ?_⟩, rfl⟩
      norm_num [zigzagArc, zigzagHeight]
    · refine ⟨⟨1 / 2, by norm_num, ?_⟩, rfl⟩
      norm_num [zigzagArc, zigzagHeight]
    · refine ⟨⟨7 / 8, by norm_num, ?_⟩, rfl⟩
      norm_num [zigzagArc, zigzagHeight]

theorem straightCrossingArc_one_crossing :
    (straightCrossingArc '' Icc 0 1) ∩ {p : ℝ × ℝ | p.2 = 0} = {(0, 0)} := by
  apply Subset.antisymm
  · rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
    have ht' : t = 1 / 2 := by change t - 1 / 2 = 0 at hz; linarith
    subst t
    norm_num [straightCrossingArc]
  · rintro p rfl
    exact ⟨⟨1 / 2, by norm_num, by norm_num [straightCrossingArc]⟩, rfl⟩

theorem isPLBall_crossingRectangle : IsPLBall 2 crossingRectangle :=
  isPLBall_two_prod (isPLBall_Icc (by norm_num)) (isPLBall_Icc (by norm_num))

def horizontalCrossingArc (t : ℝ) : ℝ × ℝ := (4 * t - 2, 0)

theorem isPLHomeomorphOn_horizontalCrossingArc :
    IsPLHomeomorphOn horizontalCrossingArc (Icc 0 1) (horizontalCrossingArc '' Icc 0 1) := by
  let a : ℝ →ᵃ[ℝ] ℝ × ℝ :=
    (4 • AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 2).prod (AffineMap.const ℝ ℝ (0 : ℝ))
  have hp : IsPiecewiseAffineOn horizontalCrossingArc univ := by
    apply (isPiecewiseAffineOn_of_affine a isOpen_univ).congr
    intro x _
    simp [a, horizontalCrossingArc]
  have hi : InjOn horizontalCrossingArc (Icc 0 1) := by
    intro s _ t _ hst
    have heq := congrArg Prod.fst hst
    change 4 * s - 2 = 4 * t - 2 at heq
    linarith
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (hp.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (subset_univ _)) hi.bijOn_image

theorem horizontalCrossingArc_image : horizontalCrossingArc '' Icc 0 1 =
    crossingRectangle ∩ {p : ℝ × ℝ | p.2 = 0} := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, rfl⟩
    · dsimp [horizontalCrossingArc]
      linarith [ht.1]
    · dsimp [horizontalCrossingArc]
      linarith [ht.2]
    · norm_num [horizontalCrossingArc]
    · norm_num [horizontalCrossingArc]
  · rintro p ⟨hp, hz⟩
    refine ⟨(p.1 + 2) / 4, ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, ?_⟩
    apply Prod.ext
    · dsimp [horizontalCrossingArc]
      ring
    · exact hz.symm

end DifferentialGeometry.Topology.PiecewiseLinear
