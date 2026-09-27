import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Prism

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def section34ZigzagHeight (x : ℝ) : ℝ := x - 3 / 2 * max (-1) (min 1 x)

noncomputable def section34ZigzagArc (t : ℝ) : ℝ × ℝ :=
  (4 * t - 2, section34ZigzagHeight (4 * t - 2))

noncomputable def section34StraightArc (t : ℝ) : ℝ × ℝ := (4 * t - 2, t - 1 / 2)

def section34CrossingRectangle : Set (ℝ × ℝ) := Icc (-2) 2 ×ˢ Icc (-1) 1

theorem section34ZigzagHeight_eq_zero_iff (x : ℝ) :
    section34ZigzagHeight x = 0 ↔ x = -3 / 2 ∨ x = 0 ∨ x = 3 / 2 := by
  unfold section34ZigzagHeight
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

theorem section34ZigzagHeight_bounds {x : ℝ} (hx : x ∈ Icc (-2 : ℝ) 2) :
    section34ZigzagHeight x ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
  unfold section34ZigzagHeight
  by_cases hleft : x ≤ -1
  · rw [min_eq_right (by linarith : x ≤ 1), max_eq_left hleft]
    exact ⟨by linarith [hx.1], by linarith⟩
  · by_cases hright : 1 ≤ x
    · rw [min_eq_left hright, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]
      exact ⟨by linarith, by linarith [hx.2]⟩
    · rw [min_eq_right (le_of_not_ge hright), max_eq_right (le_of_not_ge hleft)]
      exact ⟨by linarith, by linarith⟩

theorem isPiecewiseAffineOn_section34ZigzagHeight :
    IsPiecewiseAffineOn section34ZigzagHeight univ := by
  have hx := isPiecewiseAffineOn_id (E := ℝ) isOpen_univ
  have hm := (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ ℝ (1 : ℝ)) isOpen_univ).min hx
  have hc := (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ ℝ (-1 : ℝ)) isOpen_univ).max hm
  have h := hx.add (hc.affine_comp (LinearMap.lsmul ℝ ℝ (-3 / 2 : ℝ)).toAffineMap)
  convert h using 1
  ext x
  simp [section34ZigzagHeight, smul_eq_mul]
  ring

theorem isPLHomeomorphOn_section34ZigzagArc :
    IsPLHomeomorphOn section34ZigzagArc (Icc 0 1) (section34ZigzagArc '' Icc 0 1) := by
  let a : ℝ →ᵃ[ℝ] ℝ := 4 • AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 2
  have ha : IsPiecewiseAffineOn a univ := isPiecewiseAffineOn_of_affine a isOpen_univ
  have hg := isPiecewiseAffineOn_section34ZigzagHeight.comp ha
  rw [preimage_univ, inter_univ] at hg
  have hp : IsPiecewiseAffineOn section34ZigzagArc univ := by
    apply (ha.prod_mk hg).congr
    intro x _
    simp [a, section34ZigzagArc]
  have hi : InjOn section34ZigzagArc (Icc 0 1) := by
    intro s _ t _ hst
    have heq := congrArg Prod.fst hst
    change 4 * s - 2 = 4 * t - 2 at heq
    linarith
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (hp.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (subset_univ _)) hi.bijOn_image

theorem isPLHomeomorphOn_section34StraightArc :
    IsPLHomeomorphOn section34StraightArc (Icc 0 1) (section34StraightArc '' Icc 0 1) := by
  let a : ℝ →ᵃ[ℝ] ℝ × ℝ :=
    (4 • AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 2).prod
      (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ (1 / 2))
  have hp : IsPiecewiseAffineOn section34StraightArc univ := by
    apply (isPiecewiseAffineOn_of_affine a isOpen_univ).congr
    intro x _
    simp [a, section34StraightArc]
  have hi : InjOn section34StraightArc (Icc 0 1) := by
    intro s _ t _ hst
    have heq := congrArg Prod.fst hst
    change 4 * s - 2 = 4 * t - 2 at heq
    linarith
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (hp.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (subset_univ _)) hi.bijOn_image

theorem section34ZigzagArc_endpoints :
    section34ZigzagArc 0 = section34StraightArc 0 ∧
      section34ZigzagArc 1 = section34StraightArc 1 := by
  norm_num [section34ZigzagArc, section34ZigzagHeight, section34StraightArc]

theorem section34ZigzagArc_three_crossings :
    (section34ZigzagArc '' Icc 0 1) ∩ {p : ℝ × ℝ | p.2 = 0} =
      {(-3 / 2, 0), (0, 0), (3 / 2, 0)} := by
  apply Subset.antisymm
  · rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
    have h := (section34ZigzagHeight_eq_zero_iff (4 * t - 2)).mp hz
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
      norm_num [section34ZigzagArc, section34ZigzagHeight]
    · refine ⟨⟨1 / 2, by norm_num, ?_⟩, rfl⟩
      norm_num [section34ZigzagArc, section34ZigzagHeight]
    · refine ⟨⟨7 / 8, by norm_num, ?_⟩, rfl⟩
      norm_num [section34ZigzagArc, section34ZigzagHeight]

theorem section34StraightArc_one_crossing :
    (section34StraightArc '' Icc 0 1) ∩ {p : ℝ × ℝ | p.2 = 0} = {(0, 0)} := by
  apply Subset.antisymm
  · rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
    have ht' : t = 1 / 2 := by change t - 1 / 2 = 0 at hz; linarith
    subst t
    norm_num [section34StraightArc]
  · rintro p rfl
    exact ⟨⟨1 / 2, by norm_num, by norm_num [section34StraightArc]⟩, rfl⟩

theorem isPLBall_section34CrossingRectangle : IsPLBall 2 section34CrossingRectangle :=
  isPLBall_two_prod (isPLBall_Icc (by norm_num)) (isPLBall_Icc (by norm_num))

def section34HorizontalArc (t : ℝ) : ℝ × ℝ := (4 * t - 2, 0)

theorem isPLHomeomorphOn_section34HorizontalArc :
    IsPLHomeomorphOn section34HorizontalArc (Icc 0 1) (section34HorizontalArc '' Icc 0 1) := by
  let a : ℝ →ᵃ[ℝ] ℝ × ℝ :=
    (4 • AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 2).prod (AffineMap.const ℝ ℝ (0 : ℝ))
  have hp : IsPiecewiseAffineOn section34HorizontalArc univ := by
    apply (isPiecewiseAffineOn_of_affine a isOpen_univ).congr
    intro x _
    simp [a, section34HorizontalArc]
  have hi : InjOn section34HorizontalArc (Icc 0 1) := by
    intro s _ t _ hst
    have heq := congrArg Prod.fst hst
    change 4 * s - 2 = 4 * t - 2 at heq
    linarith
  exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (hp.mono_of_isPolyhedron isHPolytope_Icc.isPolyhedron (subset_univ _)) hi.bijOn_image

theorem section34HorizontalArc_image : section34HorizontalArc '' Icc 0 1 =
    section34CrossingRectangle ∩ {p : ℝ × ℝ | p.2 = 0} := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, rfl⟩
    · dsimp [section34HorizontalArc]
      linarith [ht.1]
    · dsimp [section34HorizontalArc]
      linarith [ht.2]
    · norm_num [section34HorizontalArc]
    · norm_num [section34HorizontalArc]
  · rintro p ⟨hp, hz⟩
    refine ⟨(p.1 + 2) / 4, ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, ?_⟩
    apply Prod.ext
    · dsimp [section34HorizontalArc]
      ring
    · exact hz.symm

end DifferentialGeometry.Topology.PiecewiseLinear
