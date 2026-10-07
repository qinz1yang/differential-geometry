import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryMetric
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.KleinCompactification
import DifferentialGeometry.Topology.FixedPoint.Brouwer
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.FixedPoints.Defs
import Mathlib.Analysis.InnerProductSpace.Convex

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem exists_fixedPoint_of_kleinClosedBall_fixed
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (u : Metric.closedBall (0 : E) 1)
    (hu : ‖(u : E)‖ < 1) (hfix : kleinClosedBallHomeomorph f u = u) :
    ∃ x : Hyperboloid E, f x = x := by
  let v : Metric.ball (0 : E) 1 := ⟨u, by simpa only [Metric.mem_ball, dist_zero_right] using hu⟩
  let x : Hyperboloid E := kleinHomeomorph.symm v
  have hx : (kleinHomeomorph x : E) = (u : E) :=
    congrArg Subtype.val (kleinHomeomorph.apply_symm_apply v)
  have hi : Set.inclusion Metric.ball_subset_closedBall (kleinHomeomorph x) = u :=
    Subtype.ext hx
  have h := kleinClosedBallHomeomorph_apply_kleinHomeomorph f x
  rw [hi, hfix] at h
  refine ⟨x, kleinHomeomorph.injective ?_⟩
  exact Subtype.ext (h.symm.trans hx.symm)

theorem boundary_time_mul_eq_one_of_fixed
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (ξ η : Metric.sphere (0 : E) 1)
    (hξ : boundaryHomeomorph f ξ = ξ) (hη : boundaryHomeomorph f η = η) (hne : ξ ≠ η) :
    (lorentzExtension f (1, (ξ : E))).1 * (lorentzExtension f (1, (η : E))).1 = 1 := by
  have h := dist_boundaryHomeomorph_sq f ξ η
  rw [hξ, hη] at h
  have hp : 0 < (lorentzExtension f (1, (ξ : E))).1 *
      (lorentzExtension f (1, (η : E))).1 :=
    mul_pos (lorentzExtension_sphere_time_pos f ξ) (lorentzExtension_sphere_time_pos f η)
  have hd : dist ξ η ^ 2 ≠ 0 := pow_ne_zero 2 (dist_ne_zero.mpr hne)
  have he := (eq_div_iff hp.ne').mp h
  apply (mul_left_cancel₀ hd)
  simpa only [mul_one] using he

private theorem null_vector_fixed_of_boundary_time_eq_one
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (ξ : Metric.sphere (0 : E) 1)
    (hξ : boundaryHomeomorph f ξ = ξ) (ht : (lorentzExtension f (1, (ξ : E))).1 = 1) :
    lorentzExtension f (1, (ξ : E)) = (1, (ξ : E)) := by
  have h := boundaryHomeomorph_apply_coe f ξ
  rw [hξ, ht, inv_one, one_smul] at h
  exact Prod.ext ht h.symm

private theorem exists_fixedPoint_of_three_boundary_fixed
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (ξ η ζ : Metric.sphere (0 : E) 1)
    (hξ : boundaryHomeomorph f ξ = ξ) (hη : boundaryHomeomorph f η = η)
    (hζ : boundaryHomeomorph f ζ = ζ) (hξη : ξ ≠ η) (hξζ : ξ ≠ ζ) (hηζ : η ≠ ζ) :
    ∃ x : Hyperboloid E, f x = x := by
  let a := (lorentzExtension f (1, (ξ : E))).1
  let b := (lorentzExtension f (1, (η : E))).1
  let c := (lorentzExtension f (1, (ζ : E))).1
  have ha : 0 < a := lorentzExtension_sphere_time_pos f ξ
  have hb : 0 < b := lorentzExtension_sphere_time_pos f η
  have hab : a * b = 1 := boundary_time_mul_eq_one_of_fixed f ξ η hξ hη hξη
  have hac : a * c = 1 := boundary_time_mul_eq_one_of_fixed f ξ ζ hξ hζ hξζ
  have hbc : b * c = 1 := boundary_time_mul_eq_one_of_fixed f η ζ hη hζ hηζ
  have hbeq : b = c := mul_left_cancel₀ ha.ne' (hab.trans hac.symm)
  have hb1 : b = 1 := by nlinarith only [hbc, hbeq, hb]
  have ha1 : a = 1 := by nlinarith only [hab, hb1]
  have hAξ := null_vector_fixed_of_boundary_time_eq_one f ξ hξ ha1
  have hAη := null_vector_fixed_of_boundary_time_eq_one f η hη hb1
  let u : E := (2 : ℝ)⁻¹ • ((ξ : E) + (η : E))
  have hd : 0 < ‖(ξ : E) - (η : E)‖ ^ 2 := by
    apply sq_pos_of_pos
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hξη (Subtype.ext h)))
  have hs : ‖(ξ : E) + (η : E)‖ < 2 := by
    have ha' := norm_add_sq_real (ξ : E) (η : E)
    have hs' := norm_sub_sq_real (ξ : E) (η : E)
    simp only [norm_eq_of_mem_sphere, one_pow] at ha' hs'
    nlinarith only [ha', hs', hd, norm_nonneg ((ξ : E) + (η : E))]
  have hu : ‖u‖ < 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith only [hs]
  have hv : ((1 : ℝ), u) = (2 : ℝ)⁻¹ • ((1, (ξ : E)) + (1, (η : E))) := by
    apply Prod.ext
    · norm_num
    · rfl
  have hAu : lorentzExtension f (1, u) = (1, u) := by
    rw [hv, map_smul, map_add, hAξ, hAη]
  let q : Metric.closedBall (0 : E) 1 :=
    ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu.le⟩
  have hq : kleinClosedBallHomeomorph f q = q := by
    apply Subtype.ext
    rw [kleinClosedBallHomeomorph_apply_coe]
    change (lorentzExtension f (1, u)).1⁻¹ • (lorentzExtension f (1, u)).2 = u
    rw [hAu]
    simp
  exact exists_fixedPoint_of_kleinClosedBall_fixed f q hu hq

theorem fixedPoints_boundaryHomeomorph_encard_le_two
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (hfree : ∀ x : Hyperboloid E, f x ≠ x) :
    (Function.fixedPoints (boundaryHomeomorph f)).encard ≤ 2 := by
  classical
  let S := Function.fixedPoints (boundaryHomeomorph f)
  change S.encard ≤ 2
  by_cases hsmall : S.encard ≤ 1
  · exact hsmall.trans (by norm_num)
  obtain ⟨ξ, η, hξ, hη, hne⟩ := Set.one_lt_encard_iff.mp (lt_of_not_ge hsmall)
  have hsub : S ⊆ {ξ, η} := by
    intro ζ hζ
    by_cases hζξ : ζ = ξ
    · simp [hζξ]
    by_cases hζη : ζ = η
    · simp [hζη]
    obtain ⟨x, hx⟩ := exists_fixedPoint_of_three_boundary_fixed f ξ η ζ hξ hη hζ
      hne (Ne.symm hζξ) (Ne.symm hζη)
    exact (hfree x hx).elim
  exact (Set.encard_mono hsub).trans_eq (Set.encard_pair hne)

theorem fixedPoints_boundaryHomeomorph_nonempty [FiniteDimensional ℝ E]
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (hfree : ∀ x : Hyperboloid E, f x ≠ x) :
    (Function.fixedPoints (boundaryHomeomorph f)).Nonempty := by
  obtain ⟨u, hu⟩ := Topology.FixedPoint.exists_fixedPoint_closedBall_of_continuous
    (kleinClosedBallHomeomorph f) (kleinClosedBallHomeomorph f).continuous
  have hle : ‖(u : E)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using u.property
  have heq : ‖(u : E)‖ = 1 := by
    apply le_antisymm hle
    by_contra h
    obtain ⟨x, hx⟩ := exists_fixedPoint_of_kleinClosedBall_fixed f u (lt_of_not_ge h) hu
    exact hfree x hx
  let ξ : Metric.sphere (0 : E) 1 :=
    ⟨u, by simpa only [Metric.mem_sphere, dist_zero_right] using heq⟩
  refine ⟨ξ, ?_⟩
  change boundaryHomeomorph f ξ = ξ
  apply Subtype.ext
  have h := kleinClosedBallHomeomorph_apply_sphere f ξ
  have hi : Set.inclusion Metric.sphere_subset_closedBall ξ = u := rfl
  rw [hi, hu] at h
  exact h.symm

theorem exists_fixedPoint_of_boundary_swap
    (f : Hyperboloid E ≃ᵢ Hyperboloid E)
    (ξ η : Metric.sphere (0 : E) 1) (hne : ξ ≠ η)
    (hξη : boundaryHomeomorph f ξ = η) (hηξ : boundaryHomeomorph f η = ξ) :
    ∃ x : Hyperboloid E, f x = x := by
  let a := (lorentzExtension f (1, (ξ : E))).1
  let b := (lorentzExtension f (1, (η : E))).1
  have ha : 0 < a := lorentzExtension_sphere_time_pos f ξ
  have hb : 0 < b := lorentzExtension_sphere_time_pos f η
  have hab : a * b = 1 := by
    have h := dist_boundaryHomeomorph_sq f ξ η
    rw [hξη, hηξ, dist_comm η ξ] at h
    have hd : dist ξ η ^ 2 ≠ 0 := pow_ne_zero 2 (dist_ne_zero.mpr hne)
    have he := (eq_div_iff (mul_pos ha hb).ne').mp h
    apply mul_left_cancel₀ hd
    simpa only [mul_one] using he
  have hlift (ζ : Metric.sphere (0 : E) 1) :
      lorentzExtension f (1, (ζ : E)) =
        (lorentzExtension f (1, (ζ : E))).1 •
          (1, (boundaryHomeomorph f ζ : E)) := by
    apply Prod.ext
    · change (lorentzExtension f (1, (ζ : E))).1 =
        (lorentzExtension f (1, (ζ : E))).1 * 1
      rw [mul_one]
    · change (lorentzExtension f (1, (ζ : E))).2 =
        (lorentzExtension f (1, (ζ : E))).1 • (boundaryHomeomorph f ζ : E)
      rw [boundaryHomeomorph_apply_coe, smul_smul,
        mul_inv_cancel₀ (lorentzExtension_sphere_time_pos f ζ).ne', one_smul]
  have hAξ : lorentzExtension f (1, (ξ : E)) = a • (1, (η : E)) := by
    simpa only [hξη] using hlift ξ
  have hAη : lorentzExtension f (1, (η : E)) = b • (1, (ξ : E)) := by
    simpa only [hηξ] using hlift η
  have hsum : 0 < 1 + a := by linarith only [ha]
  let c : ℝ := (1 + a)⁻¹
  have hc : 0 < c := inv_pos.mpr hsum
  have hcoeff : c + c * a = 1 := by
    dsimp only [c]
    rw [← mul_one_add, inv_mul_cancel₀ hsum.ne']
  let u : E := c • (ξ : E) + (c * a) • (η : E)
  have hu : ‖u‖ < 1 := norm_combo_lt_of_ne
    (norm_eq_of_mem_sphere ξ).le (norm_eq_of_mem_sphere η).le
    (fun h => hne (Subtype.ext h)) hc (mul_pos hc ha) hcoeff
  have hv : ((1 : ℝ), u) = c • ((1, (ξ : E)) + a • (1, (η : E))) := by
    apply Prod.ext
    · change 1 = c * (1 + a * 1)
      rw [mul_one]
      exact (inv_mul_cancel₀ hsum.ne').symm
    · change c • (ξ : E) + (c * a) • (η : E) = c • ((ξ : E) + a • (η : E))
      rw [smul_add, smul_smul]
  have hAu : lorentzExtension f (1, u) = (1, u) := by
    rw [hv, map_smul, map_add, hAξ, map_smul, hAη, smul_smul, hab, one_smul, add_comm]
  let q : Metric.closedBall (0 : E) 1 :=
    ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu.le⟩
  have hq : kleinClosedBallHomeomorph f q = q := by
    apply Subtype.ext
    rw [kleinClosedBallHomeomorph_apply_coe]
    change (lorentzExtension f (1, u)).1⁻¹ • (lorentzExtension f (1, u)).2 = u
    rw [hAu]
    simp
  exact exists_fixedPoint_of_kleinClosedBall_fixed f q hu hq

end DifferentialGeometry.Hyperboloid
