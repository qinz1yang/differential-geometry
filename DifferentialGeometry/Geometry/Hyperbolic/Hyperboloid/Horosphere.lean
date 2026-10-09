import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Busemann

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem time_sub_inner_boundaryHomeomorph (f : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E) :
    (f x).time - inner ℝ (f x).space (boundaryHomeomorph f ξ : F) =
      (x.time - inner ℝ x.space (ξ : E)) / (lorentzExtension f (1, (ξ : E))).1 := by
  have h := (lorentzExtension f).map_app (x.time, x.space) (1, (ξ : E))
  rw [lorentzExtension_apply] at h
  change inner ℝ (lorentzExtension f (1, (ξ : E))).2 (f x).space -
    (lorentzExtension f (1, (ξ : E))).1 * (f x).time = inner ℝ (ξ : E) x.space - 1 * x.time at h
  rw [one_mul] at h
  rw [show inner ℝ (lorentzExtension f (1, (ξ : E))).2 (f x).space =
    inner ℝ (f x).space (lorentzExtension f (1, (ξ : E))).2 from real_inner_comm _ _,
    show inner ℝ (ξ : E) x.space = inner ℝ x.space (ξ : E) from real_inner_comm _ _] at h
  rw [boundaryHomeomorph_apply_coe, real_inner_smul_right]
  have ha := (lorentzExtension_sphere_time_pos f ξ).ne'
  field_simp
  nlinarith only [h]

theorem time_sub_inner_eq_of_boundary_fixed_of_small_displacement
    (f : Hyperboloid E ≃ᵢ Hyperboloid E) (ξ : Metric.sphere (0 : E) 1)
    (hξ : boundaryHomeomorph f ξ = ξ)
    (hsmall : ∀ ε > (0 : ℝ), ∃ x : Hyperboloid E, dist x (f x) < ε)
    (x : Hyperboloid E) :
    (f x).time - inner ℝ (f x).space (ξ : E) = x.time - inner ℝ x.space (ξ : E) := by
  have hz : |Real.log ((lorentzExtension f (1, (ξ : E))).1)| = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := hsmall _ (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne))
    exact (not_lt_of_ge (abs_log_lorentzExtension_time_le_dist_of_boundary_fixed f ξ hξ y)) hy
  have ha : (lorentzExtension f (1, (ξ : E))).1 = 1 := by
    have he := congrArg Real.exp (abs_eq_zero.mp hz)
    rwa [Real.exp_log (lorentzExtension_sphere_time_pos f ξ), Real.exp_zero] at he
  have h := time_sub_inner_boundaryHomeomorph f ξ x
  rwa [hξ, ha, div_one] at h

end DifferentialGeometry.Hyperboloid
