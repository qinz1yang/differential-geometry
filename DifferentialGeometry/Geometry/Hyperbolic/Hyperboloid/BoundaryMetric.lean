import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Boundary
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import Mathlib.Topology.MetricSpace.Lipschitz

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem dist_boundaryHomeomorph_sq (e : Hyperboloid E ≃ᵢ Hyperboloid F)
    (ξ η : Metric.sphere (0 : E) 1) :
    dist (boundaryHomeomorph e ξ) (boundaryHomeomorph e η) ^ 2 = dist ξ η ^ 2 /
      ((lorentzExtension e (1, (ξ : E))).1 * (lorentzExtension e (1, (η : E))).1) := by
  have hξ := (lorentzExtension_sphere_time_pos e ξ).ne'
  have hη := (lorentzExtension_sphere_time_pos e η).ne'
  have hform := (lorentzExtension e).map_app (1, (ξ : E)) (1, (η : E))
  simp only [lorentzForm_apply, one_mul] at hform
  rw [← real_inner_comm (lorentzExtension e (1, (η : E))).2
    (lorentzExtension e (1, (ξ : E))).2, ← real_inner_comm (η : E) (ξ : E)] at hform
  simp only [Subtype.dist_eq, dist_eq_norm]
  change ‖(boundaryHomeomorph e ξ : F) - (boundaryHomeomorph e η : F)‖ ^ 2 =
    ‖(ξ : E) - (η : E)‖ ^ 2 /
      ((lorentzExtension e (1, (ξ : E))).1 * (lorentzExtension e (1, (η : E))).1)
  rw [norm_sub_sq_real, norm_sub_sq_real]
  simp only [norm_eq_of_mem_sphere, one_pow]
  rw [boundaryHomeomorph_apply_coe, boundaryHomeomorph_apply_coe,
    real_inner_smul_left, real_inner_smul_right]
  field_simp [hξ, hη]
  nlinarith only [hform]

theorem exp_neg_dist_origin_le_boundary_time
    (e : Hyperboloid E ≃ᵢ Hyperboloid F) (ξ : Metric.sphere (0 : E) 1) :
    Real.exp (-dist (origin : Hyperboloid F) (e origin)) ≤
      (lorentzExtension e (1, (ξ : E))).1 := by
  let p : Hyperboloid E := e.symm origin
  have hep : e p = origin := e.apply_symm_apply origin
  have hAp : lorentzExtension e (p.time, p.space) = (1, 0) := by
    rw [lorentzExtension_apply, hep, origin_time, origin_space]
  have hpair := (lorentzExtension e).map_app (1, (ξ : E)) (p.time, p.space)
  rw [hAp] at hpair
  simp only [lorentzForm_apply, inner_zero_left, mul_one, one_mul, zero_sub] at hpair
  have htime : (lorentzExtension e (1, (ξ : E))).1 = p.time - inner ℝ p.space (ξ : E) := by
    linarith
  have hi : inner ℝ p.space (ξ : E) ≤ ‖p.space‖ := by
    simpa only [norm_eq_of_mem_sphere, mul_one] using real_inner_le_norm p.space (ξ : E)
  have hd : dist (origin : Hyperboloid E) p = dist (origin : Hyperboloid F) (e origin) := by
    rw [← e.dist_eq, hep, dist_comm]
  have hexp : p.time - ‖p.space‖ = Real.exp (-dist (origin : Hyperboloid E) p) := by
    rw [← cosh_dist_origin p, ← sinh_dist_origin p]
    simpa only [Real.cosh_neg, Real.sinh_neg, sub_eq_add_neg] using
      Real.cosh_add_sinh (-dist (origin : Hyperboloid E) p)
  calc
    Real.exp (-dist (origin : Hyperboloid F) (e origin)) = p.time - ‖p.space‖ := by
      rw [hexp, hd]
    _ ≤ p.time - inner ℝ p.space (ξ : E) := sub_le_sub_left hi _
    _ = (lorentzExtension e (1, (ξ : E))).1 := htime.symm

theorem lipschitzWith_boundaryHomeomorph (e : Hyperboloid E ≃ᵢ Hyperboloid F) :
    LipschitzWith
      ⟨Real.exp (dist (origin : Hyperboloid F) (e origin)), (Real.exp_pos _).le⟩
      (boundaryHomeomorph e) := by
  apply LipschitzWith.of_dist_le_mul
  intro ξ η
  change dist (boundaryHomeomorph e ξ) (boundaryHomeomorph e η) ≤
    Real.exp (dist (origin : Hyperboloid F) (e origin)) * dist ξ η
  let b := dist (origin : Hyperboloid F) (e origin)
  have hξ := exp_neg_dist_origin_le_boundary_time e ξ
  have hη := exp_neg_dist_origin_le_boundary_time e η
  have hprod : Real.exp (-b) ^ 2 ≤
      (lorentzExtension e (1, (ξ : E))).1 * (lorentzExtension e (1, (η : E))).1 := by
    simpa only [sq] using mul_le_mul hξ hη (Real.exp_pos _).le
      (lorentzExtension_sphere_time_pos e ξ).le
  have hsq : dist (boundaryHomeomorph e ξ) (boundaryHomeomorph e η) ^ 2 ≤
      (Real.exp b * dist ξ η) ^ 2 := by
    calc
      _ = dist ξ η ^ 2 /
          ((lorentzExtension e (1, (ξ : E))).1 * (lorentzExtension e (1, (η : E))).1) :=
        dist_boundaryHomeomorph_sq e ξ η
      _ ≤ dist ξ η ^ 2 / Real.exp (-b) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos (Real.exp_pos _) 2) hprod
      _ = (Real.exp b * dist ξ η) ^ 2 := by
        rw [Real.exp_neg]
        field_simp
  exact (sq_le_sq₀ dist_nonneg (mul_nonneg (Real.exp_pos _).le dist_nonneg)).mp hsq

end DifferentialGeometry.Hyperboloid
