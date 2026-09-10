import DifferentialGeometry.Analysis.Calculus.Cutoff.BallRadialFunction
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section
open Set Metric Manifold Module
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ellipsoidRadialFunction (A : E ≃L[ℝ] E) (r : ℝ) (u : sphere (0 : E) 1) : ℝ :=
  r / ‖A.symm (u : E)‖

private theorem norm_symm_unit_pos (A : E ≃L[ℝ] E) (u : sphere (0 : E) 1) :
    0 < ‖A.symm (u : E)‖ := by
  apply norm_pos_iff.mpr
  intro h
  apply ne_zero_of_mem_unit_sphere u
  simpa only [A.apply_symm_apply, map_zero] using congrArg A h

theorem ellipsoidRadialFunction_pos (A : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (u : sphere (0 : E) 1) : 0 < ellipsoidRadialFunction A r u :=
  div_pos hr (norm_symm_unit_pos A u)

theorem contMDiff_ellipsoidRadialFunction {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (A : E ≃L[ℝ] E) (r : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (ellipsoidRadialFunction A r) := by
  have hA : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (fun u : sphere (0 : E) 1 ↦ A.symm (u : E)) :=
    A.symm.contDiff.contMDiff.comp contMDiff_coe_sphere
  have hn : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ (fun u : sphere (0 : E) 1 ↦ ‖A.symm (u : E)‖) := by
    intro u
    exact (contDiffAt_norm ℝ (norm_ne_zero_iff.mp (norm_symm_unit_pos A u).ne')).contMDiffAt.comp u
      (hA u)
  have hm := (contMDiff_const (c := r)).mul (hn.inv₀ (fun u ↦ (norm_symm_unit_pos A u).ne'))
  apply hm.congr
  intro u
  exact (div_eq_mul_inv r _).symm

theorem image_closedBall_affine_eq (A : E ≃L[ℝ] E) (p : E) (r : ℝ) :
    (fun x ↦ A x + p) '' closedBall 0 r = {y | ‖A.symm (y - p)‖ ≤ r} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_ofPred_eq, add_sub_cancel_right, A.symm_apply_apply] using mem_closedBall_zero_iff.mp hx
  · intro hy
    refine ⟨A.symm (y - p), mem_closedBall_zero_iff.mpr hy, ?_⟩
    change A (A.symm (y - p)) + p = y
    rw [A.apply_symm_apply, sub_add_cancel]

theorem image_ball_affine_eq (A : E ≃L[ℝ] E) (p : E) (r : ℝ) :
    (fun x ↦ A x + p) '' ball 0 r = {y | ‖A.symm (y - p)‖ < r} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_ofPred_eq, add_sub_cancel_right, A.symm_apply_apply] using mem_ball_zero_iff.mp hx
  · intro hy
    refine ⟨A.symm (y - p), mem_ball_zero_iff.mpr hy, ?_⟩
    change A (A.symm (y - p)) + p = y
    rw [A.apply_symm_apply, sub_add_cancel]

theorem smul_add_mem_closedEllipsoid_iff (A : E ≃L[ℝ] E) (p : E) (r : ℝ)
    (u : sphere (0 : E) 1) {t : ℝ} (ht : 0 ≤ t) :
    t • (u : E) + p ∈ (fun x ↦ A x + p) '' closedBall 0 r ↔
      t ≤ ellipsoidRadialFunction A r u := by
  rw [image_closedBall_affine_eq]
  change ‖A.symm (t • (u : E) + p - p)‖ ≤ r ↔ _
  rw [add_sub_cancel_right, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact (le_div_iff₀ (norm_symm_unit_pos A u)).symm

theorem smul_add_mem_openEllipsoid_iff (A : E ≃L[ℝ] E) (p : E) (r : ℝ)
    (u : sphere (0 : E) 1) {t : ℝ} (ht : 0 ≤ t) :
    t • (u : E) + p ∈ (fun x ↦ A x + p) '' ball 0 r ↔
      t < ellipsoidRadialFunction A r u := by
  rw [image_ball_affine_eq]
  change ‖A.symm (t • (u : E) + p - p)‖ < r ↔ _
  rw [add_sub_cancel_right, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact (lt_div_iff₀ (norm_symm_unit_pos A u)).symm

theorem ellipsoidRadialFunction_lt_ballRadialFunction
    (A : E ≃L[ℝ] E) (p : E) {r R : ℝ} (hr : 0 < r) (hp : ‖p‖ < R)
    (hsub : (fun x ↦ A x + p) '' closedBall 0 r ⊆ ball 0 R)
    (u : sphere (0 : E) 1) :
    ellipsoidRadialFunction A r u < Poincare.Analysis.ballRadialFunction p R (u : E) := by
  have ha := ellipsoidRadialFunction_pos A hr u
  have hi := (smul_add_mem_closedEllipsoid_iff A p r u ha.le).mpr le_rfl
  exact (Poincare.Analysis.smul_add_mem_ball_iff hp (norm_eq_of_mem_sphere u) ha.le).mp (hsub hi)

end Poincare.Topology.Manifold
