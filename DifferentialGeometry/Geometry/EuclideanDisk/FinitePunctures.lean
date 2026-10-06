import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Finite punctures in the closed disk

Removing finitely many interior points from the closed Euclidean disk leaves a
preconnected set. The disk retraction maps the punctured plane onto this complement,
since every interior point has a singleton fiber under the retraction.
-/

open Set Metric DifferentialGeometry.Topology
open scoped InnerProductSpace

namespace DifferentialGeometry.Geometry

private theorem diskRetraction_eq_of_interior {x : ℂ} {z : closedDisk}
    (hz : ‖(z : ℂ)‖ < 1) (hx : diskRetraction x = z) : x = (z : ℂ) := by
  obtain ⟨t, ht, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hz) ‖x - (z : ℂ)‖
  let y : closedDisk := ⟨(z : ℂ) + t • (x - (z : ℂ)), by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖(z : ℂ) + t • (x - (z : ℂ))‖ ≤ ‖(z : ℂ)‖ + ‖t • (x - (z : ℂ))‖ :=
        norm_add_le _ _
      _ = ‖(z : ℂ)‖ + t * ‖x - (z : ℂ)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ ≤ 1 := by nlinarith [hsmall]⟩
  have h := convexProjection_variational ⟨0, by simp⟩
    isClosed_closedBall.isComplete (convex_closedBall (0 : ℂ) 1) x y
  change ⟪x - (diskRetraction x : ℂ), (y : ℂ) - (diskRetraction x : ℂ)⟫_ℝ ≤ 0 at h
  rw [hx] at h
  change ⟪x - (z : ℂ), (z : ℂ) + t • (x - (z : ℂ)) - (z : ℂ)⟫_ℝ ≤ 0 at h
  rw [add_sub_cancel_left, real_inner_smul_right] at h
  have hinner : ⟪x - (z : ℂ), x - (z : ℂ)⟫_ℝ ≤ 0 := by nlinarith [h]
  exact sub_eq_zero.mp (real_inner_self_nonpos.mp hinner)

/-- Deleting finitely many strict interior points leaves the closed disk preconnected. -/
theorem isPreconnected_closedDisk_compl_of_finite {D : Set closedDisk} (hD : D.Finite)
    (hinterior : ∀ z ∈ D, ‖(z : ℂ)‖ < 1) : IsPreconnected (Dᶜ : Set closedDisk) := by
  let S : Set ℂ := Subtype.val '' D
  have hS : S.Finite := hD.image Subtype.val
  have hplane : IsPreconnected Sᶜ :=
    (hS.countable.isConnected_compl_of_one_lt_rank (by simp)).isPreconnected
  have himage : diskRetraction '' Sᶜ = Dᶜ := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩ hz
      apply hx
      exact ⟨diskRetraction x, hz,
        (diskRetraction_eq_of_interior (hinterior _ hz) rfl).symm⟩
    · intro hz
      refine ⟨(z : ℂ), ?_, diskRetraction_coe z⟩
      rintro ⟨w, hw, heq⟩
      exact hz ((Subtype.ext heq : w = z) ▸ hw)
  rw [← himage]
  exact hplane.image diskRetraction diskRetraction_lipschitz.continuous.continuousOn

end DifferentialGeometry.Geometry
