import DifferentialGeometry.Topology.Manifold.NearestNormalProjector
import DifferentialGeometry.Topology.Manifold.LocalExtrema
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Actual nearest-point residuals are orthogonal to the target embedding tangent range. -/

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Manifold Topology
namespace GC.MetricGeometry

theorem nearestPoint_residual_mem_actual_normal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {k : ℕ} {Z : Set H}
    [ChartedSpace (Fin k → ℝ) Z]
    (hemb : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
      (Subtype.val : Z → H)) (o : H) (y : Z)
    (hmin : IsMinOn (fun w => dist o w) Z (y : H)) :
    o - (y : H) ∈ (actualZeroSetTangentSpace k Z y)ᗮ := by
  let f : H → ℝ := fun w => ‖w - o‖ ^ 2
  have hlocal : IsLocalMin (fun w : Z => f w) y := by
    filter_upwards [] with w
    have hdist := hmin w.property
    change ‖(y : H) - o‖ ^ 2 ≤ ‖(w : H) - o‖ ^ 2
    rw [← dist_eq_norm, ← dist_eq_norm]
    rw [dist_comm (y : H) o, dist_comm (w : H) o]
    exact pow_le_pow_left₀ dist_nonneg hdist 2
  have hzero := hlocal.mvfderiv_eq_zero
    (BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, Fin k → ℝ)))
  have hd : HasFDerivAt f (2 • innerSL ℝ ((y : H) - o)) (y : H) := by
    simpa only [f, id_eq, ContinuousLinearMap.comp_id] using
      ((hasFDerivAt_id (y : H)).sub_const o).norm_sq
  have hchain := mvfderiv_comp y hd.differentiableAt.mdifferentiableAt
    (hemb.contMDiff.mdifferentiableAt (by simp))
  rw [mvfderiv_eq_fderiv, hd.fderiv] at hchain
  let A : (Fin k → ℝ) →L[ℝ] H :=
    mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : Z → H) y
  change mvfderiv 𝓘(ℝ, Fin k → ℝ) (f ∘ (Subtype.val : Z → H)) y =
    (2 • innerSL ℝ ((y : H) - o)).comp A at hchain
  change o - (y : H) ∈ (LinearMap.range A.toLinearMap)ᗮ
  rw [Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨v, rfl⟩ := hu
  have hval := congrArg (fun B : (Fin k → ℝ) →L[ℝ] ℝ => B v) (hchain.symm.trans hzero)
  have hval' : (2 : ℝ) * inner ℝ ((y : H) - o) (A v) = 0 := by
    convert hval using 1
    simp [ContinuousLinearMap.comp_apply, innerSL_apply_apply, two_smul, two_mul, inner_sub_left]
  have hinner : inner ℝ ((y : H) - o) (A v) = 0 := by linarith
  change inner ℝ (o - (y : H)) (A v) = 0
  have hneg : o - (y : H) = -((y : H) - o) := by abel
  rw [hneg, inner_neg_left, hinner, neg_zero]

theorem nearestMap_residual_mem_actual_normal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {k : ℕ} {Z : Set H}
    [ChartedSpace (Fin k → ℝ) Z] (Ω : TopologicalSpace.Opens H)
    (p : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin k → ℝ), Z⟯)
    (hemb : _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
      (Subtype.val : Z → H))
    (hnearest : ∀ z : Ω, IsMinOn (fun y => dist (z : H) y) Z (p z : H))
    (z : Ω) : (z : H) - (p z : H) ∈ (actualZeroSetTangentSpace k Z (p z))ᗮ :=
  nearestPoint_residual_mem_actual_normal hemb z (p z) (hnearest z)

end GC.MetricGeometry
