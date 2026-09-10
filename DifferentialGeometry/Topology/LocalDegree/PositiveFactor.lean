import DifferentialGeometry.Topology.LocalDegree.Euclidean

set_option autoImplicit false
open Metric Set
noncomputable section
namespace Poincare.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
theorem IsolatingRadius.pos_smul {f : E → F} {x : E} {R : ℝ}
    (h : IsolatingRadius f x R) {a : E → ℝ}
    (ha : ContinuousOn a (closedBall x R))
    (hpos : ∀ y ∈ closedBall x R, y ≠ x → 0 < a y) :
    IsolatingRadius (fun y => a y • f y) x R where
  pos := h.pos
  continuousOn := ha.smul h.continuousOn
  zero_iff y hy := by
    constructor
    · intro hz
      by_contra hne
      exact h.nonzero y hy hne ((smul_eq_zero.mp hz).resolve_left (ne_of_gt (hpos y hy hne)))
    · intro hyx
      rw [hyx, h.zero, smul_zero]

theorem sphereMap_pos_smul (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (closedBall x R))
    (hz : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0) (a : E → ℝ)
    (ha : ContinuousOn a (closedBall x R))
    (hpos : ∀ y ∈ closedBall x R, y ≠ x → 0 < a y) (r : Ioc (0 : ℝ) R) :
    sphereMap (fun y => a y • f y) x R (ha.smul hf)
        (fun y hy hne => smul_ne_zero (ne_of_gt (hpos y hy hne)) (hz y hy hne)) r =
      sphereMap f x R hf hz r := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  have hnorm : ‖(r : ℝ) • (v : E)‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg r.property.1.le, norm_eq_of_mem_sphere v, mul_one]
  have hmem : x + (r : ℝ) • (v : E) ∈ closedBall x R := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hnorm]
    exact r.property.2
  have hne : x + (r : ℝ) • (v : E) ≠ x := by
    intro he
    have he' : (r : ℝ) • (v : E) = 0 := add_eq_left.mp he
    rw [he', norm_zero] at hnorm
    exact r.property.1.ne hnorm
  have hp := hpos _ hmem hne
  simp only [sphereMap_apply, norm_smul, Real.norm_of_nonneg hp.le,
    mul_inv_rev, smul_smul, mul_assoc, inv_mul_cancel₀ hp.ne', mul_one]

theorem euclideanLocalDegree_pos_smul {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ} (hR : IsolatingRadius f x R)
    {a : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (ha : ContinuousOn a (closedBall x R))
    (hpos : ∀ y ∈ closedBall x R, y ≠ x → 0 < a y) :
    euclideanLocalDegree (fun y => a y • f y) x ⟨R, hR.pos_smul ha hpos⟩ =
      euclideanLocalDegree f x ⟨R, hR⟩ := by
  let r : Ioc (0 : ℝ) R := ⟨R, hR.pos, le_rfl⟩
  erw [euclideanLocalDegree_eq_sphereDegree _ (hR.pos_smul ha hpos) r,
    euclideanLocalDegree_eq_sphereDegree _ hR r]
  rw [sphereMap_pos_smul f x R hR.continuousOn hR.nonzero a ha hpos r]

end Poincare.LocalDegree
