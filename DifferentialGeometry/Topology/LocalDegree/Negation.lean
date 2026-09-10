import DifferentialGeometry.Topology.LocalDegree.SphereAntipodal
import DifferentialGeometry.Topology.LocalDegree.Euclidean

set_option autoImplicit false
open Metric Set
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem IsolatingRadius.neg {f : E → F} {x : E} {R : ℝ} (h : IsolatingRadius f x R) :
    IsolatingRadius (fun y => -f y) x R where
  pos := h.pos
  continuousOn := h.continuousOn.neg
  zero_iff y hy := neg_eq_zero.trans (h.zero_iff y hy)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem isolatedZero_neg {f : E → F} {x : E} (h : isolatedZero f x) :
    isolatedZero (fun y => -f y) x := ⟨h.choose, h.choose_spec.neg⟩

theorem sphereMap_neg (f : E → F) (x : E) (R : ℝ)
    (hf : ContinuousOn f (closedBall x R))
    (hz : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0) (r : Ioc (0 : ℝ) R) :
    sphereMap (fun y => -f y) x R hf.neg (fun y hy hne => neg_ne_zero.mpr (hz y hy hne)) r =
      (unitSphereAntipodal F).comp (sphereMap f x R hf hz r) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  simp only [sphereMap_apply, norm_neg, smul_neg, ContinuousMap.comp_apply,
    unitSphereAntipodal_apply]
  change -(‖f (x + (r : ℝ) • (v : E))‖⁻¹ • f (x + (r : ℝ) • (v : E))) =
    -(sphereMap f x R hf hz r v : F)
  rw [sphereMap_apply]

theorem euclideanLocalDegree_neg {d : ℕ}
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} (h : isolatedZero f x) :
    euclideanLocalDegree (fun y => -f y) x (isolatedZero_neg h) =
      (-1 : ℤ) ^ (d + 1) * euclideanLocalDegree f x h := by
  have hR := h.choose_spec
  let r : Ioc (0 : ℝ) h.choose := ⟨h.choose, hR.pos, le_rfl⟩
  erw [euclideanLocalDegree_eq_sphereDegree _ hR.neg r,
    euclideanLocalDegree_eq_sphereDegree _ hR r]
  rw [sphereMap_neg, euclideanSphereDegree_comp, euclideanSphereDegree_antipodal]

end DifferentialGeometry.LocalDegree
