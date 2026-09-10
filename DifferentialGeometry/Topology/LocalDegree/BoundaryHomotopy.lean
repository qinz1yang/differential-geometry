import DifferentialGeometry.Topology.LocalDegree.SphereMapHomotopy
import DifferentialGeometry.Topology.LocalDegree.Euclidean

set_option autoImplicit false
open Metric Set
open scoped unitInterval
noncomputable section
namespace Poincare.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem boundaryPoint_mem {x : E} {R : ℝ} (hR : 0 < R)
    (v : sphere (0 : E) 1) : x + R • (v : E) ∈ sphere x R := by
  rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg hR.le, norm_eq_of_mem_sphere v, mul_one]

def sphereMapHomotopyOfBoundary {f g : E → F} {x : E} {R : ℝ}
    (hf : IsolatingRadius f x R) (hg : IsolatingRadius g x R)
    (H : I × E → F) (hH : ContinuousOn H (univ ×ˢ sphere x R))
    (hn : ∀ t y, y ∈ sphere x R → H (t, y) ≠ 0)
    (h₀ : ∀ y ∈ sphere x R, H (0, y) = f y)
    (h₁ : ∀ y ∈ sphere x R, H (1, y) = g y) :
    (sphereMap f x R hf.continuousOn hf.nonzero ⟨R, hf.pos, le_rfl⟩).Homotopy
      (sphereMap g x R hg.continuousOn hg.nonzero ⟨R, hg.pos, le_rfl⟩) :=
  sphereMapHomotopyOfFamily hf.continuousOn hg.continuousOn hf.nonzero hg.nonzero
    ⟨R, hf.pos, le_rfl⟩ (fun p => H (p.1, x + R • (p.2 : E)))
    (hH.comp_continuous
      (continuous_fst.prodMk
        (continuous_const.add (continuous_const.smul (continuous_subtype_val.comp continuous_snd))))
      (fun p => ⟨mem_univ _, boundaryPoint_mem hf.pos p.2⟩))
    (fun p => hn p.1 _ (boundaryPoint_mem hf.pos p.2))
    (fun v => h₀ _ (boundaryPoint_mem hf.pos v))
    (fun v => h₁ _ (boundaryPoint_mem hf.pos v))


@[simp]
theorem sphereMapHomotopyOfBoundary_apply {f g : E → F} {x : E} {R : ℝ}
    (hf : IsolatingRadius f x R) (hg : IsolatingRadius g x R)
    (H : I × E → F) (hH : ContinuousOn H (univ ×ˢ sphere x R))
    (hn : ∀ t y, y ∈ sphere x R → H (t, y) ≠ 0)
    (h₀ : ∀ y ∈ sphere x R, H (0, y) = f y)
    (h₁ : ∀ y ∈ sphere x R, H (1, y) = g y) (t : I) (v : sphere (0 : E) 1) :
    (sphereMapHomotopyOfBoundary hf hg H hH hn h₀ h₁ (t, v) : F) =
      ‖H (t, x + R • (v : E))‖⁻¹ • H (t, x + R • (v : E)) :=
  sphereMapHomotopyOfFamily_apply _ _ _ _ _ _ _ _ _ _ _ _

theorem euclideanLocalDegree_eq_of_boundaryHomotopy {d : ℕ}
    {f g : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ}
    (hf : IsolatingRadius f x R) (hg : IsolatingRadius g x R)
    (H : I × EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1)))
    (hH : ContinuousOn H (univ ×ˢ sphere x R))
    (hn : ∀ t y, y ∈ sphere x R → H (t, y) ≠ 0)
    (h₀ : ∀ y ∈ sphere x R, H (0, y) = f y)
    (h₁ : ∀ y ∈ sphere x R, H (1, y) = g y) :
    euclideanLocalDegree f x ⟨R, hf⟩ = euclideanLocalDegree g x ⟨R, hg⟩ := by
  erw [euclideanLocalDegree_eq_sphereDegree _ hf ⟨R, hf.pos, le_rfl⟩,
    euclideanLocalDegree_eq_sphereDegree _ hg ⟨R, hg.pos, le_rfl⟩]
  exact euclideanSphereDegree_eq_of_homotopy (sphereMapHomotopyOfBoundary hf hg H hH hn h₀ h₁)

end Poincare.LocalDegree
