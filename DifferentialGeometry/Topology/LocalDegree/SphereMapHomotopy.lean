import DifferentialGeometry.Topology.LocalDegree.SphereMap

set_option autoImplicit false
open Metric Set
open scoped unitInterval
noncomputable section
namespace Poincare.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


def sphereMapHomotopyOfFamily {f g : E → F} {x : E} {R : ℝ}
    (hf : ContinuousOn f (closedBall x R)) (hg : ContinuousOn g (closedBall x R))
    (hfzero : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)
    (hgzero : ∀ y ∈ closedBall x R, y ≠ x → g y ≠ 0) (r : Ioc (0 : ℝ) R)
    (H : I × sphere (0 : E) 1 → F) (hH : Continuous H) (hn : ∀ p, H p ≠ 0)
    (h₀ : ∀ v, H (0, v) = f (x + (r : ℝ) • (v : E)))
    (h₁ : ∀ v, H (1, v) = g (x + (r : ℝ) • (v : E))) :
    (sphereMap f x R hf hfzero r).Homotopy (sphereMap g x R hg hgzero r) where
  toFun p := (homeomorphUnitSphereProd F ⟨H p, hn p⟩).1
  continuous_toFun := (homeomorphUnitSphereProd F).continuous.fst.comp (hH.subtype_mk hn)
  map_zero_left v := by
    apply Subtype.ext
    simp only [homeomorphUnitSphereProd_apply_fst_coe, h₀, sphereMap_apply]
  map_one_left v := by
    apply Subtype.ext
    simp only [homeomorphUnitSphereProd_apply_fst_coe, h₁, sphereMap_apply]


@[simp]
theorem sphereMapHomotopyOfFamily_apply {f g : E → F} {x : E} {R : ℝ}
    (hf : ContinuousOn f (closedBall x R)) (hg : ContinuousOn g (closedBall x R))
    (hfzero : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)
    (hgzero : ∀ y ∈ closedBall x R, y ≠ x → g y ≠ 0) (r : Ioc (0 : ℝ) R)
    (H : I × sphere (0 : E) 1 → F) (hH : Continuous H) (hn : ∀ p, H p ≠ 0)
    (h₀ : ∀ v, H (0, v) = f (x + (r : ℝ) • (v : E)))
    (h₁ : ∀ v, H (1, v) = g (x + (r : ℝ) • (v : E)))
    (t : I) (v : sphere (0 : E) 1) :
    (sphereMapHomotopyOfFamily hf hg hfzero hgzero r H hH hn h₀ h₁ (t, v) : F) =
      ‖H (t, v)‖⁻¹ • H (t, v) :=
  homeomorphUnitSphereProd_apply_fst_coe F _

end Poincare.LocalDegree
