import DifferentialGeometry.Topology.LocalDegree.FiniteAdditivity
import DifferentialGeometry.Topology.LocalDegree.BallBoundaryHomotopy

set_option autoImplicit false
noncomputable section
open CategoryTheory Set Metric
open scoped unitInterval
namespace Poincare.LocalDegree
variable {d : ℕ} {a : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ} (hr : 0 < r)
  {f g : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
  (hf : ContinuousOn f (closedBall a r)) (hg : ContinuousOn g (closedBall a r))
  (hfinitef : {x ∈ closedBall a r | f x = 0}.Finite)
  (hfiniteg : {x ∈ closedBall a r | g x = 0}.Finite)
  (hbf : ∀ x ∈ sphere a r, f x ≠ 0) (hbg : ∀ x ∈ sphere a r, g x ≠ 0)
include hr


theorem finsum_localDegrees_eq_of_boundaryHomotopy
    (H : C(I × sphere a r, EuclideanSpace ℝ (Fin (d + 1)))) (hH : ∀ q, H q ≠ 0)
    (h₀ : ∀ x : sphere a r, H (0,x) = f x.val)
    (h₁ : ∀ x : sphere a r, H (1,x) = g x.val) :
    (∑ᶠ p : {x ∈ closedBall a r | f x = 0}, euclideanLocalDegree f p.val
      (isolatedZero_of_finite_closedBall_zeroSet hf hfinitef hbf p.property.1 p.property.2)) =
    ∑ᶠ p : {x ∈ closedBall a r | g x = 0}, euclideanLocalDegree g p.val
      (isolatedZero_of_finite_closedBall_zeroSet hg hfiniteg hbg p.property.1 p.property.2) := by
  rw [← euclideanBallDegree_eq_finsum_localDegrees hr hf hfinitef hbf,
    ← euclideanBallDegree_eq_finsum_localDegrees hr hg hfiniteg hbg]
  exact euclideanBallDegree_eq_of_boundaryHomotopy hr
    (f := (⟨fun y => f y.val,hf.domRestrict⟩ : C(closedBall a r,EuclideanSpace ℝ (Fin (d + 1)))))
    (g := (⟨fun y => g y.val,hg.domRestrict⟩ : C(closedBall a r,EuclideanSpace ℝ (Fin (d + 1)))))
    (fun y hy => hbf y.val hy) (fun y hy => hbg y.val hy) H hH h₀ h₁


theorem finsum_localDegrees_eq_of_eqOn_sphere (hfg : EqOn f g (sphere a r)) :
    (∑ᶠ p : {x ∈ closedBall a r | f x = 0}, euclideanLocalDegree f p.val
      (isolatedZero_of_finite_closedBall_zeroSet hf hfinitef hbf p.property.1 p.property.2)) =
    ∑ᶠ p : {x ∈ closedBall a r | g x = 0}, euclideanLocalDegree g p.val
      (isolatedZero_of_finite_closedBall_zeroSet hg hfiniteg hbg p.property.1 p.property.2) := by
  let H : C(I × sphere a r, EuclideanSpace ℝ (Fin (d + 1))) :=
    ⟨fun q => f q.2.val,hf.comp_continuous (continuous_subtype_val.comp continuous_snd)
      (fun q => sphere_subset_closedBall q.2.property)⟩
  exact finsum_localDegrees_eq_of_boundaryHomotopy hr hf hg hfinitef hfiniteg hbf hbg H
    (fun q => hbf _ q.2.property) (fun _ => rfl) (fun x => hfg x.property)
end Poincare.LocalDegree
