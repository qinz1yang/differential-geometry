import DifferentialGeometry.Topology.LocalDegree.ClosedBall

set_option autoImplicit false
noncomputable section
open CategoryTheory Set Metric
open scoped unitInterval
namespace Poincare.LocalDegree
open Poincare.Homology
universe u
section Maps
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace F] [Zero F] [ContractibleSpace F]
  {a : E} {r : ℝ} (hr : 0 < r) {k : Type u} [Ring k] (A : ModuleCat.{u} k)
  {f g : C(closedBall a r, F)}
  (hf : ∀ y : closedBall a r, y.val ∈ sphere a r → f y ≠ 0)
  (hg : ∀ y : closedBall a r, y.val ∈ sphere a r → g y ≠ 0)

include hr in
theorem closedBallRelativeHomologyMap_eq_of_boundaryHomotopy
    (H : C(I × sphere a r, F)) (hH : ∀ q, H q ≠ 0)
    (h₀ : ∀ x : sphere a r, H (0,x) = f ⟨x.val,sphere_subset_closedBall x.property⟩)
    (h₁ : ∀ x : sphere a r, H (1,x) = g ⟨x.val,sphere_subset_closedBall x.property⟩) (n : ℕ) :
    closedBallRelativeHomologyMap A f hf (n + 1) = closedBallRelativeHomologyMap A g hg (n + 1) := by
  let _ : ContractibleSpace (closedBall a r) :=
    (convex_closedBall a r).contractibleSpace ⟨a,mem_closedBall_self hr.le⟩
  let K : TopCat.Homotopy
      (relativeSubspaceMap (X := TopCat.of (closedBall a r)) (Y := TopCat.of F)
        (s := {y : closedBall a r | y.val ∈ sphere a r}) (t := ({0}ᶜ : Set F)) (TopCat.ofHom f) hf)
      (relativeSubspaceMap (X := TopCat.of (closedBall a r)) (Y := TopCat.of F)
        (s := {y : closedBall a r | y.val ∈ sphere a r}) (t := ({0}ᶜ : Set F)) (TopCat.ofHom g) hg) := {
    toFun := fun q => ⟨H (q.1,⟨q.2.val.val,q.2.property⟩),hH _⟩
    continuous_toFun := by fun_prop
    map_zero_left := fun x => Subtype.ext (h₀ ⟨x.val.val,x.property⟩)
    map_one_left := fun x => Subtype.ext (h₁ ⟨x.val.val,x.property⟩) }
  exact relativeHomologyMap_eq_of_subspace_homotopy (X := TopCat.of (closedBall a r))
    (Y := TopCat.of F) (f := TopCat.ofHom f) (g := TopCat.ofHom g)
    (s := {y : closedBall a r | y.val ∈ sphere a r}) (t := ({0}ᶜ : Set F)) hf hg A K n
end Maps

section Degree
variable {d : ℕ} {a : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
  (hr : 0 < r) {f g : C(closedBall a r, EuclideanSpace ℝ (Fin (d + 1)))}
  (hf : ∀ y : closedBall a r, y.val ∈ sphere a r → f y ≠ 0)
  (hg : ∀ y : closedBall a r, y.val ∈ sphere a r → g y ≠ 0)


theorem euclideanBallDegree_eq_of_boundaryHomotopy
    (H : C(I × sphere a r, EuclideanSpace ℝ (Fin (d + 1)))) (hH : ∀ q, H q ≠ 0)
    (h₀ : ∀ x : sphere a r, H (0,x) = f ⟨x.val,sphere_subset_closedBall x.property⟩)
    (h₁ : ∀ x : sphere a r, H (1,x) = g ⟨x.val,sphere_subset_closedBall x.property⟩) :
    euclideanBallDegree hr f hf = euclideanBallDegree hr g hg := by
  unfold euclideanBallDegree
  rw [closedBallRelativeHomologyMap_eq_of_boundaryHomotopy hr (ModuleCat.of ℤ ℤ) hf hg H hH h₀ h₁]


theorem euclideanBallDegree_eq_of_eqOn_boundary
    (hfg : ∀ y : closedBall a r, y.val ∈ sphere a r → f y = g y) :
    euclideanBallDegree hr f hf = euclideanBallDegree hr g hg := by
  let H : C(I × sphere a r, EuclideanSpace ℝ (Fin (d + 1))) :=
    ⟨fun q => f ⟨q.2.val,sphere_subset_closedBall q.2.property⟩,by fun_prop⟩
  exact euclideanBallDegree_eq_of_boundaryHomotopy hr hf hg H
    (fun q => hf _ q.2.property) (fun _ => rfl) (fun x => hfg _ x.property)
end Degree
end Poincare.LocalDegree
