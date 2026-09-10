import DifferentialGeometry.Topology.Homology.Local.ClosedBall
import DifferentialGeometry.Topology.Homology.Relative.ContractibleHomotopy
import DifferentialGeometry.Topology.Homology.Relative.MapZero

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Metric
open scoped unitInterval
namespace Poincare.LocalDegree
open Poincare.Homology
universe u
section Maps
variable {E F : Type u} [PseudoMetricSpace E] [TopologicalSpace F] [Zero F]
  {a : E} {r : ℝ} {k : Type u} [Ring k] (A : ModuleCat.{u} k)


def closedBallRelativeHomologyMap (f : C(closedBall a r, F))
    (hb : ∀ y : closedBall a r, y.val ∈ sphere a r → f y ≠ 0) (n : ℕ) :
    relativeHomology (TopCat.of (closedBall a r)) {y : closedBall a r | y.val ∈ sphere a r} A n ⟶
      relativeHomology (TopCat.of F) ({0}ᶜ : Set F) A n :=
  Poincare.Homology.relativeHomologyMap A (X := TopCat.of (closedBall a r)) (Y := TopCat.of F)
    (s := {y : closedBall a r | y.val ∈ sphere a r}) (t := ({0}ᶜ : Set F)) (TopCat.ofHom f) hb n
end Maps

section Homotopy
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace F] [Zero F] [ContractibleSpace F]
  {a : E} {r : ℝ} (hr : 0 < r) {k : Type u} [Ring k] (A : ModuleCat.{u} k)
  {f g : C(closedBall a r, F)}
  (hf : ∀ y : closedBall a r, y.val ∈ sphere a r → f y ≠ 0)
  (hg : ∀ y : closedBall a r, y.val ∈ sphere a r → g y ≠ 0)

include hr in
theorem closedBallRelativeHomologyMap_eq_of_homotopy (H : f.Homotopy g)
    (hH : ∀ t : I, ∀ y : closedBall a r, y.val ∈ sphere a r → H (t,y) ≠ 0) (n : ℕ) :
    closedBallRelativeHomologyMap A f hf (n + 1) = closedBallRelativeHomologyMap A g hg (n + 1) := by
  let _ : ContractibleSpace (closedBall a r) :=
    (convex_closedBall a r).contractibleSpace ⟨a,mem_closedBall_self hr.le⟩
  exact relativeHomologyMap_eq_of_homotopy_of_contractible (X := TopCat.of (closedBall a r))
    (Y := TopCat.of F) (f := TopCat.ofHom f) (g := TopCat.ofHom g)
    (s := {y : closedBall a r | y.val ∈ sphere a r}) (t := ({0}ᶜ : Set F)) hf hg A H hH n
end Homotopy

section Degree
variable {d : ℕ} {a : EuclideanSpace ℝ (Fin (d + 1))} {r : ℝ}
  (hr : 0 < r) (f : C(closedBall a r, EuclideanSpace ℝ (Fin (d + 1))))
  (hb : ∀ y : closedBall a r, y.val ∈ sphere a r → f y ≠ 0)


def euclideanBallDegree : ℤ :=
  euclideanSphereTopReducedHomologyEquiv d
    ((localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
      (closedBallRelativeHomologyMap (ModuleCat.of ℤ ℤ) f hb (d + 1)
        (euclideanClosedBallFundamentalClass a r hr)))


theorem euclideanBallDegree_relativeHomology :
    closedBallRelativeHomologyMap (ModuleCat.of ℤ ℤ) f hb (d + 1)
      (euclideanClosedBallFundamentalClass a r hr) =
        euclideanBallDegree hr f hb • euclideanLocalGenerator d := by
  apply (ModuleCat.mono_iff_injective
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom).mp inferInstance
  rw [map_zsmul]
  have he := congrArg (fun g => g (euclideanSphereTopGenerator d))
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).inv_hom_id
  change (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
    (euclideanLocalGenerator d) = euclideanSphereTopGenerator d at he
  rw [he]
  exact (euclideanSphereTopReducedHomologyEquiv_smul_generator d _).symm


theorem euclideanBallDegree_eq_iff (m : ℤ) :
    euclideanBallDegree hr f hb = m ↔
      closedBallRelativeHomologyMap (ModuleCat.of ℤ ℤ) f hb (d + 1)
        (euclideanClosedBallFundamentalClass a r hr) = m • euclideanLocalGenerator d := by
  constructor
  · intro hm
    rw [← hm]
    exact euclideanBallDegree_relativeHomology hr f hb
  · intro hm
    unfold euclideanBallDegree
    rw [hm,map_zsmul]
    have he := congrArg (fun g => g (euclideanSphereTopGenerator d))
      (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).inv_hom_id
    change (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
      (euclideanLocalGenerator d) = euclideanSphereTopGenerator d at he
    rw [he,map_zsmul,euclideanSphereTopReducedHomologyEquiv_generator,smul_eq_mul,mul_one]


theorem euclideanBallDegree_eq_zero_of_nonzero (hf : ∀ x, f x ≠ 0) :
    euclideanBallDegree hr f hb = 0 := by
  have hz : closedBallRelativeHomologyMap (ModuleCat.of ℤ ℤ) f hb (d + 1) = 0 := by
    apply relativeHomologyMap_eq_zero_of_range_subset
    rintro y ⟨x,rfl⟩
    exact hf x
  unfold euclideanBallDegree
  rw [hz]
  change euclideanSphereTopReducedHomologyEquiv d
    ((localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom 0) = 0
  rw [map_zero,map_zero]


theorem euclideanBallDegree_eq_of_homotopy
    {g : C(closedBall a r, EuclideanSpace ℝ (Fin (d + 1)))}
    (hg : ∀ y : closedBall a r, y.val ∈ sphere a r → g y ≠ 0)
    (H : f.Homotopy g)
    (hH : ∀ t : I, ∀ y : closedBall a r, y.val ∈ sphere a r → H (t,y) ≠ 0) :
    euclideanBallDegree hr f hb = euclideanBallDegree hr g hg := by
  unfold euclideanBallDegree
  rw [closedBallRelativeHomologyMap_eq_of_homotopy hr (ModuleCat.of ℤ ℤ) hb hg H hH]
end Degree
end Poincare.LocalDegree
