import DifferentialGeometry.Topology.Homology.Local.Generator
import DifferentialGeometry.Topology.LocalDegree.Euclidean

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Metric
namespace DifferentialGeometry.LocalDegree
open DifferentialGeometry.Homology
universe u
section Maps
variable {E F : Type u} [PseudoMetricSpace E] [TopologicalSpace F] [Zero F]
  {f : E → F} {x : E} {R : ℝ} (hR : IsolatingRadius f x R)

private def isolatingBallMap : C(ball x R, F) :=
  ⟨fun y => f y, (hR.continuousOn.mono ball_subset_closedBall).domRestrict⟩

private theorem isolatingBallMap_mapsTo :
    MapsTo (isolatingBallMap hR) ({(⟨x,mem_ball_self hR.pos⟩ : ball x R)}ᶜ : Set (ball x R))
      ({0}ᶜ : Set F) := by
  intro y hy
  exact hR.nonzero y (ball_subset_closedBall y.property) (fun he => hy (Subtype.ext he))


def IsolatingRadius.relativeHomologyMap {k : Type u} [Ring k] (A : ModuleCat.{u} k) (n : ℕ) :
    relativeHomology (TopCat.of (ball x R))
      ({(⟨x,mem_ball_self hR.pos⟩ : ball x R)}ᶜ : Set (ball x R)) A n ⟶
    relativeHomology (TopCat.of F) ({0}ᶜ : Set F) A n :=
  DifferentialGeometry.Homology.relativeHomologyMap A (X := TopCat.of (ball x R)) (Y := TopCat.of F)
    (TopCat.ofHom (isolatingBallMap hR)) (isolatingBallMap_mapsTo hR) n


theorem IsolatingRadius.relativeHomologyMap_eq {k : Type u} [Ring k] (A : ModuleCat.{u} k) (n : ℕ) :
    hR.relativeHomologyMap A n =
      DifferentialGeometry.Homology.relativeHomologyMap A (X := TopCat.of (ball x R)) (Y := TopCat.of F)
        (s := ({(⟨x,mem_ball_self hR.pos⟩ : ball x R)}ᶜ : Set (ball x R))) (t := ({0}ᶜ : Set F))
        (TopCat.ofHom (⟨fun y => f y,
          (hR.continuousOn.mono ball_subset_closedBall).domRestrict⟩ : C(ball x R,F)))
        (fun y hy => hR.nonzero y (ball_subset_closedBall y.property)
          (fun he => hy (Subtype.ext he))) n := rfl
end Maps

variable {d : ℕ}
  {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
  {x : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ} (hR : IsolatingRadius f x R)

private def isolatingBallSphereSection (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    C(EuclideanSphere d,
      ({(⟨x,mem_ball_self hR.pos⟩ : ball x R)}ᶜ : Set (ball x R))) :=
  puncturedNeighborhoodSphereSection _ x (ball x R) (mem_ball_self hR.pos) hr
    (fun _ hy => (mem_sphere.mp hy).trans_lt hrR)

private theorem isolatingBallSphereMap_eq (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    (puncturedSpaceSphereHomotopyEquiv (EuclideanSpace ℝ (Fin (d + 1)))).toFun.comp
      ((relativeSubspaceMap (X := TopCat.of (ball x R))
        (Y := TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
        (TopCat.ofHom (isolatingBallMap hR)) (isolatingBallMap_mapsTo hR)).hom.comp
        (isolatingBallSphereSection hR r hr hrR)) =
      sphereMap f x R hR.continuousOn hR.nonzero ⟨r,hr,hrR.le⟩ := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  rw [sphereMap_apply]
  exact puncturedSpaceSphereHomotopyEquiv_apply _ _

private theorem homologyMap_sphere_comparison (r : ℝ) (hr : 0 < r) (hrR : r < R) :
    (localBallSphereHomologyIso _ x R hR.pos (ModuleCat.of ℤ ℤ) d).inv ≫ hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1) ≫
      (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom =
    reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (sphereMap f x R hR.continuousOn hR.nonzero ⟨r,hr,hrR.le⟩)) d := by
  let _ : ContractibleSpace (ball x R) := (convex_ball x R).contractibleSpace ⟨x,mem_ball_self hR.pos⟩
  dsimp only [localBallSphereHomologyIso, Iso.trans_inv,
    localEuclideanSphereHomologyIso, Iso.trans_hom]
  simp only [Category.assoc]
  have hS := puncturedNeighborhoodSphereHomologyIso_inv
    (EuclideanSpace ℝ (Fin (d + 1))) x (ball x R) (mem_ball_self hR.pos) isOpen_ball
    (ModuleCat.of ℤ ℤ) hr (fun y hy => (mem_sphere.mp hy).trans_lt hrR) d
  rw [hS]
  change reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
    (TopCat.ofHom (isolatingBallSphereSection hR r hr hrR)) d ≫ _ = _
  have hn := relativeReducedConnectingIso_naturality (ModuleCat.of ℤ ℤ)
    (X := TopCat.of (ball x R)) (Y := TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
    (TopCat.ofHom (isolatingBallMap hR)) (isolatingBallMap_mapsTo hR) d
  change _ = hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1) ≫ _ at hn
  rw [← Category.assoc (hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1)), ← hn, Category.assoc,
    Iso.inv_hom_id_assoc, reducedSingularHomologyIso_hom,
    ← reducedSingularHomologyMap_comp, ← reducedSingularHomologyMap_comp]
  exact congrArg (fun g => reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
    (TopCat.ofHom g) d) (isolatingBallSphereMap_eq hR r hr hrR)


theorem euclideanLocalDegree_relativeHomology :
    hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1) (euclideanBallLocalGenerator x R hR.pos) =
      euclideanLocalDegree f x ⟨R,hR⟩ • euclideanLocalGenerator d := by
  apply (ModuleCat.mono_iff_injective
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom).mp inferInstance
  have he := congrArg (fun g => g (euclideanSphereTopGenerator d))
    (homologyMap_sphere_comparison hR (R/2) (half_pos hR.pos) (by linarith [hR.pos]))
  change (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
    (hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1) (euclideanBallLocalGenerator x R hR.pos)) = _ at he
  rw [he, euclideanLocalDegree_generator ⟨R,hR⟩ hR ⟨R/2,half_pos hR.pos,(by linarith [hR.pos])⟩]
  rw [map_zsmul]
  congr 1
  exact (congrArg (fun g => g (euclideanSphereTopGenerator d))
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).inv_hom_id).symm
end DifferentialGeometry.LocalDegree
