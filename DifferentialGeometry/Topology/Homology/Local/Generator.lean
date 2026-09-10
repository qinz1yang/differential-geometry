import DifferentialGeometry.Topology.Homology.Local.NeighborhoodSphere
import DifferentialGeometry.Topology.Homology.Local.Graded

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Metric DifferentialGeometry.LocalDegree
namespace DifferentialGeometry.Homology
universe u
variable {d : ℕ}


def localBallSphereHomologyIso (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (r : ℝ) (hr : 0 < r) {k : Type u} [Ring k] (R : ModuleCat.{u} k) (n : ℕ) :
    relativeHomology (TopCat.of (ball x r))
      ({(⟨x,mem_ball_self hr⟩ : ball x r)}ᶜ : Set (ball x r)) R (n + 1) ≅
    reducedSingularHomology R (TopCat.of (sphere (0 : E) 1)) n := by
  let _ : ContractibleSpace (ball x r) := (convex_ball x r).contractibleSpace ⟨x,mem_ball_self hr⟩
  exact relativeReducedConnectingIso _ _ R n ≪≫
    puncturedNeighborhoodSphereHomologyIso E x (ball x r) (mem_ball_self hr) isOpen_ball R n


def euclideanBallLocalGenerator (x : EuclideanSpace ℝ (Fin (d + 1))) (R : ℝ) (hR : 0 < R) :
    relativeHomology (TopCat.of (ball x R))
      ({(⟨x,mem_ball_self hR⟩ : ball x R)}ᶜ : Set (ball x R)) (ModuleCat.of ℤ ℤ) (d + 1) :=
  (localBallSphereHomologyIso _ x R hR (ModuleCat.of ℤ ℤ) d).inv (euclideanSphereTopGenerator d)


def euclideanLocalGenerator (d : ℕ) :
    relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1)))) (ModuleCat.of ℤ ℤ) (d + 1) :=
  (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).inv (euclideanSphereTopGenerator d)


theorem euclideanLocalGenerator_ne_zero (d : ℕ) : euclideanLocalGenerator d ≠ 0 := by
  intro h
  have hh := congrArg (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom h
  have he := congrArg (fun g => g (euclideanSphereTopGenerator d))
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).inv_hom_id
  exact euclideanSphereTopGenerator_ne_zero d (he.symm.trans (hh.trans (map_zero _)))


theorem euclideanBallLocalGenerator_ne_zero (x : EuclideanSpace ℝ (Fin (d + 1)))
    (r : ℝ) (hr : 0 < r) : euclideanBallLocalGenerator x r hr ≠ 0 := by
  intro h
  have hh := congrArg (localBallSphereHomologyIso _ x r hr (ModuleCat.of ℤ ℤ) d).hom h
  have he := congrArg (fun g => g (euclideanSphereTopGenerator d))
    (localBallSphereHomologyIso _ x r hr (ModuleCat.of ℤ ℤ) d).inv_hom_id
  exact euclideanSphereTopGenerator_ne_zero d (he.symm.trans (hh.trans (map_zero _)))

end DifferentialGeometry.Homology
