import DifferentialGeometry.Topology.Homology.Reduced.MayerVietoris
import DifferentialGeometry.Topology.LocalDegree.SphereCover

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open scoped Topology
noncomputable section
universe u
namespace DifferentialGeometry.LocalDegree
open DifferentialGeometry.Homology
variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (v : Metric.sphere (0 : E) 1)

private theorem poleComplement_cover : ∀ x : Metric.sphere (0 : E) 1,
    x ∈ (poleComplement v : Set (Metric.sphere (0 : E) 1)) ∨ x ∈ (poleComplement (-v) : Set (Metric.sphere (0 : E) 1)) := by
  intro x
  have h : x ∈ (poleComplement v ⊔ poleComplement (-v)) := by
    rw [poleComplement_sup]
    trivial
  exact h

def sphereEquatorReducedHomologyIso (n : ℕ) :
    reducedSingularHomology R (TopCat.of (Metric.sphere (0 : E) 1)) (n + 1) ≅
      reducedSingularHomology R (TopCat.of (EquatorialSphere v)) n := by
  have hs := contractibleSpace_poleComplement v
  have ht := contractibleSpace_poleComplement (-v)
  exact reducedMayerVietorisConnectingIso R (TopCat.of (Metric.sphere (0 : E) 1))
      (poleComplement v : Set (Metric.sphere (0 : E) 1)) (poleComplement (-v) : Set (Metric.sphere (0 : E) 1))
      (poleComplement v).isOpen (poleComplement (-v)).isOpen (poleComplement_cover v) n ≪≫
    reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n

def sphereCoverToEquator :
    TopCat.of ↥((poleComplement v : Set (Metric.sphere (0 : E) 1)) ∩ (poleComplement (-v) : Set (Metric.sphere (0 : E) 1))) ⟶
      TopCat.of (EquatorialSphere v) :=
  TopCat.ofHom (poleIntersectionHomotopyEquiv v).toFun


@[simp]
theorem sphereCoverToEquator_apply (x : poleIntersection v) :
    sphereCoverToEquator v x = poleIntersectionHomotopyEquiv v x := rfl

@[reassoc (attr := simp)]
theorem small_inclusion_sphereEquatorReducedHomologyIso (n : ℕ) :
    HomologicalComplex.homologyMap
      (augmentedSmallChainMap R (TopCat.of (Metric.sphere (0 : E) 1))
        (twoSetFamily (TopCat.of (Metric.sphere (0 : E) 1))
          (poleComplement v : Set (Metric.sphere (0 : E) 1)) (poleComplement (-v) : Set (Metric.sphere (0 : E) 1)))) (n + 2) ≫
      (sphereEquatorReducedHomologyIso R v n).hom =
    augmentedSmallConnectingMap R (TopCat.of (Metric.sphere (0 : E) 1))
        (poleComplement v : Set (Metric.sphere (0 : E) 1)) (poleComplement (-v) : Set (Metric.sphere (0 : E) 1)) n ≫
      reducedSingularHomologyMap R (sphereCoverToEquator v) n := by
  have hs := contractibleSpace_poleComplement v
  have ht := contractibleSpace_poleComplement (-v)
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, small_inclusion_reducedMayerVietorisConnectingIso]
  rfl

def euclideanSphereReducedHomologySuccIso {k : Type} [Ring k] (R : ModuleCat k)
    (d n : ℕ) :
    reducedSingularHomology R
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)) (n + 1) ≅
      reducedSingularHomology R
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) n := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) := ⟨by simp⟩
  exact sphereEquatorReducedHomologyIso R (euclideanNorth d) n ≪≫
    reducedSingularHomologyIso R (equatorialSphereHomeomorph d (euclideanNorth d)).toHomotopyEquiv n

theorem isZero_euclideanZeroSphere_reducedHomology_succ {k : Type} [Ring k]
    (R : ModuleCat k) (n : ℕ) :
    IsZero (reducedSingularHomology R
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)) (n + 1)) :=
  IsZero.of_iso
    (isZero_reducedSingularHomology_of_isEmpty R
      (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 0)) 1)) n)
    (euclideanSphereReducedHomologySuccIso R 0 n)

end DifferentialGeometry.LocalDegree
