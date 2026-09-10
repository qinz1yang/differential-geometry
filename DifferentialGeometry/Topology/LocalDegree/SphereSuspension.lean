import DifferentialGeometry.Topology.LocalDegree.SphereSuspension.Geometry
import DifferentialGeometry.Topology.LocalDegree.SphereDegree
import DifferentialGeometry.Topology.Homology.Reduced.MayerVietorisNaturality

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Metric Set
noncomputable section
universe u
namespace Poincare.LocalDegree
open Poincare.Homology
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


theorem equatorSphereSuspension_maps_first (v : sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) :
    MapsTo (equatorSphereSuspension v f) (poleComplement v : Set (sphere (0 : E) 1))
      (poleComplement v : Set (sphere (0 : E) 1)) := by
  intro x hx
  exact mt (equatorSphereSuspension_eq_north_iff v f x).mp hx


theorem equatorSphereSuspension_maps_second (v : sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) :
    MapsTo (equatorSphereSuspension v f) (poleComplement (-v) : Set (sphere (0 : E) 1))
      (poleComplement (-v) : Set (sphere (0 : E) 1)) := by
  intro x hx
  exact mt (equatorSphereSuspension_eq_south_iff v f x).mp hx


def poleOverlapSuspension (v : sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) :
    TopCat.of (poleIntersection v) ⟶ TopCat.of (poleIntersection v) :=
  relativeSubspaceMap (TopCat.ofHom (equatorSphereSuspension v f))
    ((equatorSphereSuspension_maps_first v f).inter_inter
      (equatorSphereSuspension_maps_second v f))


theorem poleIntersectionHomotopyEquiv_inv_suspension (v : sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) :
    TopCat.ofHom (poleIntersectionHomotopyEquiv v).invFun ≫ poleOverlapSuspension v f =
      TopCat.ofHom f ≫ TopCat.ofHom (poleIntersectionHomotopyEquiv v).invFun := by
  ext x
  change orthogonalRadialExtension (ℝ ∙ (v : E))ᗮ f
    (((poleIntersectionHomotopyEquiv v).symm x).val : E) =
      (((poleIntersectionHomotopyEquiv v).symm (f x)).val : E)
  rw [poleIntersectionHomotopyEquiv_symm_apply, poleIntersectionHomotopyEquiv_symm_apply,
    orthogonalRadialExtension_sphere]

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem poleIntersectionHomologyIso_suspension (v : sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) (n : ℕ) :
    reducedSingularHomologyMap R (poleOverlapSuspension v f) n ≫
      (reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n).hom =
    (reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n).hom ≫
      reducedSingularHomologyMap R (TopCat.ofHom f) n := by
  let e : reducedSingularHomology R (TopCat.of (poleIntersection v)) n ≅
      reducedSingularHomology R (TopCat.of (EquatorialSphere v)) n :=
    reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n
  have hh := congrArg (fun g ↦ reducedSingularHomologyMap R g n)
    (poleIntersectionHomotopyEquiv_inv_suspension v f)
  simp only [reducedSingularHomologyMap_comp] at hh
  change e.inv ≫ reducedSingularHomologyMap R (poleOverlapSuspension v f) n =
    reducedSingularHomologyMap R (TopCat.ofHom f) n ≫ e.inv at hh
  apply (cancel_epi e.inv).mp
  change e.inv ≫ (_ ≫ e.hom) = e.inv ≫ (e.hom ≫ _)
  rw [← Category.assoc, hh, Category.assoc, e.inv_hom_id, Category.comp_id,
    ← Category.assoc, e.inv_hom_id, Category.id_comp]

private theorem poleCover (v : sphere (0 : E) 1) : ∀ x : sphere (0 : E) 1,
    x ∈ (poleComplement v : Set (sphere (0 : E) 1)) ∨
      x ∈ (poleComplement (-v) : Set (sphere (0 : E) 1)) := by
  intro x
  have h : x ∈ (poleComplement v ⊔ poleComplement (-v)) := by
    rw [poleComplement_sup]
    trivial
  exact h

theorem sphereEquatorReducedHomologyIso_suspension (v : sphere (0 : E) 1)
    (f : C(EquatorialSphere v, EquatorialSphere v)) (n : ℕ) :
    reducedSingularHomologyMap R (TopCat.ofHom (equatorSphereSuspension v f)) (n + 1) ≫
      (sphereEquatorReducedHomologyIso R v n).hom =
    (sphereEquatorReducedHomologyIso R v n).hom ≫
      reducedSingularHomologyMap R (TopCat.ofHom f) n := by
  have hs := contractibleSpace_poleComplement v
  have ht := contractibleSpace_poleComplement (-v)
  have h := reducedMayerVietorisConnectingMap_naturality R
    (TopCat.ofHom (equatorSphereSuspension v f))
    (equatorSphereSuspension_maps_first v f) (equatorSphereSuspension_maps_second v f)
    (poleComplement v).isOpen (poleComplement (-v)).isOpen (poleCover v)
    (poleComplement v).isOpen (poleComplement (-v)).isOpen (poleCover v) n
  rw [reducedMayerVietorisConnectingMap_eq_iso] at h
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  rw [← Category.assoc, h, Category.assoc]
  have hh := poleIntersectionHomologyIso_suspension R v f n
  have hhh := congrArg (fun g ↦
    (reducedMayerVietorisConnectingIso R (TopCat.of (sphere (0 : E) 1))
      (poleComplement v : Set (sphere (0 : E) 1))
      (poleComplement (-v) : Set (sphere (0 : E) 1))
      (poleComplement v).isOpen (poleComplement (-v)).isOpen (poleCover v) n).hom ≫ g) hh
  simpa only [Category.assoc] using! hhh


def euclideanSuspensionEquatorHomeomorph (d : ℕ) :
    EquatorialSphere (euclideanNorth (d + 1)) ≃ₜ EuclideanSphere d := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + 1))) = (d + 1) + 1) := ⟨by simp⟩
  exact equatorialSphereHomeomorph (d + 1) (euclideanNorth (d + 1))


def euclideanSuspensionEquatorMap {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    C(EquatorialSphere (euclideanNorth (d + 1)), EquatorialSphere (euclideanNorth (d + 1))) :=
  (euclideanSuspensionEquatorHomeomorph d).symm.toHomotopyEquiv.toFun.comp
    (f.comp (euclideanSuspensionEquatorHomeomorph d).toHomotopyEquiv.toFun)

def euclideanSphereSuspension {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    C(EuclideanSphere (d + 1), EuclideanSphere (d + 1)) :=
  equatorSphereSuspension (euclideanNorth (d + 1)) (euclideanSuspensionEquatorMap f)


def euclideanSphereEquatorInclusion (d : ℕ) :
    C(EuclideanSphere d, EuclideanSphere (d + 1)) where
  toFun x := ((poleIntersectionHomotopyEquiv (euclideanNorth (d + 1))).invFun
    ((euclideanSuspensionEquatorHomeomorph d).symm x)).val
  continuous_toFun := continuous_subtype_val.comp
    ((poleIntersectionHomotopyEquiv (euclideanNorth (d + 1))).invFun.continuous.comp
      (euclideanSuspensionEquatorHomeomorph d).symm.continuous)


theorem euclideanSphereSuspension_equator {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    (euclideanSphereSuspension f).comp (euclideanSphereEquatorInclusion d) =
      (euclideanSphereEquatorInclusion d).comp f := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change orthogonalRadialExtension (ℝ ∙ (euclideanNorth (d + 1)).val)ᗮ
      (euclideanSuspensionEquatorMap f)
      (((poleIntersectionHomotopyEquiv (euclideanNorth (d + 1))).symm
        ((euclideanSuspensionEquatorHomeomorph d).symm x)).val : EuclideanSpace ℝ (Fin ((d + 1) + 1))) =
    (((poleIntersectionHomotopyEquiv (euclideanNorth (d + 1))).symm
      ((euclideanSuspensionEquatorHomeomorph d).symm (f x))).val : EuclideanSpace ℝ (Fin ((d + 1) + 1)))
  rw [poleIntersectionHomotopyEquiv_symm_apply, poleIntersectionHomotopyEquiv_symm_apply,
    orthogonalRadialExtension_sphere]
  change (((euclideanSuspensionEquatorHomeomorph d).symm
    (f ((euclideanSuspensionEquatorHomeomorph d)
      ((euclideanSuspensionEquatorHomeomorph d).symm x)))).val : EuclideanSpace ℝ (Fin ((d + 1) + 1))) = _
  rw [Homeomorph.apply_symm_apply]


@[simp]
theorem euclideanSphereSuspension_north {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    euclideanSphereSuspension f (euclideanNorth (d + 1)) = euclideanNorth (d + 1) :=
  (equatorSphereSuspension_eq_north_iff _ _ _).mpr rfl


@[simp]
theorem euclideanSphereSuspension_south {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    euclideanSphereSuspension f (-euclideanNorth (d + 1)) = -euclideanNorth (d + 1) :=
  (equatorSphereSuspension_eq_south_iff _ _ _).mpr rfl


theorem euclideanSphereSuspension_height {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d))
    (x : EuclideanSphere (d + 1)) :
    inner ℝ (euclideanNorth (d + 1)).val (euclideanSphereSuspension f x).val =
      inner ℝ (euclideanNorth (d + 1)).val x.val :=
  equatorSphereSuspension_height _ _ _


theorem euclideanSuspensionEquatorMap_naturality {d : ℕ}
    (f : C(EuclideanSphere d, EuclideanSphere d)) :
    TopCat.ofHom (euclideanSuspensionEquatorMap f) ≫
        TopCat.ofHom (euclideanSuspensionEquatorHomeomorph d).toHomotopyEquiv.toFun =
      TopCat.ofHom (euclideanSuspensionEquatorHomeomorph d).toHomotopyEquiv.toFun ≫
        TopCat.ofHom f := by
  ext x : 1
  exact (euclideanSuspensionEquatorHomeomorph d).apply_symm_apply _

theorem euclideanSphereReducedHomologySuccIso_suspension {k : Type} [Ring k] (R : ModuleCat k)
    {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) (n : ℕ) :
    reducedSingularHomologyMap R (TopCat.ofHom (euclideanSphereSuspension f)) (n + 1) ≫
      (euclideanSphereReducedHomologySuccIso R (d + 1) n).hom =
    (euclideanSphereReducedHomologySuccIso R (d + 1) n).hom ≫
      reducedSingularHomologyMap R (TopCat.ofHom f) n := by
  have hh := congrArg (fun g ↦ reducedSingularHomologyMap R g n)
    (euclideanSuspensionEquatorMap_naturality f)
  simp only [reducedSingularHomologyMap_comp] at hh
  change reducedSingularHomologyMap R
      (TopCat.ofHom (equatorSphereSuspension (euclideanNorth (d + 1))
        (euclideanSuspensionEquatorMap f))) (n + 1) ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  rw [← Category.assoc, sphereEquatorReducedHomologyIso_suspension, Category.assoc]
  have hhh := congrArg (fun g ↦
    (sphereEquatorReducedHomologyIso R (euclideanNorth (d + 1)) n).hom ≫ g) hh
  simpa only [Category.assoc] using! hhh


theorem euclideanSphereDegree_suspension {d : ℕ} (f : C(EuclideanSphere d, EuclideanSphere d)) :
    euclideanSphereDegree (euclideanSphereSuspension f) = euclideanSphereDegree f := by
  change euclideanSphereTopReducedHomologyEquiv (d + 1) _ = _
  rw [euclideanSphereTopReducedHomologyEquiv_succ]
  change euclideanSphereTopReducedHomologyEquiv d
    ((reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (euclideanSphereSuspension f)) (d + 1) ≫
      (euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom)
        (euclideanSphereTopGenerator (d + 1))) = _
  rw [euclideanSphereReducedHomologySuccIso_suspension]
  change euclideanSphereTopReducedHomologyEquiv d
    (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) d
      ((euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
        (euclideanSphereTopGenerator (d + 1)))) = _
  rw [euclideanSphereTopGenerator_connecting]
  rfl

end Poincare.LocalDegree
