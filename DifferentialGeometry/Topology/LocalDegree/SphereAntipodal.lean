import DifferentialGeometry.Topology.Homology.Reduced.MayerVietorisNaturality
import DifferentialGeometry.Topology.LocalDegree.SphereDegree

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u
namespace Poincare.LocalDegree
open Poincare.Homology
variable {E : Type u} [NormedAddCommGroup E]


def unitSphereAntipodal (E : Type u) [NormedAddCommGroup E] :
    C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1) :=
  ⟨fun x ↦ -x, (continuous_neg.comp continuous_subtype_val).subtype_mk _⟩


@[simp]
theorem unitSphereAntipodal_apply (x : Metric.sphere (0 : E) 1) :
    unitSphereAntipodal E x = -x := rfl


@[simp]
theorem unitSphereAntipodal_comp_self :
    (unitSphereAntipodal E).comp (unitSphereAntipodal E) =
      ContinuousMap.id (Metric.sphere (0 : E) 1) := by
  ext x
  exact neg_neg x.val

private theorem antipodal_maps_first (v : Metric.sphere (0 : E) 1) :
    Set.MapsTo (unitSphereAntipodal E)
      (poleComplement v : Set (Metric.sphere (0 : E) 1))
      (poleComplement (-v) : Set (Metric.sphere (0 : E) 1)) := by
  intro x hx
  change -x ≠ -v
  change x ≠ v at hx
  intro h
  apply hx
  simpa using congrArg Neg.neg h

private theorem antipodal_maps_second (v : Metric.sphere (0 : E) 1) :
    Set.MapsTo (unitSphereAntipodal E)
      (poleComplement (-v) : Set (Metric.sphere (0 : E) 1))
      (poleComplement v : Set (Metric.sphere (0 : E) 1)) := by
  intro x hx
  change -x ≠ v
  change x ≠ -v at hx
  intro h
  apply hx
  simpa using congrArg Neg.neg h


def poleOverlapAntipodal (v : Metric.sphere (0 : E) 1) :
    TopCat.of (poleIntersection v) ⟶ TopCat.of (poleIntersection v) :=
  relativeSubspaceMap (TopCat.ofHom (unitSphereAntipodal E))
    (fun _ hx ↦ ⟨antipodal_maps_second v hx.2, antipodal_maps_first v hx.1⟩)

variable [InnerProductSpace ℝ E]


theorem poleIntersectionHomotopyEquiv_inv_antipodal (v : Metric.sphere (0 : E) 1) :
    TopCat.ofHom (poleIntersectionHomotopyEquiv v).invFun ≫ poleOverlapAntipodal v =
      TopCat.ofHom (unitSphereAntipodal (ℝ ∙ (v : E))ᗮ) ≫
        TopCat.ofHom (poleIntersectionHomotopyEquiv v).invFun := by
  ext x
  change -(((poleIntersectionHomotopyEquiv v).symm x).val : E) =
    (((poleIntersectionHomotopyEquiv v).symm (-x)).val : E)
  rw [poleIntersectionHomotopyEquiv_symm_apply, poleIntersectionHomotopyEquiv_symm_apply]
  rfl

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem poleIntersectionHomologyIso_antipodal (v : Metric.sphere (0 : E) 1) (n : ℕ) :
    reducedSingularHomologyMap R (poleOverlapAntipodal v) n ≫
      (reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n).hom =
    (reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n).hom ≫
      reducedSingularHomologyMap R (TopCat.ofHom (unitSphereAntipodal (ℝ ∙ (v : E))ᗮ)) n := by
  let e : reducedSingularHomology R (TopCat.of (poleIntersection v)) n ≅
      reducedSingularHomology R (TopCat.of (EquatorialSphere v)) n :=
    reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n
  have hh := congrArg (fun g ↦ reducedSingularHomologyMap R g n) (poleIntersectionHomotopyEquiv_inv_antipodal v)
  simp only [reducedSingularHomologyMap_comp] at hh
  change e.inv ≫ reducedSingularHomologyMap R (poleOverlapAntipodal v) n =
    reducedSingularHomologyMap R (TopCat.ofHom (unitSphereAntipodal (ℝ ∙ (v : E))ᗮ)) n ≫ e.inv at hh
  apply (cancel_epi e.inv).mp
  change e.inv ≫ (_ ≫ e.hom) = e.inv ≫ (e.hom ≫ _)
  rw [← Category.assoc, hh, Category.assoc, e.inv_hom_id, Category.comp_id,
    ← Category.assoc, e.inv_hom_id, Category.id_comp]

private theorem poleCover (v : Metric.sphere (0 : E) 1) : ∀ x : Metric.sphere (0 : E) 1,
    x ∈ (poleComplement v : Set (Metric.sphere (0 : E) 1)) ∨
      x ∈ (poleComplement (-v) : Set (Metric.sphere (0 : E) 1)) := by
  intro x
  have h : x ∈ (poleComplement v ⊔ poleComplement (-v)) := by
    rw [poleComplement_sup]
    trivial
  exact h

theorem reducedConnectingMap_of_coverExchange {X : TopCat.{u}} {s t : Set X} (f : X ⟶ X)
    (hs : Set.MapsTo f s t) (ht : Set.MapsTo f t s)
    (hsO : IsOpen s) (htO : IsOpen t) (hc : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    reducedSingularHomologyMap R f (n + 1) ≫
        reducedMayerVietorisConnectingMap R X s t hsO htO hc n =
      -(reducedMayerVietorisConnectingMap R X s t hsO htO hc n ≫
        reducedSingularHomologyMap R
          (relativeSubspaceMap f (show Set.MapsTo f (s ∩ t) (s ∩ t) from
            fun _ hx ↦ ⟨ht hx.2, hs hx.1⟩)) n) := by
  have h := reducedMayerVietorisConnectingMap_naturality R f hs ht hsO htO hc
    htO hsO (fun x ↦ (hc x).symm) n
  rw [reducedMayerVietorisConnectingMap_swap R X s t hsO htO hc n] at h
  have hh := congrArg (fun g ↦ g ≫ reducedSingularHomologyMap R
    (twoCoverIntersectionSwap X t s) n) h
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc,
    ← reducedSingularHomologyMap_comp, twoCoverIntersectionSwap_comp,
    reducedSingularHomologyMap_id, Category.comp_id] at hh
  exact neg_eq_iff_eq_neg.mp hh


theorem sphereEquatorReducedHomologyIso_antipodal (v : Metric.sphere (0 : E) 1) (n : ℕ) :
    reducedSingularHomologyMap R (TopCat.ofHom (unitSphereAntipodal E)) (n + 1) ≫
      (sphereEquatorReducedHomologyIso R v n).hom =
    -((sphereEquatorReducedHomologyIso R v n).hom ≫
      reducedSingularHomologyMap R (TopCat.ofHom (unitSphereAntipodal (ℝ ∙ (v : E))ᗮ)) n) := by
  have hs := contractibleSpace_poleComplement v
  have ht := contractibleSpace_poleComplement (-v)
  have h := reducedConnectingMap_of_coverExchange R (TopCat.ofHom (unitSphereAntipodal E))
    (antipodal_maps_first v) (antipodal_maps_second v)
    (poleComplement v).isOpen (poleComplement (-v)).isOpen (poleCover v) n
  rw [reducedMayerVietorisConnectingMap_eq_iso] at h
  change _ ≫ (_ ≫ _) = -((_ ≫ _) ≫ _)
  rw [← Category.assoc, h, Preadditive.neg_comp, Category.assoc]
  have hh := poleIntersectionHomologyIso_antipodal R v n
  have hhh := congrArg (fun f ↦
    (reducedMayerVietorisConnectingIso R (TopCat.of (Metric.sphere (0 : E) 1))
      (poleComplement v : Set (Metric.sphere (0 : E) 1))
      (poleComplement (-v) : Set (Metric.sphere (0 : E) 1))
      (poleComplement v).isOpen (poleComplement (-v)).isOpen (poleCover v) n).hom ≫ f) hh
  simpa only [Category.assoc] using! congrArg Neg.neg hhh

theorem equatorialSphereHomeomorph_antipodal {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (d : ℕ)
    [Fact (Module.finrank ℝ E = d + 1)] (v : Metric.sphere (0 : E) 1) :
    TopCat.ofHom (unitSphereAntipodal (ℝ ∙ (v : E))ᗮ) ≫
        TopCat.ofHom (equatorialSphereHomeomorph d v).toHomotopyEquiv.toFun =
      TopCat.ofHom (equatorialSphereHomeomorph d v).toHomotopyEquiv.toFun ≫
        TopCat.ofHom (unitSphereAntipodal (EuclideanSpace ℝ (Fin d))) := by
  ext x : 2
  change (OrthonormalBasis.fromOrthogonalSpanSingleton d
    (ne_zero_of_mem_unit_sphere v)).repr (-x.val) =
      -(OrthonormalBasis.fromOrthogonalSpanSingleton d
        (ne_zero_of_mem_unit_sphere v)).repr x.val
  exact map_neg _ _

theorem euclideanSphereReducedHomologySuccIso_antipodal {k : Type} [Ring k] (R : ModuleCat k)
    (d n : ℕ) :
    reducedSingularHomologyMap R
        (TopCat.ofHom (unitSphereAntipodal (EuclideanSpace ℝ (Fin (d + 1))))) (n + 1) ≫
      (euclideanSphereReducedHomologySuccIso R d n).hom =
    -((euclideanSphereReducedHomologySuccIso R d n).hom ≫
      reducedSingularHomologyMap R
        (TopCat.ofHom (unitSphereAntipodal (EuclideanSpace ℝ (Fin d)))) n) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))) = d + 1) := ⟨by simp⟩
  have hh := congrArg (fun f ↦ reducedSingularHomologyMap R f n)
    (equatorialSphereHomeomorph_antipodal d (euclideanNorth d))
  simp only [reducedSingularHomologyMap_comp] at hh
  change _ ≫ (_ ≫ _) = -((_ ≫ _) ≫ _)
  rw [← Category.assoc, sphereEquatorReducedHomologyIso_antipodal,
    Preadditive.neg_comp, Category.assoc]
  have hhh := congrArg (fun f ↦ (sphereEquatorReducedHomologyIso R (euclideanNorth d) n).hom ≫ f) hh
  simpa only [Category.assoc] using! congrArg Neg.neg hhh


theorem euclideanZeroSphereHomeomorphReal_antipodal :
    TopCat.ofHom (unitSphereAntipodal (EuclideanSpace ℝ (Fin 1))) ≫
        TopCat.ofHom euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun =
      TopCat.ofHom euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun ≫
        TopCat.ofHom zeroSphereAntipodal := by
  ext x
  change (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm (-x.val) =
      -(OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm x.val
  exact (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm.toLinearEquiv.map_neg x.val


theorem euclideanSphereDegree_antipodal_zero :
    euclideanSphereDegree (unitSphereAntipodal (EuclideanSpace ℝ (Fin 1))) = -1 := by
  have h := congrArg (fun f ↦ reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) f 0)
    euclideanZeroSphereHomeomorphReal_antipodal
  simp only [reducedSingularHomologyMap_comp] at h
  change euclideanZeroSphereReducedHomologyEquiv _ = -1
  rw [euclideanZeroSphereReducedHomologyEquiv_apply]
  change zeroSphereReducedEquiv (realZeroSphereReducedHomologyEquiv
    ((reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (unitSphereAntipodal (EuclideanSpace ℝ (Fin 1)))) 0 ≫
     reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun) 0)
        (euclideanSphereTopGenerator 0))) = -1
  rw [h]
  change zeroSphereReducedEquiv (realZeroSphereReducedHomologyEquiv
    (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom zeroSphereAntipodal) 0 _)) = -1
  rw [realZeroSphereReducedHomologyEquiv_map]
  have hh := congrArg (fun c ↦ zeroSphereReducedEquiv (zeroSphereReducedMap zeroSphereAntipodal c))
    euclideanSphereTopGenerator_zero_comparison
  exact hh.trans zeroSphereDegree_antipodal


theorem euclideanSphereDegree_antipodal_succ (d : ℕ) :
    euclideanSphereDegree (unitSphereAntipodal (EuclideanSpace ℝ (Fin ((d + 1) + 1)))) =
      -euclideanSphereDegree (unitSphereAntipodal (EuclideanSpace ℝ (Fin (d + 1)))) := by
  change euclideanSphereTopReducedHomologyEquiv (d + 1) _ = _
  rw [euclideanSphereTopReducedHomologyEquiv_succ]
  change euclideanSphereTopReducedHomologyEquiv d
    ((reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (unitSphereAntipodal (EuclideanSpace ℝ (Fin ((d + 1) + 1))))) (d + 1) ≫
      (euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom)
        (euclideanSphereTopGenerator (d + 1))) = _
  rw [euclideanSphereReducedHomologySuccIso_antipodal]
  change euclideanSphereTopReducedHomologyEquiv d
    (-reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
      (TopCat.ofHom (unitSphereAntipodal (EuclideanSpace ℝ (Fin (d + 1))))) d
        ((euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
          (euclideanSphereTopGenerator (d + 1)))) = _
  rw [map_neg, euclideanSphereTopGenerator_connecting]
  rfl


theorem euclideanSphereDegree_antipodal (d : ℕ) :
    euclideanSphereDegree (unitSphereAntipodal (EuclideanSpace ℝ (Fin (d + 1)))) =
      (-1 : ℤ) ^ (d + 1) := by
  induction d with
  | zero => simpa using euclideanSphereDegree_antipodal_zero
  | succ d hd =>
    rw [euclideanSphereDegree_antipodal_succ, hd]
    simpa only [mul_neg_one] using (pow_succ (-1 : ℤ) (d + 1)).symm

theorem euclideanSphereAntipodal_generator (d : ℕ) :
    reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
        (TopCat.ofHom (unitSphereAntipodal (EuclideanSpace ℝ (Fin (d + 1))))) d
          (euclideanSphereTopGenerator d) =
      ((-1 : ℤ) ^ (d + 1)) • euclideanSphereTopGenerator d := by
  rw [euclideanSphereDegree_generator, euclideanSphereDegree_antipodal]

end Poincare.LocalDegree
