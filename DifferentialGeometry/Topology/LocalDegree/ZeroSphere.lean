import DifferentialGeometry.Topology.LocalDegree.SphereMap
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Products

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Metric Set
open scoped Topology unitInterval Simplicial

noncomputable section

namespace DifferentialGeometry.LocalDegree


abbrev ZeroSphere := sphere (0 : ℝ) 1


def zeroSpherePositive : ZeroSphere := ⟨1, by simp⟩


def zeroSphereNegative : ZeroSphere := ⟨-1, by simp⟩

private theorem zeroSphere_cases (v : ZeroSphere) :
    v = zeroSpherePositive ∨ v = zeroSphereNegative := by
  have hv := v.property
  change (v : ℝ) ∈ sphere (0 : ℝ) 1 at hv
  rw [Real.sphere_eq_pair 0 (by norm_num)] at hv
  simp only [zero_sub, zero_add, mem_insert_iff, mem_singleton_iff] at hv
  exact hv.symm.imp (fun h ↦ Subtype.ext h) (fun h ↦ Subtype.ext h)

private instance : Finite ZeroSphere := by
  unfold ZeroSphere
  rw [Real.sphere_eq_pair 0 (by norm_num)]
  infer_instance

private instance : Fintype ZeroSphere := Fintype.ofFinite _

private def componentEquiv : ZerothHomotopy ZeroSphere ≃ ZeroSphere where
  toFun := ZerothHomotopy.lift id (fun _ _ p ↦ by
    simpa using TotallyDisconnectedSpace.eq_of_continuous p p.continuous 0 1)
  invFun := ZerothHomotopy.mk
  left_inv v := by induction v; rfl
  right_inv _ := rfl

private abbrev sphereSpace : TopCat := TopCat.of ZeroSphere

private abbrev intCoefficient : ModuleCat ℤ := ModuleCat.of ℤ ℤ

private abbrev homologyFunctor :=
  (singularHomologyFunctor (ModuleCat ℤ) 0).obj intCoefficient


abbrev ZeroSphereH0 :=
  ((singularHomologyFunctor (ModuleCat ℤ) 0).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of ZeroSphere)

private def homologyEquiv : ZeroSphereH0 ≃ₗ[ℤ] (ZeroSphere → ℤ) :=
  ((TopCat.singularHomology₀Iso sphereSpace intCoefficient ≪≫
      (sigmaConst.obj intCoefficient).mapIso componentEquiv.toIso ≪≫
      ModuleCat.coprodIsoDirectSum (fun _ : ZeroSphere ↦ intCoefficient)).toLinearEquiv).trans
    (DirectSum.linearEquivFunOnFintype ℤ ZeroSphere (fun _ ↦ ℤ))

private def pointClassHom (X : TopCat) (x : X) :
    intCoefficient ⟶ homologyFunctor.obj X :=
  ((TopCat.toSSet.obj X).chainComplex intCoefficient).liftCycles
    ((TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x)) 0
      (by simp) (by simp) ≫
      ((TopCat.toSSet.obj X).chainComplex intCoefficient).homologyπ 0

private theorem pointClassHom_eq (X : TopCat) (x : X) :
    pointClassHom X x =
      ((TopCat.toSSet.obj X).chainComplex intCoefficient).liftCycles
        ((TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x)) 0
          (by simp) (by simp) ≫
        ((TopCat.toSSet.obj X).chainComplex intCoefficient).homologyπ 0 := rfl

private theorem pointClassHom_map {X Y : TopCat} (f : X ⟶ Y) (x : X) :
    pointClassHom X x ≫ homologyFunctor.map f = pointClassHom Y (f x) := by
  rw [pointClassHom_eq, pointClassHom_eq]
  change _ ≫ HomologicalComplex.homologyMap
    (SSet.chainComplexMap (TopCat.toSSet.map f) intCoefficient) 0 = _
  simp only [Category.assoc, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, SSet.ι_chainComplexMap_f]
  congr 3


def zeroSphereClass (v : ZeroSphere) : ZeroSphereH0 := pointClassHom sphereSpace v 1

private theorem pointClassHom_iso (v : ZeroSphere) :
    pointClassHom sphereSpace v ≫
      (TopCat.singularHomology₀Iso sphereSpace intCoefficient).hom =
        Sigma.ι (fun _ : ZerothHomotopy ZeroSphere ↦ intCoefficient) (ZerothHomotopy.mk v) := by
  rw [pointClassHom_eq]
  change _ ≫ ((TopCat.toSSet.obj sphereSpace).homology₀Iso intCoefficient).hom ≫
    (sigmaConst.obj intCoefficient).map TopCat.zerothHomotopyEquiv.toIso.inv = _
  simp
  congr 1

private theorem homologyEquiv_class (v : ZeroSphere) :
    homologyEquiv (zeroSphereClass v) = Pi.single v 1 := by
  change DirectSum.linearEquivFunOnFintype ℤ ZeroSphere (fun _ ↦ ℤ)
    (((pointClassHom sphereSpace v ≫
      (TopCat.singularHomology₀Iso sphereSpace intCoefficient).hom ≫
      (sigmaConst.obj intCoefficient).map componentEquiv.toIso.hom ≫
      (ModuleCat.coprodIsoDirectSum (fun _ : ZeroSphere ↦ intCoefficient)).hom) 1)) = _
  rw [← Category.assoc, ← Category.assoc, pointClassHom_iso]
  simp [componentEquiv, DirectSum.linearEquivFunOnFintype_lof]
  rfl

private theorem positive_ne_negative : zeroSpherePositive ≠ zeroSphereNegative := by
  intro h
  have := congrArg Subtype.val h
  norm_num [zeroSpherePositive, zeroSphereNegative] at this

private theorem augmentation_class (v : ZeroSphere) :
    TopCat.singularHomology₀ε sphereSpace intCoefficient (zeroSphereClass v) = 1 := by
  have h : pointClassHom sphereSpace v ≫
      TopCat.singularHomology₀ε sphereSpace intCoefficient = 𝟙 intCoefficient := by
    rw [pointClassHom_eq]
    exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
      (TopCat.toSSet.obj sphereSpace) intCoefficient (TopCat.toSSetObj₀Equiv.symm v)
  exact congr($(h) 1)

private theorem homology_decompose (c : ZeroSphereH0) :
    c = homologyEquiv c zeroSpherePositive • zeroSphereClass zeroSpherePositive +
      homologyEquiv c zeroSphereNegative • zeroSphereClass zeroSphereNegative := by
  apply homologyEquiv.injective
  ext v
  rcases zeroSphere_cases v with rfl | rfl <;>
    simp [homologyEquiv_class, positive_ne_negative, positive_ne_negative.symm]

private theorem augmentation_eq (c : ZeroSphereH0) :
    TopCat.singularHomology₀ε sphereSpace intCoefficient c =
      homologyEquiv c zeroSpherePositive + homologyEquiv c zeroSphereNegative := by
  conv_lhs => rw [homology_decompose c]
  rw [map_add, map_zsmul, map_zsmul, augmentation_class, augmentation_class]
  simp


def zeroSphereReducedH0 : Submodule ℤ ZeroSphereH0 :=
  LinearMap.ker (TopCat.singularHomology₀ε (TopCat.of ZeroSphere) (ModuleCat.of ℤ ℤ)).hom


theorem mem_zeroSphereReducedH0_iff (c : ZeroSphereH0) :
    c ∈ zeroSphereReducedH0 ↔
      TopCat.singularHomology₀ε (TopCat.of ZeroSphere) (ModuleCat.of ℤ ℤ) c = 0 := Iff.rfl


def zeroSphereGenerator : zeroSphereReducedH0 :=
  ⟨zeroSphereClass zeroSpherePositive - zeroSphereClass zeroSphereNegative, by
    change TopCat.singularHomology₀ε sphereSpace intCoefficient
      (zeroSphereClass zeroSpherePositive - zeroSphereClass zeroSphereNegative) = 0
    rw [map_sub, augmentation_class, augmentation_class, sub_self]⟩


@[simp]
theorem zeroSphereGenerator_coe :
    (zeroSphereGenerator : ZeroSphereH0) =
      zeroSphereClass zeroSpherePositive - zeroSphereClass zeroSphereNegative := rfl

def zeroSphereReducedEquiv : zeroSphereReducedH0 ≃ₗ[ℤ] ℤ where
  toFun c := homologyEquiv c zeroSpherePositive
  invFun n := n • zeroSphereGenerator
  left_inv c := by
    apply Subtype.ext
    apply homologyEquiv.injective
    have hz : homologyEquiv (c : ZeroSphereH0) zeroSpherePositive +
        homologyEquiv (c : ZeroSphereH0) zeroSphereNegative = 0 :=
      (augmentation_eq c).symm.trans c.property
    ext v
    rcases zeroSphere_cases v with rfl | rfl
    · simp [homologyEquiv_class, positive_ne_negative]
    · simp [homologyEquiv_class, positive_ne_negative.symm]
      omega
  right_inv n := by
    simp [homologyEquiv_class, positive_ne_negative]
  map_add' c d := congrFun (homologyEquiv.map_add c d) zeroSpherePositive
  map_smul' n c := by simp


theorem zeroSphereReducedEquiv_smul_generator (c : zeroSphereReducedH0) :
    zeroSphereReducedEquiv c • zeroSphereGenerator = c :=
  zeroSphereReducedEquiv.symm_apply_apply c


@[simp]
theorem zeroSphereReducedEquiv_generator :
    zeroSphereReducedEquiv zeroSphereGenerator = 1 := by
  change homologyEquiv (zeroSphereGenerator : ZeroSphereH0) zeroSpherePositive = 1
  simp [homologyEquiv_class, positive_ne_negative]


theorem zeroSphereHomologyMap_class (f : C(ZeroSphere, ZeroSphere)) (v : ZeroSphere) :
    ((singularHomologyFunctor (ModuleCat ℤ) 0).obj (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom f) (zeroSphereClass v) = zeroSphereClass (f v) :=
  congr($(pointClassHom_map (TopCat.ofHom f) v) 1)

private theorem augmentation_map (f : C(ZeroSphere, ZeroSphere)) (c : ZeroSphereH0) :
    TopCat.singularHomology₀ε sphereSpace intCoefficient
      (homologyFunctor.map (TopCat.ofHom f) c) =
        TopCat.singularHomology₀ε sphereSpace intCoefficient c := by
  rw [homology_decompose c]
  simp only [map_add, map_zsmul, zeroSphereHomologyMap_class]
  rw [augmentation_class, augmentation_class, augmentation_class, augmentation_class]


def zeroSphereReducedMap (f : C(ZeroSphere, ZeroSphere)) :
    zeroSphereReducedH0 →ₗ[ℤ] zeroSphereReducedH0 where
  toFun c := ⟨homologyFunctor.map (TopCat.ofHom f) c, (augmentation_map f c).trans c.property⟩
  map_add' c d := Subtype.ext (map_add (homologyFunctor.map (TopCat.ofHom f)).hom
    (c : ZeroSphereH0) (d : ZeroSphereH0))
  map_smul' n c := Subtype.ext (by
    simp)


@[simp]
theorem zeroSphereReducedMap_coe (f : C(ZeroSphere, ZeroSphere)) (c : zeroSphereReducedH0) :
    (zeroSphereReducedMap f c : ZeroSphereH0) =
      ((singularHomologyFunctor (ModuleCat ℤ) 0).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.ofHom f) c := rfl


theorem zeroSphereReducedMap_generator_coe (f : C(ZeroSphere, ZeroSphere)) :
    (zeroSphereReducedMap f zeroSphereGenerator : ZeroSphereH0) =
      zeroSphereClass (f zeroSpherePositive) - zeroSphereClass (f zeroSphereNegative) := by
  simp [zeroSphereReducedMap_coe, zeroSphereHomologyMap_class]

def zeroSphereDegree (f : C(ZeroSphere, ZeroSphere)) : ℤ :=
  zeroSphereReducedEquiv (zeroSphereReducedMap f zeroSphereGenerator)


theorem zeroSphereDegree_smul_generator (f : C(ZeroSphere, ZeroSphere)) :
    zeroSphereDegree f • zeroSphereGenerator = zeroSphereReducedMap f zeroSphereGenerator :=
  zeroSphereReducedEquiv_smul_generator _


theorem zeroSphereDegree_eq_iff (f : C(ZeroSphere, ZeroSphere)) (n : ℤ) :
    zeroSphereDegree f = n ↔
      zeroSphereReducedMap f zeroSphereGenerator = n • zeroSphereGenerator := by
  rw [← zeroSphereDegree_smul_generator]
  constructor
  · rintro rfl
    rfl
  · intro h
    have := congrArg zeroSphereReducedEquiv h
    simpa using this


theorem zeroSphereReducedMap_comp (f g : C(ZeroSphere, ZeroSphere)) :
    zeroSphereReducedMap (g.comp f) = (zeroSphereReducedMap g).comp (zeroSphereReducedMap f) := by
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  change homologyFunctor.map (TopCat.ofHom f ≫ TopCat.ofHom g) (c : ZeroSphereH0) =
    homologyFunctor.map (TopCat.ofHom g) (homologyFunctor.map (TopCat.ofHom f) c)
  rw [Functor.map_comp]
  rfl


@[simp]
theorem zeroSphereDegree_id : zeroSphereDegree (ContinuousMap.id ZeroSphere) = 1 := by
  apply (zeroSphereDegree_eq_iff _ _).mpr
  apply Subtype.ext
  simp only [one_smul, zeroSphereReducedMap_coe]
  change homologyFunctor.map (𝟙 sphereSpace) (zeroSphereGenerator : ZeroSphereH0) = _
  rw [CategoryTheory.Functor.map_id]
  rfl


@[simp]
theorem zeroSphereDegree_const (v : ZeroSphere) :
    zeroSphereDegree (ContinuousMap.const ZeroSphere v) = 0 := by
  apply (zeroSphereDegree_eq_iff _ _).mpr
  apply Subtype.ext
  simp [zeroSphereReducedMap_coe, zeroSphereHomologyMap_class]


def zeroSphereAntipodal : C(ZeroSphere, ZeroSphere) where
  toFun v := ⟨-(v : ℝ), by simpa only [mem_sphere_zero_iff_norm, norm_neg] using v.property⟩
  continuous_toFun := continuous_subtype_val.neg.subtype_mk (fun v ↦ by
    change -(v : ℝ) ∈ ZeroSphere
    simpa only [mem_sphere_zero_iff_norm, norm_neg] using v.property)

private theorem antipodal_positive :
    zeroSphereAntipodal zeroSpherePositive = zeroSphereNegative := rfl

private theorem antipodal_negative :
    zeroSphereAntipodal zeroSphereNegative = zeroSpherePositive := by
  apply Subtype.ext
  simp [zeroSphereAntipodal, zeroSpherePositive, zeroSphereNegative]


@[simp]
theorem zeroSphereDegree_antipodal : zeroSphereDegree zeroSphereAntipodal = -1 := by
  apply (zeroSphereDegree_eq_iff _ _).mpr
  apply Subtype.ext
  simp [zeroSphereReducedMap_coe, zeroSphereHomologyMap_class, antipodal_positive,
    antipodal_negative, neg_sub]


theorem zeroSphereDegree_comp (f g : C(ZeroSphere, ZeroSphere)) :
    zeroSphereDegree (g.comp f) = zeroSphereDegree g * zeroSphereDegree f := by
  apply (zeroSphereDegree_eq_iff _ _).mpr
  rw [zeroSphereReducedMap_comp, LinearMap.comp_apply, ← zeroSphereDegree_smul_generator,
    map_smul, ← zeroSphereDegree_smul_generator, smul_smul, mul_comm]


theorem zeroSphereDegree_eq_of_homotopy {f g : C(ZeroSphere, ZeroSphere)}
    (H : f.Homotopy g) : zeroSphereDegree f = zeroSphereDegree g := by
  have H' : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := H
  have h := H'.congr_homologyMap_singularChainComplexFunctor intCoefficient 0
  change homologyFunctor.map (TopCat.ofHom f) = homologyFunctor.map (TopCat.ofHom g) at h
  unfold zeroSphereDegree
  congr 1
  apply Subtype.ext
  exact congr($(h) (zeroSphereGenerator : ZeroSphereH0))


theorem zeroSphereDegree_eq (f : C(ZeroSphere, ZeroSphere)) :
    zeroSphereDegree f =
      (if f zeroSpherePositive = zeroSpherePositive then 1 else 0) -
        (if f zeroSphereNegative = zeroSpherePositive then 1 else 0) := by
  change homologyEquiv (homologyFunctor.map (TopCat.ofHom f)
    (zeroSphereGenerator : ZeroSphereH0)) zeroSpherePositive = _
  simp [zeroSphereHomologyMap_class, homologyEquiv_class, Pi.single_apply, eq_comm]

theorem zeroSphereDegree_sphereMap_id (R : ℝ) (r : Ioc (0 : ℝ) R) :
    zeroSphereDegree (sphereMap (fun y : ℝ ↦ y) 0 R continuousOn_id
      (fun _ _ h ↦ h) r) = 1 := by
  rw [sphereMap_id, zeroSphereDegree_id]

theorem zeroSphereDegree_sphereMap_eq (f : ℝ → ℝ) (x R : ℝ)
    (hf : ContinuousOn f (closedBall x R))
    (hzero : ∀ y ∈ closedBall x R, y ≠ x → f y ≠ 0)
    (r₀ r₁ : Ioc (0 : ℝ) R) :
    zeroSphereDegree (sphereMap f x R hf hzero r₀) =
      zeroSphereDegree (sphereMap f x R hf hzero r₁) :=
  zeroSphereDegree_eq_of_homotopy (sphereMapHomotopy f x R hf hzero r₀ r₁)

end DifferentialGeometry.LocalDegree
