import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial ContinuousMap

noncomputable section
universe u

namespace DifferentialGeometry.Homology

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  (X : TopCat.{u})

def singularAugmentation :
    ((TopCat.toSSet.obj X).chainComplex R).X 0 ⟶ R :=
  Sigma.desc (fun _ : TopCat.toSSet.obj X _⦋0⦌ ↦ 𝟙 R)


@[reassoc (attr := simp)]
theorem ι_singularAugmentation (σ : TopCat.toSSet.obj X _⦋0⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularAugmentation R X = 𝟙 R :=
  Sigma.ι_desc _ _


theorem d_singularAugmentation :
    ((TopCat.toSSet.obj X).chainComplex R).d 1 0 ≫ singularAugmentation R X = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d, Fin.sum_univ_two]
  simp

variable {X} {Y Z : TopCat.{u}}


@[reassoc (attr := simp)]
theorem singularAugmentation_naturality (f : X ⟶ Y) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) R).f 0 ≫
        singularAugmentation R Y = singularAugmentation R X := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  simp

variable (X)

def augmentedSingularChainComplex : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.augment ((TopCat.toSSet.obj X).chainComplex R)
    (singularAugmentation R X) (d_singularAugmentation R X)


@[simp]
theorem augmentedSingularChainComplex_X_zero :
    (augmentedSingularChainComplex R X).X 0 = R := rfl


@[simp]
theorem augmentedSingularChainComplex_X_succ (n : ℕ) :
    (augmentedSingularChainComplex R X).X (n + 1) =
      ((TopCat.toSSet.obj X).chainComplex R).X n := rfl


@[simp]
theorem augmentedSingularChainComplex_d_one_zero :
    (augmentedSingularChainComplex R X).d 1 0 = singularAugmentation R X := rfl


@[simp]
theorem augmentedSingularChainComplex_d_succ_succ (i j : ℕ) :
    (augmentedSingularChainComplex R X).d (i + 1) (j + 1) =
      ((TopCat.toSSet.obj X).chainComplex R).d i j :=
  ChainComplex.augment_d_succ_succ _ _ _ i j

variable {X}

def augmentedSingularChainMap (f : X ⟶ Y) :
    augmentedSingularChainComplex R X ⟶ augmentedSingularChainComplex R Y where
  f
    | 0 => 𝟙 R
    | n + 1 => (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n
  comm' i j _ := by
    rcases i with _ | i
    · cases j <;> simp [augmentedSingularChainComplex, ChainComplex.augment]
    rcases j with _ | j
    · cases i
      · simpa only [augmentedSingularChainComplex, ChainComplex.augment,
          Category.comp_id] using! singularAugmentation_naturality R f
      · simp [augmentedSingularChainComplex, ChainComplex.augment]
    simpa only [augmentedSingularChainComplex_d_succ_succ] using!
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).comm i j


@[simp]
theorem augmentedSingularChainMap_f_zero (f : X ⟶ Y) :
    (augmentedSingularChainMap R f).f 0 = 𝟙 R := rfl


@[simp]
theorem augmentedSingularChainMap_f_succ (f : X ⟶ Y) (n : ℕ) :
    (augmentedSingularChainMap R f).f (n + 1) =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n := rfl


@[simp]
theorem augmentedSingularChainMap_id : augmentedSingularChainMap R (𝟙 X) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    exact congrArg (fun φ ↦ φ.f n)
      (CategoryTheory.Functor.map_id ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R) X)


theorem augmentedSingularChainMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    augmentedSingularChainMap R (f ≫ g) =
      augmentedSingularChainMap R f ≫ augmentedSingularChainMap R g := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => exact (Category.id_comp _).symm
  | succ n =>
    exact congrArg (fun φ ↦ φ.f n)
      (Functor.map_comp ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R) f g)


def augmentedSingularChainFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} k) ℕ where
  obj := augmentedSingularChainComplex R
  map := augmentedSingularChainMap R
  map_id _ := augmentedSingularChainMap_id R
  map_comp := augmentedSingularChainMap_comp R

def augmentedSingularChainHomotopy {f g : X ⟶ Y} (H : TopCat.Homotopy f g) :
    _root_.Homotopy (augmentedSingularChainMap R f) (augmentedSingularChainMap R g) where
  hom
    | i + 1, j + 1 => (H.toSSet.chainComplexMap R).hom i j
    | _, _ => 0
  zero i j hij := by
    cases i <;> cases j
    · rfl
    · rfl
    · rfl
    · exact (H.toSSet.chainComplexMap R).zero _ _ (by simpa using hij)
  comm i := by
    cases i with
    | zero =>
      rw [dNext_nat, prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
      exact (show (𝟙 R) = (0 : R ⟶ R) ≫ (0 : R ⟶ R) +
          (0 : R ⟶ ((TopCat.toSSet.obj Y).chainComplex R).X 0) ≫
            singularAugmentation R Y + 𝟙 R by simp)
    | succ i =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 2) (i + 1) from rfl)]
      have h := (H.toSSet.chainComplexMap R).comm i
      rw [dNext_nat, prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i from rfl)] at h
      cases i with
      | zero =>
        exact (show (SSet.chainComplexMap (TopCat.toSSet.map f) R).f 0 =
            singularAugmentation R X ≫
              (0 : R ⟶ ((TopCat.toSSet.obj Y).chainComplex R).X 0) +
            (H.toSSet.chainComplexMap R).hom 0 1 ≫
              ((TopCat.toSSet.obj Y).chainComplex R).d 1 0 +
            (SSet.chainComplexMap (TopCat.toSSet.map g) R).f 0 by
          simpa using! h)
      | succ i => simpa only [augmentedSingularChainMap_f_succ,
          augmentedSingularChainComplex_d_succ_succ, Nat.add_sub_cancel_right] using! h


@[simp]
theorem augmentedSingularChainHomotopy_hom_zero {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (j : ℕ) :
    (augmentedSingularChainHomotopy R H).hom 0 j = 0 := by cases j <;> rfl


@[simp]
theorem augmentedSingularChainHomotopy_hom_succ {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (i j : ℕ) :
    (augmentedSingularChainHomotopy R H).hom (i + 1) (j + 1) =
      (H.toSSet.chainComplexMap R).hom i j := rfl

abbrev reducedSingularHomology (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} k :=
  (augmentedSingularChainComplex R X).homology (n + 1)


def reducedSingularHomologyMap (f : X ⟶ Y) (n : ℕ) :
    reducedSingularHomology R X n ⟶ reducedSingularHomology R Y n :=
  HomologicalComplex.homologyMap (augmentedSingularChainMap R f) (n + 1)


@[simp]
theorem reducedSingularHomologyMap_id (n : ℕ) :
    reducedSingularHomologyMap R (𝟙 X) n = 𝟙 _ := by
  simp [reducedSingularHomologyMap, reducedSingularHomology]


theorem reducedSingularHomologyMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    reducedSingularHomologyMap R (f ≫ g) n =
      reducedSingularHomologyMap R f n ≫ reducedSingularHomologyMap R g n := by
  exact (congrArg (HomologicalComplex.homologyFunctor _ _ (n + 1)).map
    (augmentedSingularChainMap_comp R f g)).trans (Functor.map_comp _ _ _)


theorem reducedSingularHomologyMap_eq_of_homotopy {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (n : ℕ) :
    reducedSingularHomologyMap R f n = reducedSingularHomologyMap R g n :=
  (augmentedSingularChainHomotopy R H).homologyMap_eq (n + 1)


def reducedSingularHomologyFunctor (n : ℕ) : TopCat.{u} ⥤ ModuleCat.{u} k :=
  augmentedSingularChainFunctor R ⋙ HomologicalComplex.homologyFunctor _ _ (n + 1)

def reducedSingularHomologyIso (e : X ≃ₕ Y) (n : ℕ) :
    reducedSingularHomology R X n ≅ reducedSingularHomology R Y n where
  hom := reducedSingularHomologyMap R (TopCat.ofHom e.toFun) n
  inv := reducedSingularHomologyMap R (TopCat.ofHom e.invFun) n
  hom_inv_id := by
    rw [← reducedSingularHomologyMap_comp]
    exact (reducedSingularHomologyMap_eq_of_homotopy R e.left_inv.some n).trans
      (reducedSingularHomologyMap_id R n)
  inv_hom_id := by
    rw [← reducedSingularHomologyMap_comp]
    exact (reducedSingularHomologyMap_eq_of_homotopy R e.right_inv.some n).trans
      (reducedSingularHomologyMap_id R n)


@[simp]
theorem reducedSingularHomologyIso_hom (e : X ≃ₕ Y) (n : ℕ) :
    (reducedSingularHomologyIso R e n).hom =
      reducedSingularHomologyMap R (TopCat.ofHom e.toFun) n := rfl


@[simp]
theorem reducedSingularHomologyIso_inv (e : X ≃ₕ Y) (n : ℕ) :
    (reducedSingularHomologyIso R e n).inv =
      reducedSingularHomologyMap R (TopCat.ofHom e.invFun) n := rfl

variable (X)


def singularZeroProjection :
    ((TopCat.toSSet.obj X).chainComplex R).X 0 ⟶
      (TopCat.toSSet.obj X).homology R 0 :=
  ((TopCat.toSSet.obj X).chainComplex R).pOpcycles 0 ≫
    ((TopCat.toSSet.obj X).chainComplex R).isoHomologyι₀.inv

instance : Epi (singularZeroProjection R X) := by
  unfold singularZeroProjection
  infer_instance


@[reassoc (attr := simp)]
theorem ι_singularZeroProjection (σ : TopCat.toSSet.obj X _⦋0⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularZeroProjection R X =
      ((TopCat.toSSet.obj X).chainComplex R).liftCycles
        ((TopCat.toSSet.obj X).ιChainComplex σ) 0 (by simp) (by simp) ≫
        ((TopCat.toSSet.obj X).chainComplex R).homologyπ 0 := by
  apply (cancel_mono (((TopCat.toSSet.obj X).chainComplex R).homologyι 0)).mp
  simp only [singularZeroProjection, Category.assoc,
    HomologicalComplex.isoHomologyι_inv_hom_id, Category.comp_id,
    HomologicalComplex.homology_π_ι, HomologicalComplex.liftCycles_i_assoc]


@[reassoc (attr := simp)]
theorem singularZeroProjection_augmentation :
    singularZeroProjection R X ≫ (TopCat.toSSet.obj X).homology₀ε R =
      singularAugmentation R X := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_singularZeroProjection, Category.assoc, ι_singularAugmentation]
  exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
    (TopCat.toSSet.obj X) R σ

private def reducedZeroOpcyclesIso :
    ((augmentedSingularChainComplex R X).sc' 2 1 0).opcycles ≅
      (TopCat.toSSet.obj X).homology R 0 :=
  (((augmentedSingularChainComplex R X).sc' 2 1 0).isoOpcyclesOfIsColimit
    (((TopCat.toSSet.obj X).chainComplex R).sc' 1 0 0).opcyclesIsCokernel).symm ≪≫
      (((TopCat.toSSet.obj X).chainComplex R).opcyclesIsoSc' 1 0 0 (by simp) (by simp)).symm ≪≫
        ((TopCat.toSSet.obj X).chainComplex R).isoHomologyι₀.symm

private theorem reducedZeroOpcyclesIso_projection :
    ((augmentedSingularChainComplex R X).sc' 2 1 0).pOpcycles ≫
      (reducedZeroOpcyclesIso R X).hom = singularZeroProjection R X := by
  have h := ((augmentedSingularChainComplex R X).sc' 2 1 0).pOpcycles_π_isoOpcyclesOfIsColimit_inv
      (((TopCat.toSSet.obj X).chainComplex R).sc' 1 0 0).opcyclesIsCokernel
  change ((augmentedSingularChainComplex R X).sc' 2 1 0).pOpcycles ≫
    (((augmentedSingularChainComplex R X).sc' 2 1 0).isoOpcyclesOfIsColimit
      (((TopCat.toSSet.obj X).chainComplex R).sc' 1 0 0).opcyclesIsCokernel).inv =
        (((TopCat.toSSet.obj X).chainComplex R).sc' 1 0 0).pOpcycles at h
  have h' := congrArg (fun φ ↦ φ ≫
    (((TopCat.toSSet.obj X).chainComplex R).opcyclesIsoSc' 1 0 0 (by simp) (by simp)).inv ≫
      ((TopCat.toSSet.obj X).chainComplex R).isoHomologyι₀.inv) h
  have h'' := congrArg (fun φ ↦ φ ≫
      ((TopCat.toSSet.obj X).chainComplex R).isoHomologyι₀.inv)
    (((TopCat.toSSet.obj X).chainComplex R).pOpcycles_opcyclesIsoSc'_inv
      1 0 0 (by simp) (by simp))
  exact h'.trans (by simpa only [Category.assoc] using! h'')

private theorem reducedZeroOpcyclesIso_augmentation :
    ((augmentedSingularChainComplex R X).sc' 2 1 0).fromOpcycles =
      (reducedZeroOpcyclesIso R X).hom ≫ (TopCat.toSSet.obj X).homology₀ε R := by
  apply (cancel_epi ((augmentedSingularChainComplex R X).sc' 2 1 0).pOpcycles).mp
  change _ = (((augmentedSingularChainComplex R X).sc' 2 1 0).pOpcycles ≫
    (reducedZeroOpcyclesIso R X).hom) ≫ (TopCat.toSSet.obj X).homology₀ε R
  rw [ShortComplex.p_fromOpcycles,
    reducedZeroOpcyclesIso_projection]
  exact (singularZeroProjection_augmentation R X).symm

private def reducedZeroArrowIso :
    Arrow.mk ((augmentedSingularChainComplex R X).sc' 2 1 0).fromOpcycles ≅
      Arrow.mk ((TopCat.toSSet.obj X).homology₀ε R) :=
  Arrow.isoMk (reducedZeroOpcyclesIso R X) (Iso.refl R)
    (by simpa using! (reducedZeroOpcyclesIso_augmentation R X).symm)

private def reducedZeroKernelIso :
    ((augmentedSingularChainComplex R X).sc' 2 1 0).homology ≅
      kernel ((TopCat.toSSet.obj X).homology₀ε R) :=
  KernelFork.mapIsoOfIsLimit
    (kf := KernelFork.ofι ((augmentedSingularChainComplex R X).sc' 2 1 0).homologyι
      ((augmentedSingularChainComplex R X).sc' 2 1 0).homologyι_comp_fromOpcycles)
    (kf' := KernelFork.ofι (kernel.ι ((TopCat.toSSet.obj X).homology₀ε R))
      (kernel.condition ((TopCat.toSSet.obj X).homology₀ε R)))
    ((augmentedSingularChainComplex R X).sc' 2 1 0).homologyIsKernel
    (kernelIsKernel ((TopCat.toSSet.obj X).homology₀ε R))
    (reducedZeroArrowIso R X)

private theorem reducedZeroKernelIso_hom_ι :
    (reducedZeroKernelIso R X).hom ≫ kernel.ι ((TopCat.toSSet.obj X).homology₀ε R) =
    ((augmentedSingularChainComplex R X).sc' 2 1 0).homologyι ≫
      (reducedZeroOpcyclesIso R X).hom := by
  simp only [reducedZeroKernelIso, KernelFork.mapIsoOfIsLimit_hom]
  change _ ≫ (KernelFork.ofι (kernel.ι ((TopCat.toSSet.obj X).homology₀ε R))
    (kernel.condition ((TopCat.toSSet.obj X).homology₀ε R))).ι = _
  rw [KernelFork.mapOfIsLimit_ι]
  rfl

def reducedSingularHomologyZeroIso :
    reducedSingularHomology R X 0 ≅
      ModuleCat.of k (LinearMap.ker ((TopCat.toSSet.obj X).homology₀ε R).hom) :=
  (augmentedSingularChainComplex R X).homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    reducedZeroKernelIso R X ≪≫ ModuleCat.kernelIsoKer ((TopCat.toSSet.obj X).homology₀ε R)

@[reassoc]
private theorem reducedSingularHomologyZeroIso_π_subtype :
    (augmentedSingularChainComplex R X).homologyπ 1 ≫
      (reducedSingularHomologyZeroIso R X).hom ≫
      ModuleCat.ofHom (LinearMap.ker ((TopCat.toSSet.obj X).homology₀ε R).hom).subtype =
    (augmentedSingularChainComplex R X).iCycles 1 ≫ singularZeroProjection R X := by
  change _ ≫ (((augmentedSingularChainComplex R X).homologyIsoSc' 2 1 0
    (by simp) (by simp)).hom ≫ (reducedZeroKernelIso R X).hom ≫
      (ModuleCat.kernelIsoKer ((TopCat.toSSet.obj X).homology₀ε R)).hom) ≫ _ = _
  rw [Category.assoc, Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
    reducedZeroKernelIso_hom_ι]
  rw [HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.homology_π_ι_assoc]
  have h := congrArg (fun φ ↦
    ((augmentedSingularChainComplex R X).cyclesIsoSc' 2 1 0 (by simp) (by simp)).hom ≫
      ((augmentedSingularChainComplex R X).sc' 2 1 0).iCycles ≫ φ)
    (reducedZeroOpcyclesIso_projection R X)
  have h' := congrArg (fun φ ↦ φ ≫ singularZeroProjection R X)
    ((augmentedSingularChainComplex R X).cyclesIsoSc'_hom_iCycles 2 1 0 (by simp) (by simp))
  exact (h.trans (by simpa only [Category.assoc] using! h'))

@[reassoc]
theorem reducedSingularHomologyZeroIso_cycle {A : ModuleCat.{u} k}
    (c : A ⟶ ((TopCat.toSSet.obj X).chainComplex R).X 0)
    (hc : c ≫ singularAugmentation R X = 0) :
    (augmentedSingularChainComplex R X).liftCycles c 0 (by simp) hc ≫
      (augmentedSingularChainComplex R X).homologyπ 1 ≫
      (reducedSingularHomologyZeroIso R X).hom ≫
      ModuleCat.ofHom (LinearMap.ker ((TopCat.toSSet.obj X).homology₀ε R).hom).subtype =
    c ≫ singularZeroProjection R X := by
  rw [reducedSingularHomologyZeroIso_π_subtype]
  exact HomologicalComplex.liftCycles_i_assoc
    (augmentedSingularChainComplex R X) (i := 1) c 0 (by simp) hc (singularZeroProjection R X)

private def reducedPositiveShortComplexIso (n : ℕ) :
    (augmentedSingularChainComplex R X).sc' (n + 3) (n + 2) (n + 1) ≅
      ((TopCat.toSSet.obj X).chainComplex R).sc' (n + 2) (n + 1) n :=
  ShortComplex.isoMk
    (Iso.refl (((TopCat.toSSet.obj X).chainComplex R).X (n + 2)))
    (Iso.refl (((TopCat.toSSet.obj X).chainComplex R).X (n + 1)))
    (Iso.refl (((TopCat.toSSet.obj X).chainComplex R).X n))
    (by exact (show 𝟙 _ ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) =
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) ≫ 𝟙 _ from
      (Category.id_comp _).trans (Category.comp_id _).symm))
    (by exact (show 𝟙 _ ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n =
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫ 𝟙 _ from
      (Category.id_comp _).trans (Category.comp_id _).symm))

def reducedSingularHomologySuccIso (n : ℕ) :
    reducedSingularHomology R X (n + 1) ≅ (TopCat.toSSet.obj X).homology R (n + 1) :=
  (augmentedSingularChainComplex R X).homologyIsoSc' (n + 3) (n + 2) (n + 1)
    (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (reducedPositiveShortComplexIso R X n) ≪≫
      (((TopCat.toSSet.obj X).chainComplex R).homologyIsoSc' (n + 2) (n + 1) n
        (by simp) (by simp)).symm

theorem isZero_reducedSingularHomology_zero_of_pathConnected [PathConnectedSpace X] :
    IsZero (reducedSingularHomology R X 0) := by
  have hinj : Function.Injective ((TopCat.toSSet.obj X).homology₀ε R) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have : Subsingleton (LinearMap.ker ((TopCat.toSSet.obj X).homology₀ε R).hom) :=
    ⟨fun a b ↦ Subtype.ext (hinj (a.property.trans b.property.symm))⟩
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (reducedSingularHomologyZeroIso R X)

theorem isZero_reducedSingularHomology_of_isEmpty [IsEmpty X] (n : ℕ) :
    IsZero (reducedSingularHomology R X n) := by
  have hz : IsZero (((TopCat.toSSet.obj X).chainComplex R).X n) := by
    rw [IsZero.iff_id_eq_zero]
    apply SSet.chainComplex_hom_ext
    intro σ
    exact isEmptyElim ((X.toSSetObjEquiv _ σ) (stdSimplex.vertex 0))
  exact (HomologicalComplex.ExactAt.of_isZero
    (K := augmentedSingularChainComplex R X) (i := n + 1) hz).isZero_homology


theorem isZero_reducedSingularHomology_of_contractible [ContractibleSpace X] (n : ℕ) :
    IsZero (reducedSingularHomology R X n) := by
  let P : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let e : X ≃ₕ P := (ContractibleSpace.hequiv X P).some
  have hP : IsZero (reducedSingularHomology R P n) := by
    cases n with
    | zero => exact isZero_reducedSingularHomology_zero_of_pathConnected R P
    | succ n =>
      exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat.{u} k) (n + 1) R P (by simp)).of_iso
          (reducedSingularHomologySuccIso R P n)
  exact hP.of_iso (reducedSingularHomologyIso R e n)

variable {X}


@[reassoc]
theorem singularZeroProjection_naturality (f : X ⟶ Y) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) R).f 0 ≫ singularZeroProjection R Y =
      singularZeroProjection R X ≫ SSet.homologyMap (TopCat.toSSet.map f) R 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, ι_singularZeroProjection,
    ← Category.assoc, ι_singularZeroProjection]
  change _ = _ ≫ HomologicalComplex.homologyMap
    (SSet.chainComplexMap (TopCat.toSSet.map f) R) 0
  simp only [Category.assoc, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, SSet.ι_chainComplexMap_f]


@[reassoc]
theorem singularHomologyZeroAugmentation_naturality (f : X ⟶ Y) :
    SSet.homologyMap (TopCat.toSSet.map f) R 0 ≫ (TopCat.toSSet.obj Y).homology₀ε R =
      (TopCat.toSSet.obj X).homology₀ε R := by
  apply (cancel_epi (singularZeroProjection R X)).mp
  rw [← singularZeroProjection_naturality_assoc, singularZeroProjection_augmentation,
    singularAugmentation_naturality, singularZeroProjection_augmentation]

@[reassoc]
theorem reducedSingularHomologyZeroIso_naturality (f : X ⟶ Y) :
    reducedSingularHomologyMap R f 0 ≫ (reducedSingularHomologyZeroIso R Y).hom ≫
      ModuleCat.ofHom (LinearMap.ker ((TopCat.toSSet.obj Y).homology₀ε R).hom).subtype =
    (reducedSingularHomologyZeroIso R X).hom ≫
      ModuleCat.ofHom (LinearMap.ker ((TopCat.toSSet.obj X).homology₀ε R).hom).subtype ≫
        SSet.homologyMap (TopCat.toSSet.map f) R 0 := by
  apply (cancel_epi ((augmentedSingularChainComplex R X).homologyπ 1)).mp
  change _ ≫ HomologicalComplex.homologyMap (augmentedSingularChainMap R f) 1 ≫ _ = _
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    reducedSingularHomologyZeroIso_π_subtype]
  rw [reducedSingularHomologyZeroIso_π_subtype_assoc]
  have h := HomologicalComplex.cyclesMap_i_assoc (augmentedSingularChainMap R f) 1
    (singularZeroProjection R Y)
  have h' := congrArg (fun φ ↦ (augmentedSingularChainComplex R X).iCycles 1 ≫ φ)
    (singularZeroProjection_naturality R f)
  exact h.trans h'

end DifferentialGeometry.Homology
