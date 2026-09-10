import DifferentialGeometry.Topology.SphereSeparation.SphereCellularComparison
import DifferentialGeometry.Topology.SphereSeparation.SmallChainsPrism
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.Basis.Basic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Poincare.Topology.SphereSeparation




noncomputable def integerDualMap {M N : ModuleCat ℤ} (f : M ⟶ N) :
    ModuleCat.of ℤ (integerDual N) ⟶ ModuleCat.of ℤ (integerDual M) :=
  ModuleCat.ofHom (dualDifferential f)

@[simp]
theorem integerDualMap_id (M : ModuleCat ℤ) :
    integerDualMap (𝟙 M) = 𝟙 (ModuleCat.of ℤ (integerDual M)) := by
  ext φ x
  rfl

@[simp]
theorem integerDualMap_comp {M N P : ModuleCat ℤ} (f : M ⟶ N) (g : N ⟶ P) :
    integerDualMap (f ≫ g) = integerDualMap g ≫ integerDualMap f := by
  ext φ x
  rfl

@[simp]
theorem integerDualMap_zero {M N : ModuleCat ℤ} :
    integerDualMap (0 : M ⟶ N) = 0 := by
  ext φ x
  change φ (0 : N) = 0
  exact map_zero φ

@[simp]
theorem integerDualMap_add {M N : ModuleCat ℤ} (f g : M ⟶ N) :
    integerDualMap (f + g) = integerDualMap f + integerDualMap g := by
  ext φ x
  change φ (f x + g x) = φ (f x) + φ (g x)
  exact map_add φ _ _


noncomputable def integerDualShortComplex (S : ShortComplex (ModuleCat ℤ)) :
    ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk (integerDualMap S.g) (integerDualMap S.f) (by
    rw [← integerDualMap_comp, S.zero, integerDualMap_zero])


noncomputable def integerDualSplitting {S : ShortComplex (ModuleCat ℤ)}
    (s : S.Splitting) : (integerDualShortComplex S).Splitting where
  r := integerDualMap s.s
  s := integerDualMap s.r
  f_r := by
    dsimp [integerDualShortComplex]
    rw [← integerDualMap_comp, s.s_g, integerDualMap_id]
  s_g := by
    dsimp [integerDualShortComplex]
    rw [← integerDualMap_comp, s.f_r, integerDualMap_id]
  id := by
    dsimp [integerDualShortComplex]
    ext φ x
    change φ (s.s (S.g x)) + φ (S.f (s.r x)) = φ x
    rw [← map_add]
    apply congrArg φ
    have hx := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom s.id) x
    simpa [add_comm] using hx


theorem integerDualShortExact_of_splitting {S : ShortComplex (ModuleCat ℤ)}
    (s : S.Splitting) : (integerDualShortComplex S).ShortExact :=
  (integerDualSplitting s).shortExact

theorem integerSimplicialChainDegree_projective (Y : SSet) (n : ℕ) :
    CategoryTheory.Projective ((Y.chainComplex (ModuleCat.of ℤ ℤ)).X n) := by
  change CategoryTheory.Projective (∐ fun (_ : Y _⦋n⦌) => ModuleCat.of ℤ ℤ)
  let _ : CategoryTheory.Projective (ModuleCat.of ℤ ℤ) :=
    ModuleCat.projective_of_free (Module.Basis.singleton Unit ℤ)
  infer_instance

noncomputable def smallSingularChainsHomotopyEquivOfOpenCoverMV
    (X : TopCat) (V W : Set X)
    (hV : IsOpen V) (hW : IsOpen W) (hcover : V ∪ W = Set.univ) :
    HomotopyEquiv (smallSingularChainComplex X V W)
      (integerSingularChains X) := by
  letI (n : ℕ) : CategoryTheory.Projective
      ((smallSingularChainComplex X V W).X n) := by
    exact integerSimplicialChainDegree_projective
      (smallSingularSubcomplex X V W : SSet) n
  letI (n : ℕ) : CategoryTheory.Projective
      ((integerSingularChains X).X n) := by
    exact integerSimplicialChainDegree_projective (TopCat.toSSet.obj X) n
  have hq : QuasiIso (smallSingularChainInclusion X V W) :=
    quasiIso_smallSingularChainInclusion X V W hV hW hcover
  have hh := (ChainComplex.quasiIso_iff_of_projective
    (smallSingularChainInclusion X V W)).mp hq
  let e := Classical.choose hh
  have he := Classical.choose_spec hh
  exact e.copy (_root_.Homotopy.ofEq he)

@[simp]
theorem dualCochainMap_zero
    {C D : ChainComplex (ModuleCat ℤ) ℕ} :
    dualCochainMap (0 : C ⟶ D) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  dsimp [dualCochainMap, dualCochainComplex]
  ext φ x
  change φ (0 : D.X n) = 0
  exact map_zero φ

@[simp]
theorem dualCochainMap_add
    {C D : ChainComplex (ModuleCat ℤ) ℕ} (f g : C ⟶ D) :
    dualCochainMap (f + g) = dualCochainMap f + dualCochainMap g := by
  apply HomologicalComplex.hom_ext
  intro n
  dsimp [dualCochainMap, dualCochainComplex]
  ext φ x
  change φ (f.f n x + g.f n x) = φ (f.f n x) + φ (g.f n x)
  exact map_add φ _ _

noncomputable def dualCochainShortComplex
    (S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (dualCochainMap S.g) (dualCochainMap S.f) (by
    rw [← dualCochainMap_comp, S.zero, dualCochainMap_zero])

theorem dualCochainShortComplex_shortExact_of_degreewise_projective
    {S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}
    (hS : S.ShortExact)
    (hprojective : ∀ n, CategoryTheory.Projective (S.X₃.X n)) :
    (dualCochainShortComplex S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let F := HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n
  let _ : CategoryTheory.Projective ((S.map F).X₃) := hprojective n
  let s := (hS.map_of_exact F).splittingOfProjective
  change (integerDualShortComplex
    (S.map (HomologicalComplex.eval (ModuleCat ℤ)
      (ComplexShape.down ℕ) n))).ShortExact
  exact integerDualShortExact_of_splitting s

noncomputable def dualCochainBiprodIso
    (C D : ChainComplex (ModuleCat ℤ) ℕ) :
    dualCochainComplex (C ⊞ D) ≅
      dualCochainComplex C ⊞ dualCochainComplex D where
  hom := biprod.lift (dualCochainMap biprod.inl) (dualCochainMap biprod.inr)
  inv := biprod.desc (dualCochainMap biprod.fst) (dualCochainMap biprod.snd)
  hom_inv_id := by
    rw [biprod.lift_desc, ← dualCochainMap_comp,
      ← dualCochainMap_comp, ← dualCochainMap_add,
      biprod.total, dualCochainMap_id]
  inv_hom_id := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.lift_fst, biprod.desc_eq,
        Preadditive.add_comp]
      simp only [Category.assoc, ← dualCochainMap_comp,
        biprod.inl_fst, dualCochainMap_id]
      rw [show (biprod.inl : C ⟶ C ⊞ D) ≫ biprod.snd = 0 by simp,
        dualCochainMap_zero, comp_zero, add_zero, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, biprod.lift_snd, biprod.desc_eq,
        Preadditive.add_comp]
      simp only [Category.assoc, ← dualCochainMap_comp,
        biprod.inr_snd, dualCochainMap_id]
      rw [show (biprod.inr : D ⟶ C ⊞ D) ≫ biprod.fst = 0 by simp,
        dualCochainMap_zero, comp_zero, zero_add, Category.comp_id,
        Category.id_comp]



noncomputable def subspaceMayerVietorisCochainSequence
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  dualCochainShortComplex
    (integerSingularChains_isPushout_subspaces A B).shortComplex

theorem subspaceMayerVietorisCochainSequence_shortExact
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (subspaceMayerVietorisCochainSequence A B).ShortExact := by
  apply dualCochainShortComplex_shortExact_of_degreewise_projective
    (integerSingularChains_mayerVietoris_shortExact_subspaces A B)
  intro n
  change CategoryTheory.Projective
    (((((singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B)) :
      (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet).chainComplex
        (ModuleCat.of ℤ ℤ)).X n)
  exact integerSimplicialChainDegree_projective _ n

noncomputable def subspaceMayerVietorisMiddleCochainIso
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (subspaceMayerVietorisCochainSequence A B).X₂ ≅
      singularCochainComplex (TopCat.of A) ⊞
        singularCochainComplex (TopCat.of B) :=
  dualCochainBiprodIso
    (integerSingularChains (TopCat.of A))
    (integerSingularChains (TopCat.of B))

noncomputable abbrev smallSubspaceUnionCohomology
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ) : ModuleCat ℤ :=
  (subspaceMayerVietorisCochainSequence A B).X₁.homology n

noncomputable def smallSubspaceUnionCohomologyIsoOfOpenCover
    (X : TopCat) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (n : ℕ) :
    smallSubspaceUnionCohomology A B n ≅ singularCohomology X n :=
  (dualCochainHomotopyEquiv
    (smallSingularChainsHomotopyEquivOfOpenCoverMV
      X A B hA hB hcover)).symm.toHomologyIso n


noncomputable abbrev subspaceMayerVietorisMiddleCohomology
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ) : ModuleCat ℤ :=
  (subspaceMayerVietorisCochainSequence A B).X₂.homology n

noncomputable def subspaceMayerVietorisMiddleCohomologyIso
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ) :
    subspaceMayerVietorisMiddleCohomology A B n ≅
      singularCohomology (TopCat.of A) n ⊞
        singularCohomology (TopCat.of B) n := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℤ)
    (ComplexShape.up ℕ) n
  let _ : F.Additive := inferInstance
  let _ : PreservesFiniteBiproducts F :=
    Functor.preservesFiniteBiproductsOfAdditive F
  let _ : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  exact F.mapIso (subspaceMayerVietorisMiddleCochainIso A B) ≪≫
    F.mapBiprod
      (singularCochainComplex (TopCat.of A))
      (singularCochainComplex (TopCat.of B))

theorem isZero_subspaceMayerVietorisMiddleCohomology
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ)
    (hA : IsZero (singularCohomology (TopCat.of A) n))
    (hB : IsZero (singularCohomology (TopCat.of B) n)) :
    IsZero (subspaceMayerVietorisMiddleCohomology A B n) := by
  apply IsZero.of_iso _ (subspaceMayerVietorisMiddleCohomologyIso A B n)
  exact (biprod_isZero_iff _ _).2 ⟨hA, hB⟩



private theorem mvDualAlternatingConst_d_zero_one :
    (dualCochainComplex
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ))).d 0 1 = 0 := by
  change ModuleCat.ofHom (dualDifferential
    ((ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ)).d 1 0)) = 0
  rw [show
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ)).d 1 0 = 0 by
        rw [ChainComplex.alternatingConst]
        rw [HomologicalComplex.alternatingConst_d]
        simp [show ¬ Even 1 by rintro ⟨k, hk⟩; omega]
        rfl]
  ext φ
  simp [dualDifferential]

private theorem mvDualAlternatingConst_d_one_two :
    (dualCochainComplex
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ))).d 1 2 =
        𝟙 (ModuleCat.of ℤ (integerDual (ModuleCat.of ℤ ℤ))) := by
  ext φ
  rfl

private theorem mvDualAlternatingConst_exactAt_one :
    (dualCochainComplex
      (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ))).ExactAt 1 := by
  let K := dualCochainComplex
    (ChainComplex.alternatingConst.obj (ModuleCat.of ℤ ℤ))
  rw [K.exactAt_iff' 0 1 2 (CochainComplex.prev_nat_succ 0)
    (CochainComplex.next ℕ 1)]
  have hf : (K.sc' 0 1 2).f = 0 := by
    change K.d 0 1 = 0
    exact mvDualAlternatingConst_d_zero_one
  exact (ShortComplex.exact_iff_mono _ hf).2 (by
    have hmono : Mono
        (𝟙 (ModuleCat.of ℤ (integerDual (ModuleCat.of ℤ ℤ)))) := by
      infer_instance
    change Mono (K.d 1 2)
    rw [mvDualAlternatingConst_d_one_two]
    exact hmono)

theorem isZero_singularCohomology_punit_one :
    IsZero (singularCohomology (TopCat.of PUnit) 1) := by
  have hexact : (singularCochainComplex (TopCat.of PUnit)).ExactAt 1 :=
    mvDualAlternatingConst_exactAt_one.of_iso
      singularCochainComplexPUnitIsoDualAlternatingConst.symm
  exact hexact.isZero_homology

theorem isZero_singularCohomology_one_of_contractible
    (Y : Type) [TopologicalSpace Y] [ContractibleSpace Y] :
    IsZero (singularCohomology (TopCat.of Y) 1) := by
  have hUnit : IsZero (singularCohomology (TopCat.of Unit) 1) :=
    IsZero.of_iso isZero_singularCohomology_punit_one
      (singularCohomologyIsoOfHomeomorph
        (Homeomorph.homeomorphOfUnique Unit PUnit) 1).symm
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit Y
  exact IsZero.of_iso hUnit
    (singularCohomologyIsoOfHomotopyEquiv e 1).symm

noncomputable def subspaceMayerVietorisOverlapCochainIso
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (subspaceMayerVietorisCochainSequence A B).X₃ ≅
      singularCochainComplex (TopCat.of (A ∩ B : Set X)) :=
  Iso.refl _

noncomputable def subspaceMayerVietorisConnecting
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ) :
    (subspaceMayerVietorisCochainSequence A B).X₃.homology n ⟶
      smallSubspaceUnionCohomology A B (n + 1) :=
  (subspaceMayerVietorisCochainSequence_shortExact A B).δ n (n + 1) (by simp)

@[reassoc (attr := simp)]
theorem subspaceMayerVietorisConnecting_comp
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ) :
    subspaceMayerVietorisConnecting A B n ≫
        HomologicalComplex.homologyMap
          (subspaceMayerVietorisCochainSequence A B).f (n + 1) = 0 := by
  exact (subspaceMayerVietorisCochainSequence_shortExact A B).δ_comp
    n (n + 1) (by simp)

@[reassoc (attr := simp)]
theorem subspaceMayerVietoris_comp_connecting
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ) :
    HomologicalComplex.homologyMap
        (subspaceMayerVietorisCochainSequence A B).g n ≫
      subspaceMayerVietorisConnecting A B n = 0 := by
  exact (subspaceMayerVietorisCochainSequence_shortExact A B).comp_δ
    n (n + 1) (by simp)

theorem subspaceMayerVietoris_exact_at_overlap
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (subspaceMayerVietorisCochainSequence A B).g n)
      (subspaceMayerVietorisConnecting A B n)
      (subspaceMayerVietoris_comp_connecting A B n)).Exact := by
  exact (subspaceMayerVietorisCochainSequence_shortExact A B).homology_exact₃
    n (n + 1) (by simp)

theorem subspaceMayerVietoris_exact_at_smallUnion
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ) :
    (ShortComplex.mk
      (subspaceMayerVietorisConnecting A B n)
      (HomologicalComplex.homologyMap
        (subspaceMayerVietorisCochainSequence A B).f (n + 1))
      (subspaceMayerVietorisConnecting_comp A B n)).Exact := by
  exact (subspaceMayerVietorisCochainSequence_shortExact A B).homology_exact₁
    n (n + 1) (by simp)


theorem subspaceMayerVietoris_exact_at_middle
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (subspaceMayerVietorisCochainSequence A B).f n)
      (HomologicalComplex.homologyMap
        (subspaceMayerVietorisCochainSequence A B).g n)
      (by
        rw [← HomologicalComplex.homologyMap_comp,
          (subspaceMayerVietorisCochainSequence A B).zero,
          HomologicalComplex.homologyMap_zero])).Exact := by
  exact (subspaceMayerVietorisCochainSequence_shortExact A B).homology_exact₂ n

noncomputable def subspaceMayerVietorisConnectingIso
    {X : Type} [TopologicalSpace X] (A B : Set X) (n : ℕ)
    (hn : IsZero (subspaceMayerVietorisMiddleCohomology A B n))
    (hn1 : IsZero (subspaceMayerVietorisMiddleCohomology A B (n + 1))) :
    (subspaceMayerVietorisCochainSequence A B).X₃.homology n ≅
      smallSubspaceUnionCohomology A B (n + 1) :=
  (subspaceMayerVietorisCochainSequence_shortExact A B).δIso
    n (n + 1) (by simp) hn hn1

noncomputable def subspaceMayerVietorisHOneToHTwoIso
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (h1 : IsZero (subspaceMayerVietorisMiddleCohomology A B 1))
    (h2 : IsZero (subspaceMayerVietorisMiddleCohomology A B 2)) :
    (subspaceMayerVietorisCochainSequence A B).X₃.homology 1 ≅
      smallSubspaceUnionCohomology A B 2 :=
  subspaceMayerVietorisConnectingIso A B 1 h1 h2

noncomputable def subspaceMayerVietorisHOneToHTwoIsoOfMemberVanishing
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA1 : IsZero (singularCohomology (TopCat.of A) 1))
    (hB1 : IsZero (singularCohomology (TopCat.of B) 1))
    (hA2 : IsZero (singularCohomology (TopCat.of A) 2))
    (hB2 : IsZero (singularCohomology (TopCat.of B) 2)) :
    singularCohomology (TopCat.of (A ∩ B : Set X)) 1 ≅
      smallSubspaceUnionCohomology A B 2 :=
  ((HomologicalComplex.homologyFunctor (ModuleCat ℤ)
      (ComplexShape.up ℕ) 1).mapIso
        (subspaceMayerVietorisOverlapCochainIso A B)).symm ≪≫
    subspaceMayerVietorisHOneToHTwoIso A B
      (isZero_subspaceMayerVietorisMiddleCohomology A B 1 hA1 hB1)
      (isZero_subspaceMayerVietorisMiddleCohomology A B 2 hA2 hB2)

noncomputable def subspaceMayerVietorisHOneToHTwoIsoOfContractible
    {X : Type} [TopologicalSpace X] (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B] :
    singularCohomology (TopCat.of (A ∩ B : Set X)) 1 ≅
      smallSubspaceUnionCohomology A B 2 :=
  subspaceMayerVietorisHOneToHTwoIsoOfMemberVanishing A B
    (isZero_singularCohomology_one_of_contractible A)
    (isZero_singularCohomology_one_of_contractible B)
    (isZero_singularCohomology_two_of_contractible A)
    (isZero_singularCohomology_two_of_contractible B)

noncomputable def subspaceMayerVietorisHOneToHTwoIsoOfContractibleOpenCover
    (X : TopCat) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ) :
    singularCohomology (TopCat.of (A ∩ B : Set X)) 1 ≅
      singularCohomology X 2 :=
  subspaceMayerVietorisHOneToHTwoIsoOfContractible A B ≪≫
    smallSubspaceUnionCohomologyIsoOfOpenCover X A B hA hB hcover 2

noncomputable def subspaceMayerVietorisHTwoIsoOfOverlap
    (X : TopCat) (A B : Set X) (G : ModuleCat ℤ)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (hOverlap : singularCohomology (TopCat.of (A ∩ B : Set X)) 1 ≅ G) :
    singularCohomology X 2 ≅ G :=
  (subspaceMayerVietorisHOneToHTwoIsoOfContractibleOpenCover
    X A B hA hB hcover).symm ≪≫ hOverlap

noncomputable def subspaceMayerVietorisHTwoIsoIntOfOverlap
    (X : TopCat) (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = Set.univ)
    (hOverlap : singularCohomology (TopCat.of (A ∩ B : Set X)) 1 ≅
      ModuleCat.of ℤ ℤ) :
    singularCohomology X 2 ≅ ModuleCat.of ℤ ℤ :=
  subspaceMayerVietorisHTwoIsoOfOverlap X A B (ModuleCat.of ℤ ℤ)
    hA hB hcover hOverlap

end Poincare.Topology.SphereSeparation
