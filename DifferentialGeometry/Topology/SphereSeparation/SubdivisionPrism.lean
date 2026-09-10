import DifferentialGeometry.Topology.SphereSeparation.SubdivisionBoundary
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open Simplicial
open scoped Simplicial

namespace DifferentialGeometry.Topology.SphereSeparation

private noncomputable abbrev PrismChains (X : TopCat) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X

noncomputable def signedBarycentricSubdivisionChainEndomorphism (X : TopCat) :
    PrismChains X ⟶ PrismChains X :=
  barycentricSubdivisionChainEndomorphism X
    (barycentricSubdivisionBoundaryCompatible X)

private noncomputable def prismChainHomotopyEquivOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    HomotopyEquiv (PrismChains (TopCat.of X))
      (PrismChains (TopCat.of Y)) where
  hom := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom e.toFun)
  inv := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    rw [← Functor.map_comp]
    let H := Classical.choice e.left_inv
    let H' : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun)
        (𝟙 (TopCat.of X)) := H
    exact (TopCat.Homotopy.singularChainComplexFunctorObjMap H'
      (ModuleCat.of ℤ ℤ)).trans (_root_.Homotopy.ofEq
        (CategoryTheory.Functor.map_id
          ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)) (TopCat.of X)))
  homotopyInvHomId := by
    rw [← Functor.map_comp]
    let H := Classical.choice e.right_inv
    let H' : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun)
        (𝟙 (TopCat.of Y)) := H
    exact (TopCat.Homotopy.singularChainComplexFunctorObjMap H'
      (ModuleCat.of ℤ ℤ)).trans (_root_.Homotopy.ofEq
        (CategoryTheory.Functor.map_id
          ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
            (ModuleCat.of ℤ ℤ)) (TopCat.of Y)))

private noncomputable def prismChainsPUnitHomotopyEquivSingleZero :
    HomotopyEquiv (PrismChains (TopCat.of PUnit))
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj
        (ModuleCat.of ℤ ℤ)) :=
  (HomotopyEquiv.ofIso
    ((AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) (TopCat.of PUnit)) ≪≫
      ChainComplex.alternatingConst.mapIso
        (coproductUniqueIso (fun _ : PUnit => ModuleCat.of ℤ ℤ)))).trans
    (ChainComplex.alternatingConstHomotopyEquiv (ModuleCat.of ℤ ℤ))

noncomputable def standardSimplexChainsHomotopyEquivSingleZero (n : ℕ) :
    HomotopyEquiv
      (PrismChains (TopCat.of (stdSimplex ℝ (Fin (n + 1)))))
      ((HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.down ℕ) 0).obj
        (ModuleCat.of ℤ ℤ)) := by
  letI : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨stdSimplex.barycenter, stdSimplex.barycenter.property⟩
  let e : ContinuousMap.HomotopyEquiv
      (stdSimplex ℝ (Fin (n + 1))) PUnit :=
    (Classical.choice
      (ContractibleSpace.hequiv_unit (stdSimplex ℝ (Fin (n + 1))))).trans
      (Homeomorph.homeomorphOfUnique Unit PUnit).toHomotopyEquiv
  exact (prismChainHomotopyEquivOfHomotopyEquiv e).trans
    prismChainsPUnitHomotopyEquivSingleZero

noncomputable def standardSimplexPositiveContraction (n : ℕ) :
    _root_.Homotopy
      (𝟙 (PrismChains (TopCat.of (stdSimplex ℝ (Fin (n + 1))))))
      ((standardSimplexChainsHomotopyEquivSingleZero n).hom ≫
        (standardSimplexChainsHomotopyEquivSingleZero n).inv) :=
  (standardSimplexChainsHomotopyEquivSingleZero n).homotopyHomInvId.symm

theorem standardSimplexProjection_f_succ (n k : ℕ) :
    (((standardSimplexChainsHomotopyEquivSingleZero n).hom ≫
      (standardSimplexChainsHomotopyEquivSingleZero n).inv).f (k + 1)) = 0 := by
  change (standardSimplexChainsHomotopyEquivSingleZero n).hom.f (k + 1) ≫
    (standardSimplexChainsHomotopyEquivSingleZero n).inv.f (k + 1) = 0
  rw [show (standardSimplexChainsHomotopyEquivSingleZero n).hom.f (k + 1) = 0 by
    apply (HomologicalComplex.isZero_single_obj_X
      (ComplexShape.down ℕ) 0 (ModuleCat.of ℤ ℤ) (k + 1) (by omega)).eq_of_tgt]
  simp

theorem standardSimplexPositiveContraction_fillsCycle
    (n k : ℕ)
    (z : ModuleCat.of ℤ ℤ ⟶
      (PrismChains (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).X (k + 1))
    (hz : z ≫
      (PrismChains (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).d
        (k + 1) k = 0) :
    z ≫ (standardSimplexPositiveContraction n).hom (k + 1) (k + 2) ≫
        (PrismChains (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).d
          (k + 2) (k + 1) = z := by
  have h := congr_arg (fun q => z ≫ q)
    ((standardSimplexPositiveContraction n).comm (k + 1))
  rw [Homotopy.dNext_succ_chainComplex,
    Homotopy.prevD_chainComplex,
    standardSimplexProjection_f_succ] at h
  simp only [HomologicalComplex.id_f, Category.comp_id,
    Preadditive.comp_add, add_zero] at h
  rw [← Category.assoc, hz, zero_comp, zero_add] at h
  simpa only [Category.assoc, Nat.add_comm] using h.symm



noncomputable def standardSimplexIdentitySingularSimplex (n : ℕ) :
    (TopCat.toSSet.obj (TopCat.of (stdSimplex ℝ (Fin (n + 1))))) _⦋n⦌ :=
  ((TopCat.of (stdSimplex ℝ (Fin (n + 1)))).toSSetObjEquiv _).symm
    (ContinuousMap.id _)


noncomputable def singularSimplexRealizationMap
    (X : TopCat) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    TopCat.of (stdSimplex ℝ (Fin (n + 1))) ⟶ X :=
  TopCat.ofHom (X.toSSetObjEquiv _ s)

@[simp]
theorem toSSet_map_standardSimplexIdentitySingularSimplex
    (X : TopCat) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map (singularSimplexRealizationMap X s)).app _
        (standardSimplexIdentitySingularSimplex n) = s := by
  apply (X.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro x
  rfl

theorem singularSimplexRealizationMap_naturality
    {X Y : TopCat} (f : X ⟶ Y) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularSimplexRealizationMap Y ((TopCat.toSSet.map f).app _ s) =
      singularSimplexRealizationMap X s ≫ f := by
  ext x
  rfl

theorem chainComplexMap_singularSimplexRealizationMap_naturality
    {X Y : TopCat} (f : X ⟶ Y) {n q : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (SSet.chainComplexMap
        (TopCat.toSSet.map (singularSimplexRealizationMap X s))
        (ModuleCat.of ℤ ℤ)).f q ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f)
        (ModuleCat.of ℤ ℤ)).f q =
      (SSet.chainComplexMap
        (TopCat.toSSet.map (singularSimplexRealizationMap Y
          ((TopCat.toSSet.map f).app _ s)))
        (ModuleCat.of ℤ ℤ)).f q := by
  rw [singularSimplexRealizationMap_naturality]
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp,
    ← Functor.map_comp]

@[reassoc (attr := simp)]
theorem ι_standardSimplex_comp_singularSimplexRealizationMap
    (X : TopCat) {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj
      (TopCat.of (stdSimplex ℝ (Fin (n + 1))))).ιChainComplex
        (R := ModuleCat.of ℤ ℤ)
          (standardSimplexIdentitySingularSimplex n) ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (singularSimplexRealizationMap X s))
        (ModuleCat.of ℤ ℤ)).f n =
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s := by
  rw [SSet.ι_chainComplexMap_f,
    toSSet_map_standardSimplexIdentitySingularSimplex]


noncomputable def signedBarycentricSubdivisionDifference (X : TopCat) :
    PrismChains X ⟶ PrismChains X :=
  signedBarycentricSubdivisionChainEndomorphism X - 𝟙 _

theorem signedBarycentricSubdivisionDifference_naturality
    {X Y : TopCat} (f : X ⟶ Y) :
    signedBarycentricSubdivisionDifference X ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f =
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map f ≫
        signedBarycentricSubdivisionDifference Y := by
  rw [signedBarycentricSubdivisionDifference,
    signedBarycentricSubdivisionDifference,
    Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id]
  congr 1
  exact barycentricSubdivisionChainEndomorphism_naturality f
    (barycentricSubdivisionBoundaryCompatible X)
    (barycentricSubdivisionBoundaryCompatible Y)

private noncomputable def successorPrismModelError
    (k : ℕ)
    (previous : ∀ X : TopCat, (PrismChains X).X k ⟶
      (PrismChains X).X (k + 1)) :
    ModuleCat.of ℤ ℤ ⟶
      (PrismChains
        (TopCat.of (stdSimplex ℝ (Fin (k + 2))))).X (k + 1) :=
  let Δ := TopCat.of (stdSimplex ℝ (Fin (k + 2)))
  (TopCat.toSSet.obj Δ).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      (standardSimplexIdentitySingularSimplex (k + 1)) ≫
        (signedBarycentricSubdivisionDifference Δ).f (k + 1) -
    ((TopCat.toSSet.obj Δ).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (standardSimplexIdentitySingularSimplex (k + 1)) ≫
      (PrismChains Δ).d (k + 1) k ≫ previous Δ)

noncomputable def barycentricSubdivisionPrismComponent :
    (n : ℕ) → (X : TopCat) →
      (PrismChains X).X n ⟶ (PrismChains X).X (n + 1) :=
  fun n => match n with
  | 0 => fun _ => 0
  | k + 1 => fun X =>
      Sigma.desc fun s =>
        successorPrismModelError k (barycentricSubdivisionPrismComponent k) ≫
          (standardSimplexPositiveContraction (k + 1)).hom
            (k + 1) (k + 2) ≫
          (SSet.chainComplexMap
            (TopCat.toSSet.map (singularSimplexRealizationMap X s))
            (ModuleCat.of ℤ ℤ)).f (k + 2)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_barycentricSubdivisionPrismComponent_zero
    (X : TopCat) (s : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s ≫
      barycentricSubdivisionPrismComponent 0 X = 0 := by
  change _ ≫ (0 : (PrismChains X).X 0 ⟶ (PrismChains X).X 1) = 0
  rw [comp_zero]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_barycentricSubdivisionPrismComponent_succ
    (X : TopCat) (k : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋k + 1⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s ≫
        barycentricSubdivisionPrismComponent (k + 1) X =
      successorPrismModelError k (barycentricSubdivisionPrismComponent k) ≫
        (standardSimplexPositiveContraction (k + 1)).hom
          (k + 1) (k + 2) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map (singularSimplexRealizationMap X s))
          (ModuleCat.of ℤ ℤ)).f (k + 2) := by
  dsimp [barycentricSubdivisionPrismComponent, SSet.ιChainComplex]
  rw [Sigma.ι_desc]

set_option backward.isDefEq.respectTransparency false in
theorem barycentricSubdivisionPrismComponent_naturality
    (n : ℕ) {X Y : TopCat} (f : X ⟶ Y) :
    barycentricSubdivisionPrismComponent n X ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f)
          (ModuleCat.of ℤ ℤ)).f (n + 1) =
      (SSet.chainComplexMap (TopCat.toSSet.map f)
          (ModuleCat.of ℤ ℤ)).f n ≫
        barycentricSubdivisionPrismComponent n Y := by
  induction n with
  | zero =>
      simp [barycentricSubdivisionPrismComponent]
  | succ k ih =>
      apply SSet.chainComplex_hom_ext
      intro s
      rw [← Category.assoc,
        ι_barycentricSubdivisionPrismComponent_succ]
      conv_rhs =>
        rw [← Category.assoc, SSet.ι_chainComplexMap_f,
          ι_barycentricSubdivisionPrismComponent_succ]
      simp only [Category.assoc]
      rw [chainComplexMap_singularSimplexRealizationMap_naturality]

set_option backward.isDefEq.respectTransparency false in
theorem ι_map_barycentricSubdivisionPrismComponent
    {A X : TopCat} (f : A ⟶ X) (n : ℕ)
    (t : (TopCat.toSSet.obj A) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map f).app _ t) ≫
        barycentricSubdivisionPrismComponent n X =
      ((TopCat.toSSet.obj A).ιChainComplex (R := ModuleCat.of ℤ ℤ) t ≫
          barycentricSubdivisionPrismComponent n A) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f)
          (ModuleCat.of ℤ ℤ)).f (n + 1) := by
  rw [← SSet.ι_chainComplexMap_f]
  simp only [Category.assoc]
  rw [← barycentricSubdivisionPrismComponent_naturality n f]

private noncomputable def barycentricSubdivisionPrismHomOfRel
    (X : TopCat) (i j : ℕ) (hji : (ComplexShape.down ℕ).Rel j i) :
    (PrismChains X).X i ⟶ (PrismChains X).X j := by
  have h : i + 1 = j := by simpa using hji
  subst j
  exact barycentricSubdivisionPrismComponent i X

@[simp]
private theorem barycentricSubdivisionPrismHomOfRel_succ
    (X : TopCat) (i : ℕ)
    (h : (ComplexShape.down ℕ).Rel (i + 1) i) :
    barycentricSubdivisionPrismHomOfRel X i (i + 1) h =
      barycentricSubdivisionPrismComponent i X := by
  unfold barycentricSubdivisionPrismHomOfRel
  rfl

noncomputable def barycentricSubdivisionPrismNullMap (X : TopCat) :
    PrismChains X ⟶ PrismChains X :=
  Homotopy.nullHomotopicMap'
    (barycentricSubdivisionPrismHomOfRel X)

theorem barycentricSubdivisionPrismNullMap_f_zero (X : TopCat) :
    (barycentricSubdivisionPrismNullMap X).f 0 = 0 := by
  rw [barycentricSubdivisionPrismNullMap,
    Homotopy.nullHomotopicMap'_f_of_not_rel_left
      (show (ComplexShape.down ℕ).Rel 1 0 by simp)
      (show ∀ l : ℕ, ¬(ComplexShape.down ℕ).Rel 0 l by simp)]
  rw [barycentricSubdivisionPrismHomOfRel_succ]
  change (0 : (PrismChains X).X 0 ⟶ (PrismChains X).X 1) ≫
    (PrismChains X).d 1 0 = 0
  simp

theorem barycentricSubdivisionPrismNullMap_f_succ
    (X : TopCat) (k : ℕ) :
    (barycentricSubdivisionPrismNullMap X).f (k + 1) =
      (PrismChains X).d (k + 1) k ≫
          barycentricSubdivisionPrismComponent k X +
        barycentricSubdivisionPrismComponent (k + 1) X ≫
          (PrismChains X).d (k + 2) (k + 1) := by
  rw [barycentricSubdivisionPrismNullMap,
    Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) by simp)
      (show (ComplexShape.down ℕ).Rel (k + 1) k by simp)]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem successorPrismModelError_comp_d_eq_zero
    (k : ℕ)
    (ih : ∀ X : TopCat,
      (signedBarycentricSubdivisionDifference X).f k =
        (barycentricSubdivisionPrismNullMap X).f k) :
    successorPrismModelError k (barycentricSubdivisionPrismComponent k) ≫
      (PrismChains
        (TopCat.of (stdSimplex ℝ (Fin (k + 2))))).d (k + 1) k = 0 := by
  let Δ := TopCat.of (stdSimplex ℝ (Fin (k + 2)))
  let ιΔ : ModuleCat.of ℤ ℤ ⟶ (PrismChains Δ).X (k + 1) :=
    (TopCat.toSSet.obj Δ).ιChainComplex
      (R := ModuleCat.of ℤ ℤ)
      (standardSimplexIdentitySingularSimplex (k + 1))
  change ((ιΔ ≫ (signedBarycentricSubdivisionDifference Δ).f (k + 1)) -
      (ιΔ ≫ (PrismChains Δ).d (k + 1) k ≫
        barycentricSubdivisionPrismComponent k Δ)) ≫
        (PrismChains Δ).d (k + 1) k = 0
  rw [Preadditive.sub_comp]
  simp only [Category.assoc]
  rw [(signedBarycentricSubdivisionDifference Δ).comm (k + 1) k,
    ih Δ]
  rw [← (barycentricSubdivisionPrismNullMap Δ).comm (k + 1) k]
  rw [barycentricSubdivisionPrismNullMap_f_succ]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
  rw [(PrismChains Δ).d_comp_d]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem signedBarycentricSubdivisionDifference_f_eq_prismNullMap_f
    (n : ℕ) (X : TopCat) :
    (signedBarycentricSubdivisionDifference X).f n =
      (barycentricSubdivisionPrismNullMap X).f n := by
  induction n generalizing X with
  | zero =>
      rw [barycentricSubdivisionPrismNullMap_f_zero]
      simp [signedBarycentricSubdivisionDifference,
        signedBarycentricSubdivisionChainEndomorphism,
        barycentricSubdivisionChainEndomorphism_f_zero]
  | succ k ih =>
      rw [barycentricSubdivisionPrismNullMap_f_succ]
      apply SSet.chainComplex_hom_ext
      intro s
      rw [Preadditive.comp_add]
      let Δ := TopCat.of (stdSimplex ℝ (Fin (k + 1 + 1)))
      let F : PrismChains Δ ⟶ PrismChains X :=
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
          (ModuleCat.of ℤ ℤ)).map (singularSimplexRealizationMap X s)
      let ιΔ : ModuleCat.of ℤ ℤ ⟶ (PrismChains Δ).X (k + 1) :=
        (TopCat.toSSet.obj Δ).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          (standardSimplexIdentitySingularSimplex (k + 1))
      let z : ModuleCat.of ℤ ℤ ⟶ (PrismChains Δ).X (k + 1) :=
        successorPrismModelError k
          (barycentricSubdivisionPrismComponent k)
      have hι : ιΔ ≫ F.f (k + 1) =
          (TopCat.toSSet.obj X).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) s := by
        exact ι_standardSimplex_comp_singularSimplexRealizationMap X s
      have hdiff :
          (signedBarycentricSubdivisionDifference Δ).f (k + 1) ≫
              F.f (k + 1) =
            F.f (k + 1) ≫
              (signedBarycentricSubdivisionDifference X).f (k + 1) := by
        have h := congr_arg (fun q => q.f (k + 1))
          (signedBarycentricSubdivisionDifference_naturality
            (singularSimplexRealizationMap X s))
        simpa only [HomologicalComplex.comp_f] using h
      have hlower :
          (TopCat.toSSet.obj X).ιChainComplex
                (R := ModuleCat.of ℤ ℤ) s ≫
              (PrismChains X).d (k + 1) k ≫
              barycentricSubdivisionPrismComponent k X =
            (ιΔ ≫ (PrismChains Δ).d (k + 1) k ≫
                barycentricSubdivisionPrismComponent k Δ) ≫
              F.f (k + 1) := by
        have hnat :
            F.f k ≫ barycentricSubdivisionPrismComponent k X =
              barycentricSubdivisionPrismComponent k Δ ≫ F.f (k + 1) := by
          change
            (SSet.chainComplexMap
                (TopCat.toSSet.map (singularSimplexRealizationMap X s))
                (ModuleCat.of ℤ ℤ)).f k ≫
                  barycentricSubdivisionPrismComponent k X =
              barycentricSubdivisionPrismComponent k
                  (TopCat.of (stdSimplex ℝ (Fin (k + 1 + 1)))) ≫
                (SSet.chainComplexMap
                  (TopCat.toSSet.map (singularSimplexRealizationMap X s))
                  (ModuleCat.of ℤ ℤ)).f (k + 1)
          exact (barycentricSubdivisionPrismComponent_naturality k
            (singularSimplexRealizationMap X s)).symm
        calc
          _ = (ιΔ ≫ F.f (k + 1)) ≫
                (PrismChains X).d (k + 1) k ≫
                barycentricSubdivisionPrismComponent k X := by rw [hι]
          _ = ιΔ ≫ (F.f (k + 1) ≫
                (PrismChains X).d (k + 1) k) ≫
                barycentricSubdivisionPrismComponent k X := by
              simp only [Category.assoc]
          _ = ιΔ ≫ ((PrismChains Δ).d (k + 1) k ≫ F.f k) ≫
                barycentricSubdivisionPrismComponent k X := by
              rw [F.comm (k + 1) k]
          _ = ιΔ ≫ (PrismChains Δ).d (k + 1) k ≫
                (F.f k ≫ barycentricSubdivisionPrismComponent k X) := by
              simp only [Category.assoc]
          _ = (ιΔ ≫ (PrismChains Δ).d (k + 1) k ≫
                barycentricSubdivisionPrismComponent k Δ) ≫
                F.f (k + 1) := by rw [hnat]; simp only [Category.assoc]
      have hz : z ≫ (PrismChains Δ).d (k + 1) k = 0 := by
        exact successorPrismModelError_comp_d_eq_zero k ih
      have hfillF :
          z ≫ (standardSimplexPositiveContraction (k + 1)).hom
                (k + 1) (k + 2) ≫
              (PrismChains Δ).d (k + 2) (k + 1) ≫ F.f (k + 1) =
            z ≫ F.f (k + 1) := by
        have h := congr_arg (fun q => q ≫ F.f (k + 1))
          (standardSimplexPositiveContraction_fillsCycle (k + 1) k z hz)
        simpa only [Category.assoc] using h
      have hupper :
          (TopCat.toSSet.obj X).ιChainComplex
                (R := ModuleCat.of ℤ ℤ) s ≫
              barycentricSubdivisionPrismComponent (k + 1) X ≫
              (PrismChains X).d (k + 2) (k + 1) =
            z ≫ F.f (k + 1) := by
        have hprism :
            (TopCat.toSSet.obj X).ιChainComplex
                  (R := ModuleCat.of ℤ ℤ) s ≫
                barycentricSubdivisionPrismComponent (k + 1) X =
              z ≫ (standardSimplexPositiveContraction (k + 1)).hom
                    (k + 1) (k + 2) ≫ F.f (k + 2) := by
          exact ι_barycentricSubdivisionPrismComponent_succ X k s
        calc
          _ = ((TopCat.toSSet.obj X).ιChainComplex
                    (R := ModuleCat.of ℤ ℤ) s ≫
                  barycentricSubdivisionPrismComponent (k + 1) X) ≫
                (PrismChains X).d (k + 2) (k + 1) := by
              simp only [Category.assoc]
          _ = (z ≫ (standardSimplexPositiveContraction (k + 1)).hom
                    (k + 1) (k + 2) ≫ F.f (k + 2)) ≫
                (PrismChains X).d (k + 2) (k + 1) := by rw [hprism]
          _ = z ≫ (standardSimplexPositiveContraction (k + 1)).hom
                    (k + 1) (k + 2) ≫
                (F.f (k + 2) ≫
                  (PrismChains X).d (k + 2) (k + 1)) := by
              simp only [Category.assoc]
          _ = z ≫ (standardSimplexPositiveContraction (k + 1)).hom
                    (k + 1) (k + 2) ≫
                ((PrismChains Δ).d (k + 2) (k + 1) ≫ F.f (k + 1)) := by
              rw [F.comm (k + 2) (k + 1)]
          _ = z ≫ F.f (k + 1) := hfillF
      have hdecomp :
          ιΔ ≫ (signedBarycentricSubdivisionDifference Δ).f (k + 1) =
            (ιΔ ≫ (PrismChains Δ).d (k + 1) k ≫
                barycentricSubdivisionPrismComponent k Δ) + z := by
        dsimp [z, successorPrismModelError]
        abel
      calc
        (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) s ≫
            (signedBarycentricSubdivisionDifference X).f (k + 1) =
          (ιΔ ≫ (signedBarycentricSubdivisionDifference Δ).f (k + 1)) ≫
            F.f (k + 1) := by
              rw [Category.assoc, hdiff, ← Category.assoc, hι]
        _ = ((ιΔ ≫ (PrismChains Δ).d (k + 1) k ≫
                barycentricSubdivisionPrismComponent k Δ) + z) ≫
              F.f (k + 1) := by rw [hdecomp]
        _ = (ιΔ ≫ (PrismChains Δ).d (k + 1) k ≫
                barycentricSubdivisionPrismComponent k Δ) ≫ F.f (k + 1) +
              z ≫ F.f (k + 1) := by rw [Preadditive.add_comp]
        _ = (TopCat.toSSet.obj X).ιChainComplex
                (R := ModuleCat.of ℤ ℤ) s ≫
              (PrismChains X).d (k + 1) k ≫
                barycentricSubdivisionPrismComponent k X +
            (TopCat.toSSet.obj X).ιChainComplex
                (R := ModuleCat.of ℤ ℤ) s ≫
              barycentricSubdivisionPrismComponent (k + 1) X ≫
                (PrismChains X).d (k + 2) (k + 1) := by
          rw [hlower, hupper]

theorem signedBarycentricSubdivisionDifference_eq_prismNullMap
    (X : TopCat) :
    signedBarycentricSubdivisionDifference X =
      barycentricSubdivisionPrismNullMap X := by
  apply HomologicalComplex.hom_ext
  intro n
  exact signedBarycentricSubdivisionDifference_f_eq_prismNullMap_f n X

noncomputable def signedBarycentricSubdivisionDifferenceNullHomotopy
    (X : TopCat) :
    _root_.Homotopy (signedBarycentricSubdivisionDifference X) 0 :=
  (_root_.Homotopy.ofEq
      (signedBarycentricSubdivisionDifference_eq_prismNullMap X)).trans
    (_root_.Homotopy.nullHomotopy'
      (barycentricSubdivisionPrismHomOfRel X))

noncomputable def signedBarycentricSubdivisionChainHomotopy
    (X : TopCat) :
    _root_.Homotopy (signedBarycentricSubdivisionChainEndomorphism X)
      (𝟙 (PrismChains X)) :=
  _root_.Homotopy.equivSubZero.symm
    (signedBarycentricSubdivisionDifferenceNullHomotopy X)

end DifferentialGeometry.Topology.SphereSeparation
