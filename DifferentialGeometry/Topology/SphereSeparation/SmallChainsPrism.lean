import DifferentialGeometry.Topology.SphereSeparation.SubdivisionPrism
import DifferentialGeometry.Topology.SphereSeparation.SpecializedDuality
import DifferentialGeometry.Topology.SphereSeparation.LocallyNilpotentHomotopy
import DifferentialGeometry.Topology.SphereSeparation.SubdivisionSmallness

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open Simplicial
open scoped Simplicial

namespace Poincare.Topology.SphereSeparation

private noncomputable abbrev AmbientChains (X : TopCat) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  integerSingularChainComplex X

noncomputable def leftToSmallSingularSubcomplex
    (X : TopCat) (V W : Set X) :
    TopCat.toSSet.obj (TopCat.of V) ⟶ (smallSingularSubcomplex X V W : SSet) :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (topologicalSubspaceInclusion V))
    (show SSet.Subcomplex.range
          (TopCat.toSSet.map (topologicalSubspaceInclusion V)) ≤
        smallSingularSubcomplex X V W by
      exact le_sup_left)

noncomputable def rightToSmallSingularSubcomplex
    (X : TopCat) (V W : Set X) :
    TopCat.toSSet.obj (TopCat.of W) ⟶ (smallSingularSubcomplex X V W : SSet) :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (topologicalSubspaceInclusion W))
    (show SSet.Subcomplex.range
          (TopCat.toSSet.map (topologicalSubspaceInclusion W)) ≤
        smallSingularSubcomplex X V W by
      exact le_sup_right)

@[reassoc (attr := simp)]
theorem leftToSmallSingularSubcomplex_comp_inclusion
    (X : TopCat) (V W : Set X) :
    leftToSmallSingularSubcomplex X V W ≫
        (smallSingularSubcomplex X V W).ι =
      TopCat.toSSet.map (topologicalSubspaceInclusion V) := by
  exact SSet.Subcomplex.lift_ι _ _

@[reassoc (attr := simp)]
theorem rightToSmallSingularSubcomplex_comp_inclusion
    (X : TopCat) (V W : Set X) :
    rightToSmallSingularSubcomplex X V W ≫
        (smallSingularSubcomplex X V W).ι =
      TopCat.toSSet.map (topologicalSubspaceInclusion W) := by
  exact SSet.Subcomplex.lift_ι _ _


noncomputable def smallBarycentricPiece
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (smallSingularSubcomplex X V W : SSet) _⦋n⦌ := by
  refine ⟨barycentricPieceOfSingularSimplex X s.1 σ, ?_⟩
  rcases s.2 with hs | hs
  · rcases hs with ⟨t, ht⟩
    apply Or.inl
    refine ⟨barycentricPieceOfSingularSimplex (TopCat.of V) t σ, ?_⟩
    rw [barycentricPieceOfSingularSimplex_naturality, ht]
  · rcases hs with ⟨t, ht⟩
    apply Or.inr
    refine ⟨barycentricPieceOfSingularSimplex (TopCat.of W) t σ, ?_⟩
    rw [barycentricPieceOfSingularSimplex_naturality, ht]

@[simp]
theorem smallBarycentricPiece_val
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌)
    (σ : Equiv.Perm (Fin (n + 1))) :
    (smallBarycentricPiece X V W s σ).1 =
      barycentricPieceOfSingularSimplex X s.1 σ :=
  rfl

noncomputable def smallBarycentricSubdivisionDegreeMap
    (X : TopCat) (V W : Set X) (n : ℕ) :
    (smallSingularChainComplex X V W).X n ⟶
      (smallSingularChainComplex X V W).X n :=
  Sigma.desc fun s =>
    ∑ σ : Equiv.Perm (Fin (n + 1)),
      (Equiv.Perm.sign σ : ℤ) •
        (smallSingularSubcomplex X V W : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) (smallBarycentricPiece X V W s σ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ιChainComplex_smallBarycentricSubdivisionDegreeMap
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) :
    (smallSingularSubcomplex X V W : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s ≫
        smallBarycentricSubdivisionDegreeMap X V W n =
      ∑ σ : Equiv.Perm (Fin (n + 1)),
        (Equiv.Perm.sign σ : ℤ) •
          (smallSingularSubcomplex X V W : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) (smallBarycentricPiece X V W s σ) := by
  dsimp [smallBarycentricSubdivisionDegreeMap, SSet.ιChainComplex]
  rw [Sigma.ι_desc]

set_option backward.isDefEq.respectTransparency false in
theorem smallBarycentricSubdivisionDegreeMap_comp_inclusion
    (X : TopCat) (V W : Set X) (n : ℕ) :
    smallBarycentricSubdivisionDegreeMap X V W n ≫
        (smallSingularChainInclusion X V W).f n =
      (smallSingularChainInclusion X V W).f n ≫
        (signedBarycentricSubdivisionChainEndomorphism X).f n := by
  change smallBarycentricSubdivisionDegreeMap X V W n ≫
        (SSet.chainComplexMap (smallSingularSubcomplex X V W).ι
          (ModuleCat.of ℤ ℤ)).f n =
      (SSet.chainComplexMap (smallSingularSubcomplex X V W).ι
          (ModuleCat.of ℤ ℤ)).f n ≫
        barycentricSubdivisionDegreeMap X n
  apply SSet.chainComplex_hom_ext
  intro s
  rw [← Category.assoc,
    ιChainComplex_smallBarycentricSubdivisionDegreeMap,
    Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f]
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  rw [ιChainComplex_barycentricSubdivisionDegreeMap]
  apply Finset.sum_congr rfl
  intro σ _
  congr 2

noncomputable def smallBarycentricSubdivisionChainEndomorphism
    (X : TopCat) (V W : Set X) :
    smallSingularChainComplex X V W ⟶
      smallSingularChainComplex X V W where
  f n := smallBarycentricSubdivisionDegreeMap X V W n
  comm' i j hij := by
    obtain rfl : i = j + 1 := by simpa using hij.symm
    let _ : Mono (smallSingularChainInclusion X V W) :=
      mono_smallSingularChainInclusion X V W
    apply (cancel_mono ((smallSingularChainInclusion X V W).f j)).1
    calc
      (smallBarycentricSubdivisionDegreeMap X V W (j + 1) ≫
          (smallSingularChainComplex X V W).d (j + 1) j) ≫
            (smallSingularChainInclusion X V W).f j =
        smallBarycentricSubdivisionDegreeMap X V W (j + 1) ≫
          ((smallSingularChainComplex X V W).d (j + 1) j ≫
            (smallSingularChainInclusion X V W).f j) := by
              simp only [Category.assoc]
      _ = smallBarycentricSubdivisionDegreeMap X V W (j + 1) ≫
          ((smallSingularChainInclusion X V W).f (j + 1) ≫
            (integerSingularChainComplex X).d (j + 1) j) := by
              rw [← (smallSingularChainInclusion X V W).comm (j + 1) j]
      _ = (smallBarycentricSubdivisionDegreeMap X V W (j + 1) ≫
            (smallSingularChainInclusion X V W).f (j + 1)) ≫
          (integerSingularChainComplex X).d (j + 1) j := by
              simp only [Category.assoc]
      _ = ((smallSingularChainInclusion X V W).f (j + 1) ≫
            (signedBarycentricSubdivisionChainEndomorphism X).f (j + 1)) ≫
          (integerSingularChainComplex X).d (j + 1) j := by
              rw [smallBarycentricSubdivisionDegreeMap_comp_inclusion]
      _ = (smallSingularChainInclusion X V W).f (j + 1) ≫
          ((signedBarycentricSubdivisionChainEndomorphism X).f (j + 1) ≫
            (integerSingularChainComplex X).d (j + 1) j) := by
              simp only [Category.assoc]
      _ = (smallSingularChainInclusion X V W).f (j + 1) ≫
          ((integerSingularChainComplex X).d (j + 1) j ≫
            (signedBarycentricSubdivisionChainEndomorphism X).f j) := by
              rw [(signedBarycentricSubdivisionChainEndomorphism X).comm
                (j + 1) j]
      _ = ((smallSingularChainInclusion X V W).f (j + 1) ≫
            (integerSingularChainComplex X).d (j + 1) j) ≫
          (signedBarycentricSubdivisionChainEndomorphism X).f j := by
              simp only [Category.assoc]
      _ = ((smallSingularChainComplex X V W).d (j + 1) j ≫
            (smallSingularChainInclusion X V W).f j) ≫
          (signedBarycentricSubdivisionChainEndomorphism X).f j := by
              rw [(smallSingularChainInclusion X V W).comm (j + 1) j]
      _ = (smallSingularChainComplex X V W).d (j + 1) j ≫
          ((smallSingularChainInclusion X V W).f j ≫
            (signedBarycentricSubdivisionChainEndomorphism X).f j) := by
              simp only [Category.assoc]
      _ = (smallSingularChainComplex X V W).d (j + 1) j ≫
          (smallBarycentricSubdivisionDegreeMap X V W j ≫
            (smallSingularChainInclusion X V W).f j) := by
              rw [smallBarycentricSubdivisionDegreeMap_comp_inclusion]
      _ = ((smallSingularChainComplex X V W).d (j + 1) j ≫
            smallBarycentricSubdivisionDegreeMap X V W j) ≫
          (smallSingularChainInclusion X V W).f j := by
              simp only [Category.assoc]

theorem smallBarycentricSubdivisionChainEndomorphism_comp_inclusion
    (X : TopCat) (V W : Set X) :
    smallBarycentricSubdivisionChainEndomorphism X V W ≫
        smallSingularChainInclusion X V W =
      smallSingularChainInclusion X V W ≫
        signedBarycentricSubdivisionChainEndomorphism X := by
  apply HomologicalComplex.hom_ext
  intro n
  exact smallBarycentricSubdivisionDegreeMap_comp_inclusion X V W n



noncomputable def leftToSmallSingularChainMap
    (X : TopCat) (V W : Set X) :
    AmbientChains (TopCat.of V) ⟶ smallSingularChainComplex X V W :=
  SSet.chainComplexMap (leftToSmallSingularSubcomplex X V W)
    (ModuleCat.of ℤ ℤ)

noncomputable def rightToSmallSingularChainMap
    (X : TopCat) (V W : Set X) :
    AmbientChains (TopCat.of W) ⟶ smallSingularChainComplex X V W :=
  SSet.chainComplexMap (rightToSmallSingularSubcomplex X V W)
    (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)]
theorem leftToSmallSingularChainMap_comp_inclusion
    (X : TopCat) (V W : Set X) :
    leftToSmallSingularChainMap X V W ≫
        smallSingularChainInclusion X V W =
      integerSingularChainMap (topologicalSubspaceInclusion V) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
        (leftToSmallSingularSubcomplex X V W) ≫
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
        (smallSingularSubcomplex X V W).ι =
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map
      (TopCat.toSSet.map (topologicalSubspaceInclusion V))
  rw [← Functor.map_comp, leftToSmallSingularSubcomplex_comp_inclusion]

@[reassoc (attr := simp)]
theorem rightToSmallSingularChainMap_comp_inclusion
    (X : TopCat) (V W : Set X) :
    rightToSmallSingularChainMap X V W ≫
        smallSingularChainInclusion X V W =
      integerSingularChainMap (topologicalSubspaceInclusion W) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
        (rightToSmallSingularSubcomplex X V W) ≫
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
        (ModuleCat.of ℤ ℤ)).map
        (smallSingularSubcomplex X V W).ι =
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map
      (TopCat.toSSet.map (topologicalSubspaceInclusion W))
  rw [← Functor.map_comp, rightToSmallSingularSubcomplex_comp_inclusion]

private def SmallSimplexFactorsLeftOf
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) : Prop :=
  ∃ t : (TopCat.toSSet.obj (TopCat.of V)) _⦋n⦌,
    (TopCat.toSSet.map (topologicalSubspaceInclusion V)).app _ t = s.1

private def SmallSimplexFactorsRightOf
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) : Prop :=
  ∃ t : (TopCat.toSSet.obj (TopCat.of W)) _⦋n⦌,
    (TopCat.toSSet.map (topologicalSubspaceInclusion W)).app _ t = s.1

private theorem smallSimplex_factors_left_or_right
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) :
    SmallSimplexFactorsLeftOf X V W s ∨
      SmallSimplexFactorsRightOf X V W s :=
  s.2

noncomputable def smallBarycentricSubdivisionPrismGenerator
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) :
    ModuleCat.of ℤ ℤ ⟶ (smallSingularChainComplex X V W).X (n + 1) := by
  classical
  exact if hV : SmallSimplexFactorsLeftOf X V W s then
    let t := Classical.choose hV
    (TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) t ≫
      barycentricSubdivisionPrismComponent n (TopCat.of V) ≫
      (leftToSmallSingularChainMap X V W).f (n + 1)
  else
    let hW : SmallSimplexFactorsRightOf X V W s := by
      rcases smallSimplex_factors_left_or_right X V W s with h | h
      · exact False.elim (hV h)
      · exact h
    let t := Classical.choose hW
    (TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) t ≫
      barycentricSubdivisionPrismComponent n (TopCat.of W) ≫
      (rightToSmallSingularChainMap X V W).f (n + 1)

set_option backward.isDefEq.respectTransparency false in
theorem smallBarycentricSubdivisionPrismGenerator_comp_inclusion
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) :
    smallBarycentricSubdivisionPrismGenerator X V W s ≫
        (smallSingularChainInclusion X V W).f (n + 1) =
      (TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s.1 ≫
        barycentricSubdivisionPrismComponent n X := by
  classical
  by_cases hV : SmallSimplexFactorsLeftOf X V W s
  · rw [smallBarycentricSubdivisionPrismGenerator, dif_pos hV]
    have ht :
        (TopCat.toSSet.map (topologicalSubspaceInclusion V)).app _
            (Classical.choose hV) =
          s.1 := Classical.choose_spec hV
    have hcomp := HomologicalComplex.congr_hom
      (leftToSmallSingularChainMap_comp_inclusion X V W) (n + 1)
    have hcomp' :
        (leftToSmallSingularChainMap X V W).f (n + 1) ≫
            (smallSingularChainInclusion X V W).f (n + 1) =
          (integerSingularChainMap
            (topologicalSubspaceInclusion V)).f (n + 1) := by
      simpa only [HomologicalComplex.comp_f] using hcomp
    calc
      _ = ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) (Classical.choose hV) ≫
            barycentricSubdivisionPrismComponent n (TopCat.of V)) ≫
          ((leftToSmallSingularChainMap X V W).f (n + 1) ≫
            (smallSingularChainInclusion X V W).f (n + 1)) := by
              simp only [Category.assoc]
      _ = ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) (Classical.choose hV) ≫
            barycentricSubdivisionPrismComponent n (TopCat.of V)) ≫
          (integerSingularChainMap
            (topologicalSubspaceInclusion V)).f (n + 1) := by rw [hcomp']
      _ = (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.map
                  (topologicalSubspaceInclusion V)).app _
                    (Classical.choose hV)) ≫
            barycentricSubdivisionPrismComponent n X :=
          (ι_map_barycentricSubdivisionPrismComponent
            (topologicalSubspaceInclusion V) n (Classical.choose hV)).symm
      _ = _ := by rw [ht]
  · rw [smallBarycentricSubdivisionPrismGenerator, dif_neg hV]
    let hW : SmallSimplexFactorsRightOf X V W s := by
      rcases smallSimplex_factors_left_or_right X V W s with h | h
      · exact False.elim (hV h)
      · exact h
    have ht :
        (TopCat.toSSet.map (topologicalSubspaceInclusion W)).app _
            (Classical.choose hW) =
          s.1 := Classical.choose_spec hW
    have hcomp := HomologicalComplex.congr_hom
      (rightToSmallSingularChainMap_comp_inclusion X V W) (n + 1)
    have hcomp' :
        (rightToSmallSingularChainMap X V W).f (n + 1) ≫
            (smallSingularChainInclusion X V W).f (n + 1) =
          (integerSingularChainMap
            (topologicalSubspaceInclusion W)).f (n + 1) := by
      simpa only [HomologicalComplex.comp_f] using hcomp
    calc
      _ = ((TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) (Classical.choose hW) ≫
            barycentricSubdivisionPrismComponent n (TopCat.of W)) ≫
          ((rightToSmallSingularChainMap X V W).f (n + 1) ≫
            (smallSingularChainInclusion X V W).f (n + 1)) := by
              simp only [Category.assoc]
      _ = ((TopCat.toSSet.obj (TopCat.of W)).ιChainComplex
              (R := ModuleCat.of ℤ ℤ) (Classical.choose hW) ≫
            barycentricSubdivisionPrismComponent n (TopCat.of W)) ≫
          (integerSingularChainMap
            (topologicalSubspaceInclusion W)).f (n + 1) := by rw [hcomp']
      _ = (TopCat.toSSet.obj X).ιChainComplex
              (R := ModuleCat.of ℤ ℤ)
                ((TopCat.toSSet.map
                  (topologicalSubspaceInclusion W)).app _
                    (Classical.choose hW)) ≫
            barycentricSubdivisionPrismComponent n X :=
          (ι_map_barycentricSubdivisionPrismComponent
            (topologicalSubspaceInclusion W) n (Classical.choose hW)).symm
      _ = _ := by rw [ht]

noncomputable def smallBarycentricSubdivisionPrismComponent
    (X : TopCat) (V W : Set X) (n : ℕ) :
    (smallSingularChainComplex X V W).X n ⟶
      (smallSingularChainComplex X V W).X (n + 1) :=
  Sigma.desc fun s =>
    smallBarycentricSubdivisionPrismGenerator X V W s

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem ι_smallBarycentricSubdivisionPrismComponent
    (X : TopCat) (V W : Set X) {n : ℕ}
    (s : (smallSingularSubcomplex X V W : SSet) _⦋n⦌) :
    (smallSingularSubcomplex X V W : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s ≫
        smallBarycentricSubdivisionPrismComponent X V W n =
      smallBarycentricSubdivisionPrismGenerator X V W s := by
  dsimp [smallBarycentricSubdivisionPrismComponent, SSet.ιChainComplex]
  rw [Sigma.ι_desc]

set_option backward.isDefEq.respectTransparency false in
theorem smallBarycentricSubdivisionPrismComponent_comp_inclusion
    (X : TopCat) (V W : Set X) (n : ℕ) :
    smallBarycentricSubdivisionPrismComponent X V W n ≫
        (smallSingularChainInclusion X V W).f (n + 1) =
      (smallSingularChainInclusion X V W).f n ≫
        barycentricSubdivisionPrismComponent n X := by
  apply SSet.chainComplex_hom_ext
  intro s
  have hι :
      (smallSingularSubcomplex X V W : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) s ≫
          (smallSingularChainInclusion X V W).f n =
        (TopCat.toSSet.obj X).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s.1 := by
    change (smallSingularSubcomplex X V W : SSet).ιChainComplex
            (R := ModuleCat.of ℤ ℤ) s ≫
          (SSet.chainComplexMap (smallSingularSubcomplex X V W).ι
            (ModuleCat.of ℤ ℤ)).f n = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  rw [← Category.assoc, ι_smallBarycentricSubdivisionPrismComponent,
    smallBarycentricSubdivisionPrismGenerator_comp_inclusion]
  rw [← Category.assoc, hι]

private noncomputable def smallBarycentricSubdivisionPrismHomOfRel
    (X : TopCat) (V W : Set X) (i j : ℕ)
    (hji : (ComplexShape.down ℕ).Rel j i) :
    (smallSingularChainComplex X V W).X i ⟶
      (smallSingularChainComplex X V W).X j := by
  have h : i + 1 = j := by simpa using hji
  subst j
  exact smallBarycentricSubdivisionPrismComponent X V W i

@[simp]
private theorem smallBarycentricSubdivisionPrismHomOfRel_succ
    (X : TopCat) (V W : Set X) (i : ℕ)
    (h : (ComplexShape.down ℕ).Rel (i + 1) i) :
    smallBarycentricSubdivisionPrismHomOfRel X V W i (i + 1) h =
      smallBarycentricSubdivisionPrismComponent X V W i := by
  unfold smallBarycentricSubdivisionPrismHomOfRel
  rfl

noncomputable def smallBarycentricSubdivisionPrismNullMap
    (X : TopCat) (V W : Set X) :
    smallSingularChainComplex X V W ⟶
      smallSingularChainComplex X V W :=
  _root_.Homotopy.nullHomotopicMap'
    (smallBarycentricSubdivisionPrismHomOfRel X V W)

private noncomputable def ambientBarycentricSubdivisionPrismHomOfRel
    (X : TopCat) (i j : ℕ)
    (hji : (ComplexShape.down ℕ).Rel j i) :
    (AmbientChains X).X i ⟶ (AmbientChains X).X j := by
  have h : i + 1 = j := by simpa using hji
  subst j
  exact barycentricSubdivisionPrismComponent i X

@[simp]
private theorem ambientBarycentricSubdivisionPrismHomOfRel_succ
    (X : TopCat) (i : ℕ)
    (h : (ComplexShape.down ℕ).Rel (i + 1) i) :
    ambientBarycentricSubdivisionPrismHomOfRel X i (i + 1) h =
      barycentricSubdivisionPrismComponent i X := by
  unfold ambientBarycentricSubdivisionPrismHomOfRel
  rfl

private noncomputable def ambientBarycentricSubdivisionPrismNullMap
    (X : TopCat) : AmbientChains X ⟶ AmbientChains X :=
  _root_.Homotopy.nullHomotopicMap'
    (ambientBarycentricSubdivisionPrismHomOfRel X)

set_option backward.isDefEq.respectTransparency false in
private theorem ambientBarycentricSubdivisionPrismComponent_zero
    (X : TopCat) : barycentricSubdivisionPrismComponent 0 X = 0 := by
  apply SSet.chainComplex_hom_ext
  intro s
  rw [ι_barycentricSubdivisionPrismComponent_zero]
  rw [comp_zero]

private theorem ambientBarycentricSubdivisionPrismNullMap_f_zero
    (X : TopCat) :
    (ambientBarycentricSubdivisionPrismNullMap X).f 0 = 0 := by
  rw [ambientBarycentricSubdivisionPrismNullMap,
    _root_.Homotopy.nullHomotopicMap'_f_of_not_rel_left
      (show (ComplexShape.down ℕ).Rel 1 0 by simp)
      (show ∀ l : ℕ, ¬(ComplexShape.down ℕ).Rel 0 l by simp)]
  rw [ambientBarycentricSubdivisionPrismHomOfRel_succ,
    ambientBarycentricSubdivisionPrismComponent_zero]
  simp

private theorem ambientBarycentricSubdivisionPrismNullMap_f_succ
    (X : TopCat) (k : ℕ) :
    (ambientBarycentricSubdivisionPrismNullMap X).f (k + 1) =
      (AmbientChains X).d (k + 1) k ≫
          barycentricSubdivisionPrismComponent k X +
        barycentricSubdivisionPrismComponent (k + 1) X ≫
          (AmbientChains X).d (k + 2) (k + 1) := by
  rw [ambientBarycentricSubdivisionPrismNullMap,
    _root_.Homotopy.nullHomotopicMap'_f
      (show (ComplexShape.down ℕ).Rel (k + 2) (k + 1) by simp)
      (show (ComplexShape.down ℕ).Rel (k + 1) k by simp)]
  rfl

private theorem ambientBarycentricSubdivisionPrismNullMap_eq
    (X : TopCat) :
    ambientBarycentricSubdivisionPrismNullMap X =
      barycentricSubdivisionPrismNullMap X := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      rw [ambientBarycentricSubdivisionPrismNullMap_f_zero,
        barycentricSubdivisionPrismNullMap_f_zero]
  | succ k =>
      rw [ambientBarycentricSubdivisionPrismNullMap_f_succ,
        barycentricSubdivisionPrismNullMap_f_succ]

set_option backward.isDefEq.respectTransparency false in
private theorem smallBarycentricSubdivisionPrismHomOfRel_comp_inclusion
    (X : TopCat) (V W : Set X) (i j : ℕ)
    (hji : (ComplexShape.down ℕ).Rel j i) :
    smallBarycentricSubdivisionPrismHomOfRel X V W i j hji ≫
        (smallSingularChainInclusion X V W).f j =
      (smallSingularChainInclusion X V W).f i ≫
        ambientBarycentricSubdivisionPrismHomOfRel X i j hji := by
  have h : i + 1 = j := by simpa using hji
  subst j
  change smallBarycentricSubdivisionPrismComponent X V W i ≫
      (smallSingularChainInclusion X V W).f (i + 1) =
    (smallSingularChainInclusion X V W).f i ≫
      barycentricSubdivisionPrismComponent i X
  exact smallBarycentricSubdivisionPrismComponent_comp_inclusion X V W i

theorem smallBarycentricSubdivisionPrismNullMap_comp_inclusion
    (X : TopCat) (V W : Set X) :
    smallBarycentricSubdivisionPrismNullMap X V W ≫
        smallSingularChainInclusion X V W =
      smallSingularChainInclusion X V W ≫
        barycentricSubdivisionPrismNullMap X := by
  rw [← ambientBarycentricSubdivisionPrismNullMap_eq]
  rw [smallBarycentricSubdivisionPrismNullMap,
    ambientBarycentricSubdivisionPrismNullMap,
    _root_.Homotopy.nullHomotopicMap'_comp,
    _root_.Homotopy.comp_nullHomotopicMap']
  congr
  funext i j hji
  exact smallBarycentricSubdivisionPrismHomOfRel_comp_inclusion
    X V W i j hji


noncomputable def smallBarycentricSubdivisionDifference
    (X : TopCat) (V W : Set X) :
    smallSingularChainComplex X V W ⟶
      smallSingularChainComplex X V W :=
  smallBarycentricSubdivisionChainEndomorphism X V W - 𝟙 _

theorem smallBarycentricSubdivisionDifference_comp_inclusion
    (X : TopCat) (V W : Set X) :
    smallBarycentricSubdivisionDifference X V W ≫
        smallSingularChainInclusion X V W =
      smallSingularChainInclusion X V W ≫
        signedBarycentricSubdivisionDifference X := by
  rw [smallBarycentricSubdivisionDifference,
    signedBarycentricSubdivisionDifference,
    Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id,
    smallBarycentricSubdivisionChainEndomorphism_comp_inclusion]

theorem smallBarycentricSubdivisionDifference_eq_prismNullMap
    (X : TopCat) (V W : Set X) :
    smallBarycentricSubdivisionDifference X V W =
      smallBarycentricSubdivisionPrismNullMap X V W := by
  let _ : Mono (smallSingularChainInclusion X V W) :=
    mono_smallSingularChainInclusion X V W
  apply (cancel_mono (smallSingularChainInclusion X V W)).1
  rw [smallBarycentricSubdivisionDifference_comp_inclusion,
    smallBarycentricSubdivisionPrismNullMap_comp_inclusion,
    signedBarycentricSubdivisionDifference_eq_prismNullMap]

noncomputable def smallBarycentricSubdivisionDifferenceNullHomotopy
    (X : TopCat) (V W : Set X) :
    _root_.Homotopy (smallBarycentricSubdivisionDifference X V W) 0 :=
  (_root_.Homotopy.ofEq
      (smallBarycentricSubdivisionDifference_eq_prismNullMap X V W)).trans
    (_root_.Homotopy.nullHomotopy'
      (smallBarycentricSubdivisionPrismHomOfRel X V W))

noncomputable def smallBarycentricSubdivisionChainHomotopy
    (X : TopCat) (V W : Set X) :
    _root_.Homotopy
      (smallBarycentricSubdivisionChainEndomorphism X V W)
      (𝟙 (smallSingularChainComplex X V W)) :=
  _root_.Homotopy.equivSubZero.symm
    (smallBarycentricSubdivisionDifferenceNullHomotopy X V W)



noncomputable def smallChainsCokernelSubdivision
    (X : TopCat) (V W : Set X) :
    cokernel (smallSingularChainInclusion X V W) ⟶
      cokernel (smallSingularChainInclusion X V W) :=
  chainCokernelEndomorphism
    (smallSingularChainInclusion X V W)
    (smallBarycentricSubdivisionChainEndomorphism X V W)
    (signedBarycentricSubdivisionChainEndomorphism X)
    (smallBarycentricSubdivisionChainEndomorphism_comp_inclusion
      X V W).symm


noncomputable def smallChainsCokernelSubdivisionPrismComponent
    (X : TopCat) (V W : Set X) (n : ℕ) :
    (cokernel (smallSingularChainInclusion X V W)).X n ⟶
      (cokernel (smallSingularChainInclusion X V W)).X (n + 1) :=
  (PreservesCokernel.iso
      (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      (smallSingularChainInclusion X V W)).hom ≫
    cokernel.desc ((smallSingularChainInclusion X V W).f n)
      (barycentricSubdivisionPrismComponent n X ≫
        (cokernel.π (smallSingularChainInclusion X V W)).f (n + 1))
      (by
      have hzero :
          (smallSingularChainInclusion X V W).f (n + 1) ≫
              (cokernel.π
                (smallSingularChainInclusion X V W)).f (n + 1) = 0 := by
        have h := HomologicalComplex.congr_hom
          (cokernel.condition (smallSingularChainInclusion X V W)) (n + 1)
        simpa only [HomologicalComplex.comp_f,
          HomologicalComplex.zero_f_apply] using h
      calc
        (smallSingularChainInclusion X V W).f n ≫
              (barycentricSubdivisionPrismComponent n X ≫
                (cokernel.π
                  (smallSingularChainInclusion X V W)).f (n + 1)) =
            ((smallSingularChainInclusion X V W).f n ≫
                barycentricSubdivisionPrismComponent n X) ≫
              (cokernel.π
                (smallSingularChainInclusion X V W)).f (n + 1) := by
                  simp only [Category.assoc]
        _ = (smallBarycentricSubdivisionPrismComponent X V W n ≫
                (smallSingularChainInclusion X V W).f (n + 1)) ≫
              (cokernel.π
                (smallSingularChainInclusion X V W)).f (n + 1) := by
                  rw [smallBarycentricSubdivisionPrismComponent_comp_inclusion]
        _ = smallBarycentricSubdivisionPrismComponent X V W n ≫
              ((smallSingularChainInclusion X V W).f (n + 1) ≫
                (cokernel.π
                  (smallSingularChainInclusion X V W)).f (n + 1)) := by
                  simp only [Category.assoc]
        _ = 0 := by rw [hzero, comp_zero])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem smallChainsCokernelProjection_comp_subdivisionPrismComponent
    (X : TopCat) (V W : Set X) (n : ℕ) :
    (cokernel.π (smallSingularChainInclusion X V W)).f n ≫
        smallChainsCokernelSubdivisionPrismComponent X V W n =
      barycentricSubdivisionPrismComponent n X ≫
        (cokernel.π
          (smallSingularChainInclusion X V W)).f (n + 1) := by
  have hπ :
      (cokernel.π (smallSingularChainInclusion X V W)).f n ≫
          (PreservesCokernel.iso
            (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
            (smallSingularChainInclusion X V W)).hom =
        cokernel.π ((smallSingularChainInclusion X V W).f n) := by
    exact PreservesCokernel.π_iso_hom
      (G := HomologicalComplex.eval
        (ModuleCat ℤ) (ComplexShape.down ℕ) n)
      (f := smallSingularChainInclusion X V W)
  change (cokernel.π (smallSingularChainInclusion X V W)).f n ≫
      ((PreservesCokernel.iso
          (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)
          (smallSingularChainInclusion X V W)).hom ≫
        cokernel.desc ((smallSingularChainInclusion X V W).f n)
          (barycentricSubdivisionPrismComponent n X ≫
            (cokernel.π
              (smallSingularChainInclusion X V W)).f (n + 1)) _) = _
  rw [← Category.assoc, hπ, cokernel.π_desc]

private noncomputable def smallChainsCokernelSubdivisionPrismHomOfRel
    (X : TopCat) (V W : Set X) (i j : ℕ)
    (hji : (ComplexShape.down ℕ).Rel j i) :
    (cokernel (smallSingularChainInclusion X V W)).X i ⟶
      (cokernel (smallSingularChainInclusion X V W)).X j := by
  have h : i + 1 = j := by simpa using hji
  subst j
  exact smallChainsCokernelSubdivisionPrismComponent X V W i

set_option backward.isDefEq.respectTransparency false in
private theorem smallChainsCokernelSubdivisionPrismHomOfRel_succ
    (X : TopCat) (V W : Set X) (i : ℕ)
    (h : (ComplexShape.down ℕ).Rel (i + 1) i) :
    smallChainsCokernelSubdivisionPrismHomOfRel X V W i (i + 1) h =
      smallChainsCokernelSubdivisionPrismComponent X V W i := by
  unfold smallChainsCokernelSubdivisionPrismHomOfRel
  rfl

noncomputable def smallChainsCokernelSubdivisionPrismNullMap
    (X : TopCat) (V W : Set X) :
    cokernel (smallSingularChainInclusion X V W) ⟶
      cokernel (smallSingularChainInclusion X V W) :=
  _root_.Homotopy.nullHomotopicMap'
    (smallChainsCokernelSubdivisionPrismHomOfRel X V W)

set_option backward.isDefEq.respectTransparency false in
private theorem smallChainsCokernelSubdivisionPrismHomOfRel_projection
    (X : TopCat) (V W : Set X) (i j : ℕ)
    (hji : (ComplexShape.down ℕ).Rel j i) :
    (cokernel.π (smallSingularChainInclusion X V W)).f i ≫
        smallChainsCokernelSubdivisionPrismHomOfRel X V W i j hji =
      ambientBarycentricSubdivisionPrismHomOfRel X i j hji ≫
        (cokernel.π (smallSingularChainInclusion X V W)).f j := by
  have h : i + 1 = j := by simpa using hji
  subst j
  change (cokernel.π (smallSingularChainInclusion X V W)).f i ≫
      smallChainsCokernelSubdivisionPrismComponent X V W i =
    barycentricSubdivisionPrismComponent i X ≫
      (cokernel.π (smallSingularChainInclusion X V W)).f (i + 1)
  exact smallChainsCokernelProjection_comp_subdivisionPrismComponent X V W i

theorem smallChainsCokernelProjection_comp_subdivisionPrismNullMap
    (X : TopCat) (V W : Set X) :
    cokernel.π (smallSingularChainInclusion X V W) ≫
        smallChainsCokernelSubdivisionPrismNullMap X V W =
      barycentricSubdivisionPrismNullMap X ≫
        cokernel.π (smallSingularChainInclusion X V W) := by
  rw [← ambientBarycentricSubdivisionPrismNullMap_eq]
  rw [smallChainsCokernelSubdivisionPrismNullMap,
    ambientBarycentricSubdivisionPrismNullMap,
    _root_.Homotopy.comp_nullHomotopicMap',
    _root_.Homotopy.nullHomotopicMap'_comp]
  congr
  funext i j hji
  exact smallChainsCokernelSubdivisionPrismHomOfRel_projection
    X V W i j hji

@[reassoc (attr := simp)]
theorem smallChainsCokernelProjection_comp_subdivision
    (X : TopCat) (V W : Set X) :
    cokernel.π (smallSingularChainInclusion X V W) ≫
        smallChainsCokernelSubdivision X V W =
      signedBarycentricSubdivisionChainEndomorphism X ≫
        cokernel.π (smallSingularChainInclusion X V W) := by
  exact chainCokernelProjection_naturality
    (smallSingularChainInclusion X V W)
    (smallBarycentricSubdivisionChainEndomorphism X V W)
    (signedBarycentricSubdivisionChainEndomorphism X)
    (smallBarycentricSubdivisionChainEndomorphism_comp_inclusion
      X V W).symm


noncomputable def smallChainsCokernelSubdivisionDifference
    (X : TopCat) (V W : Set X) :
    cokernel (smallSingularChainInclusion X V W) ⟶
      cokernel (smallSingularChainInclusion X V W) :=
  smallChainsCokernelSubdivision X V W - 𝟙 _

theorem smallChainsCokernelProjection_comp_subdivisionDifference
    (X : TopCat) (V W : Set X) :
    cokernel.π (smallSingularChainInclusion X V W) ≫
        smallChainsCokernelSubdivisionDifference X V W =
      signedBarycentricSubdivisionDifference X ≫
        cokernel.π (smallSingularChainInclusion X V W) := by
  rw [smallChainsCokernelSubdivisionDifference,
    signedBarycentricSubdivisionDifference,
    Preadditive.comp_sub, Preadditive.sub_comp,
    Category.comp_id, Category.id_comp,
    smallChainsCokernelProjection_comp_subdivision]

theorem smallChainsCokernelSubdivisionDifference_eq_prismNullMap
    (X : TopCat) (V W : Set X) :
    smallChainsCokernelSubdivisionDifference X V W =
      smallChainsCokernelSubdivisionPrismNullMap X V W := by
  apply (cancel_epi
    (cokernel.π (smallSingularChainInclusion X V W))).1
  rw [smallChainsCokernelProjection_comp_subdivisionDifference,
    smallChainsCokernelProjection_comp_subdivisionPrismNullMap,
    signedBarycentricSubdivisionDifference_eq_prismNullMap]

noncomputable def smallChainsCokernelSubdivisionDifferenceNullHomotopy
    (X : TopCat) (V W : Set X) :
    _root_.Homotopy
      (smallChainsCokernelSubdivisionDifference X V W) 0 :=
  (_root_.Homotopy.ofEq
      (smallChainsCokernelSubdivisionDifference_eq_prismNullMap X V W)).trans
    (_root_.Homotopy.nullHomotopy'
      (smallChainsCokernelSubdivisionPrismHomOfRel X V W))

noncomputable def smallChainsCokernelSubdivisionHomotopy
    (X : TopCat) (V W : Set X) :
    _root_.Homotopy (smallChainsCokernelSubdivision X V W)
      (𝟙 (cokernel (smallSingularChainInclusion X V W))) :=
  _root_.Homotopy.equivSubZero.symm
    (smallChainsCokernelSubdivisionDifferenceNullHomotopy X V W)



theorem smallChainsCokernelSubdivision_eventually_zero
    (X : TopCat) {V₀ W₀ V W : Set X}
    (hV₀ : IsOpen V₀) (hW₀ : IsOpen W₀)
    (hcover : V₀ ∪ W₀ = Set.univ)
    (hV : V₀ ⊆ V) (hW : W₀ ⊆ W) (n : ℕ) :
    ∀ x : (integerSingularChainComplex X).X n, ∃ k : ℕ,
      (cokernel.π (smallSingularChainInclusion X V W)).f n
        ((((signedBarycentricSubdivisionChainEndomorphism X).f n)^[k]) x) =
          0 := by
  apply subdivision_eventually_zero_in_smallChainCokernel X
    hV₀ hW₀ hcover hV hW n
  intro x hx
  have hmap := HomologicalComplex.congr_hom
    (smallChainsCokernelProjection_comp_subdivision X V W) n
  have happly := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hmap) x
  calc
    (cokernel.π (smallSingularChainInclusion X V W)).f n
        ((singularBarycentricSubdivision X).f n x) =
      (smallChainsCokernelSubdivision X V W).f n
        ((cokernel.π (smallSingularChainInclusion X V W)).f n x) :=
          happly.symm
    _ = (smallChainsCokernelSubdivision X V W).f n 0 := by rw [hx]
    _ = 0 := map_zero _

theorem quasiIso_smallSingularChainInclusion
    (X : TopCat) (V W : Set X)
    (hV : IsOpen V) (hW : IsOpen W)
    (hcover : V ∪ W = Set.univ) :
    QuasiIso (smallSingularChainInclusion X V W) := by
  let _ : Mono (smallSingularChainInclusion X V W) :=
    mono_smallSingularChainInclusion X V W
  apply quasiIso_of_cokernelSubdivision_eventually_zero
    (smallSingularChainInclusion X V W)
    (smallBarycentricSubdivisionChainEndomorphism X V W)
    (signedBarycentricSubdivisionChainEndomorphism X)
    (smallBarycentricSubdivisionChainEndomorphism_comp_inclusion X V W).symm
    (smallChainsCokernelSubdivisionHomotopy X V W)
  intro n x
  exact smallChainsCokernelSubdivision_eventually_zero X
    hV hW hcover (fun _ h ↦ h) (fun _ h ↦ h) n x

theorem quasiIso_smallSingularChainInclusion_of_openCover_refines
    (X : TopCat) {V₀ W₀ V W : Set X}
    (hV₀ : IsOpen V₀) (hW₀ : IsOpen W₀)
    (hcover : V₀ ∪ W₀ = Set.univ)
    (hV : V₀ ⊆ V) (hW : W₀ ⊆ W) :
    QuasiIso (smallSingularChainInclusion X V W) := by
  let _ : Mono (smallSingularChainInclusion X V W) :=
    mono_smallSingularChainInclusion X V W
  apply quasiIso_of_cokernelSubdivision_eventually_zero
    (smallSingularChainInclusion X V W)
    (smallBarycentricSubdivisionChainEndomorphism X V W)
    (signedBarycentricSubdivisionChainEndomorphism X)
    (smallBarycentricSubdivisionChainEndomorphism_comp_inclusion X V W).symm
    (smallChainsCokernelSubdivisionHomotopy X V W)
  intro n x
  exact smallChainsCokernelSubdivision_eventually_zero X
    hV₀ hW₀ hcover hV hW n x

end Poincare.Topology.SphereSeparation
