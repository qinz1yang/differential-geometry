import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import DifferentialGeometry.Topology.SphereSeparation.SphereComparison
import DifferentialGeometry.Topology.SphereSeparation.SpecializedDuality

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open Simplicial
open scoped Simplicial

namespace DifferentialGeometry.Topology.SphereSeparation



private noncomputable def integerSimplicialChainsEvalIso (n : ℕ) :
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ) ⋙
        HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) ≅
      ((evaluation SimplexCategoryᵒᵖ Type).obj
        (Opposite.op (SimplexCategory.mk n))) ⋙
        sigmaConst.obj (ModuleCat.of ℤ ℤ) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

noncomputable instance integerSimplicialChains_preservesColimitsOfShape
    {J : Type} [Category J] :
    PreservesColimitsOfShape J
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n => by
    exact preservesColimitsOfShape_of_natIso
      (integerSimplicialChainsEvalIso n).symm)

theorem integerChains_isPushout_of_subcomplex_bicartSq
    {X : SSet} {A₁ A₂ A₃ A₄ : X.Subcomplex}
    (sq : SSet.Subcomplex.BicartSq A₁ A₂ A₃ A₄) :
    IsPushout
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₂)
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₁₃)
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₂₄)
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE sq.le₃₄)
        (ModuleCat.of ℤ ℤ)) :=
  (sq.isPushout.map
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)))

theorem integerChains_isPushout_inf_sup
    {X : SSet} (A B : X.Subcomplex) :
    IsPushout
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
        (ModuleCat.of ℤ ℤ))
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))
        (ModuleCat.of ℤ ℤ)) :=
  integerChains_isPushout_of_subcomplex_bicartSq
    ({ sup_eq := rfl, inf_eq := rfl } :
      SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B))

theorem mono_integerSimplicialChainMap
    {X Y : SSet} (f : X ⟶ Y) [Mono f] :
    Mono (SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)) := by
  dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor,
    AlgebraicTopology.singularChainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
  infer_instance

theorem integerChains_mayerVietoris_shortExact
    {X : SSet} (A B : X.Subcomplex) :
    (integerChains_isPushout_inf_sup A B).shortComplex.ShortExact := by
  let h := integerChains_isPushout_inf_sup A B
  let _ : Mono
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        (ModuleCat.of ℤ ℤ)) :=
    mono_integerSimplicialChainMap _
  apply ShortComplex.ShortExact.mk'
  · exact h.exact_shortComplex
  · change Mono (biprod.lift
      (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        (ModuleCat.of ℤ ℤ))
      (-SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
        (ModuleCat.of ℤ ℤ)))
    infer_instance
  · exact h.epi_shortComplex_g

noncomputable def integerChainsRelativeUnionComparison
    {X : SSet} (A B : X.Subcomplex) :
    cokernel
        (SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
          (ModuleCat.of ℤ ℤ)) ⟶
      cokernel
        (SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
          (ModuleCat.of ℤ ℤ)) :=
  let h := integerChains_isPushout_inf_sup A B
  cokernel.map _ _
    (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (ModuleCat.of ℤ ℤ))
    (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))
      (ModuleCat.of ℤ ℤ)) h.w.symm

theorem isIso_integerChainsRelativeUnionComparison
    {X : SSet} (A B : X.Subcomplex) :
    IsIso (integerChainsRelativeUnionComparison A B) := by
  let h := (integerChains_isPushout_inf_sup A B).flip
  exact isIso_cokernel_map_of_isPushout h

noncomputable def integerChainsRelativeUnionIso
    {X : SSet} (A B : X.Subcomplex) :
    cokernel
        (SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
          (ModuleCat.of ℤ ℤ)) ≅
      cokernel
        (SSet.chainComplexMap
          (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
          (ModuleCat.of ℤ ℤ)) := by
  let _ := isIso_integerChainsRelativeUnionComparison A B
  exact asIso (integerChainsRelativeUnionComparison A B)



theorem mem_range_toSSet_subspace_iff
    {X : Type} [TopologicalSpace X] (A : Set X)
    {n : SimplexCategoryᵒᵖ}
    (s : (TopCat.toSSet.obj (TopCat.of X)).obj n) :
    s ∈ (SSet.Subcomplex.range
        (TopCat.toSSet.map (topologicalSubspaceInclusion A))).obj n ↔
      Set.range (TopCat.toSSetObjEquiv (TopCat.of X) n s) ⊆ A := by
  constructor
  · rintro ⟨t, rfl⟩ x ⟨z, rfl⟩
    exact (TopCat.toSSetObjEquiv (TopCat.of A) n t z).2
  · intro hs
    let t : C(stdSimplex ℝ (Fin (n.unop.len + 1)), A) :=
      ⟨fun z ↦ ⟨TopCat.toSSetObjEquiv (TopCat.of X) n s z,
          hs ⟨z, rfl⟩⟩,
        (TopCat.toSSetObjEquiv (TopCat.of X) n s).continuous.subtype_mk _⟩
    refine ⟨(TopCat.toSSetObjEquiv (TopCat.of A) n).symm t, ?_⟩
    apply (TopCat.toSSetObjEquiv (TopCat.of X) n).injective
    apply ContinuousMap.ext
    intro z
    rfl

theorem range_toSSet_subspace_inter
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    SSet.Subcomplex.range
        (TopCat.toSSet.map (topologicalSubspaceInclusion (A ∩ B))) =
      SSet.Subcomplex.range
          (TopCat.toSSet.map (topologicalSubspaceInclusion A)) ⊓
        SSet.Subcomplex.range
          (TopCat.toSSet.map (topologicalSubspaceInclusion B)) := by
  ext n s
  rw [mem_range_toSSet_subspace_iff]
  rw [Subfunctor.min_obj, Set.mem_inter_iff,
    mem_range_toSSet_subspace_iff, mem_range_toSSet_subspace_iff]
  constructor
  · intro hs
    exact ⟨fun x hx ↦ (hs hx).1, fun x hx ↦ (hs hx).2⟩
  · rintro ⟨hsA, hsB⟩ x hx
    exact ⟨hsA hx, hsB hx⟩

noncomputable def singularChainsSubspaceRangeIso
    {X : Type} [TopologicalSpace X] (A : Set X) :
    integerSingularChains (TopCat.of A) ≅
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        (SSet.Subcomplex.range
          (TopCat.toSSet.map (topologicalSubspaceInclusion A))) := by
  let i := topologicalSubspaceInclusion A
  letI : Mono i := (TopCat.mono_iff_injective i).2 Subtype.val_injective
  letI : Mono (TopCat.toSSet.map i) := by apply Functor.map_mono
  exact ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).mapIso
      (asIso (SSet.Subcomplex.toRange (TopCat.toSSet.map i)))

noncomputable def singularChainsIntersectionInfIso
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    integerSingularChains (TopCat.of (A ∩ B : Set X)) ≅
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        ((SSet.Subcomplex.range
              (TopCat.toSSet.map (topologicalSubspaceInclusion A)) ⊓
            SSet.Subcomplex.range
              (TopCat.toSSet.map (topologicalSubspaceInclusion B))) :
          (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) :=
  singularChainsSubspaceRangeIso (A ∩ B) ≪≫
    ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).mapIso
        (SSet.Subcomplex.eqToIso (range_toSSet_subspace_inter A B))

noncomputable abbrev singularSubspaceRange
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (TopCat.toSSet.obj (TopCat.of X)).Subcomplex :=
  SSet.Subcomplex.range
    (TopCat.toSSet.map (topologicalSubspaceInclusion A))

noncomputable def singularChainsIntersectionToLeft
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    integerSingularChains (TopCat.of (A ∩ B : Set X)) ⟶
      integerSingularChains (TopCat.of A) :=
  (singularChainsIntersectionInfIso A B).hom ≫
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE
        (inf_le_left : singularSubspaceRange (A := A) ⊓
          singularSubspaceRange (A := B) ≤ singularSubspaceRange (A := A)))
      (ModuleCat.of ℤ ℤ) ≫
    (singularChainsSubspaceRangeIso A).inv

noncomputable def singularChainsIntersectionToRight
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    integerSingularChains (TopCat.of (A ∩ B : Set X)) ⟶
      integerSingularChains (TopCat.of B) :=
  (singularChainsIntersectionInfIso A B).hom ≫
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE
        (inf_le_right : singularSubspaceRange (A := A) ⊓
          singularSubspaceRange (A := B) ≤ singularSubspaceRange (A := B)))
      (ModuleCat.of ℤ ℤ) ≫
    (singularChainsSubspaceRangeIso B).inv

noncomputable def singularChainsLeftToSmall
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    integerSingularChains (TopCat.of A) ⟶
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        (((singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B)) :
          (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) :=
  (singularChainsSubspaceRangeIso A).hom ≫
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE
        (le_sup_left : singularSubspaceRange (A := A) ≤
          singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B)))
      (ModuleCat.of ℤ ℤ)

noncomputable def singularChainsRightToSmall
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    integerSingularChains (TopCat.of B) ⟶
      ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj
        (((singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B)) :
          (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) : SSet) :=
  (singularChainsSubspaceRangeIso B).hom ≫
    SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE
        (le_sup_right : singularSubspaceRange (A := B) ≤
          singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B)))
      (ModuleCat.of ℤ ℤ)

theorem integerSingularChains_isPushout_subspaces
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    IsPushout
      (singularChainsIntersectionToLeft A B)
      (singularChainsIntersectionToRight A B)
      (singularChainsLeftToSmall A B)
      (singularChainsRightToSmall A B) := by
  let h := integerChains_isPushout_inf_sup
    (singularSubspaceRange (A := A)) (singularSubspaceRange (A := B))
  apply h.of_iso'
    (singularChainsIntersectionInfIso A B)
    (singularChainsSubspaceRangeIso A)
    (singularChainsSubspaceRangeIso B)
    (Iso.refl _)
  · simp [singularChainsIntersectionToLeft]
  · simp [singularChainsIntersectionToRight]
  · dsimp [singularChainsLeftToSmall]
    rw [Category.comp_id]
  · dsimp [singularChainsRightToSmall]
    rw [Category.comp_id]

theorem integerSingularChains_mayerVietoris_shortExact_subspaces
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (integerSingularChains_isPushout_subspaces A B).shortComplex.ShortExact := by
  let iLeft := SSet.Subcomplex.homOfLE
    (inf_le_left : singularSubspaceRange (A := A) ⊓
      singularSubspaceRange (A := B) ≤ singularSubspaceRange (A := A))
  let _ : Mono (SSet.chainComplexMap iLeft (ModuleCat.of ℤ ℤ)) :=
    mono_integerSimplicialChainMap iLeft
  let _ : Mono (singularChainsIntersectionToLeft A B) := by
    dsimp [singularChainsIntersectionToLeft]
    infer_instance
  let h := integerSingularChains_isPushout_subspaces A B
  apply ShortComplex.ShortExact.mk'
  · exact h.exact_shortComplex
  · change Mono (biprod.lift
      (singularChainsIntersectionToLeft A B)
      (-singularChainsIntersectionToRight A B))
    infer_instance
  · exact h.epi_shortComplex_g




theorem isOpen_sphereTwoPuncture (p : SphereTwo) :
    IsOpen ({p}ᶜ : Set SphereTwo) :=
  isClosed_singleton.isOpen_compl


theorem sphereTwoPunctureCover
    {p q : SphereTwo} (hpq : p ≠ q) :
    ({p}ᶜ : Set SphereTwo) ∪ {q}ᶜ = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_univ, iff_true]
  by_cases hxp : x = p
  · exact Or.inr (by simpa [hxp] using hpq)
  · exact Or.inl hxp

theorem sphereTwoPuncture_inter
    (p q : SphereTwo) :
    ({p}ᶜ : Set SphereTwo) ∩ {q}ᶜ = ({p, q} : Set SphereTwo)ᶜ := by
  ext x
  simp

theorem sphereTwoPunctureCover_mayerVietoris_shortExact
    (p q : SphereTwo) :
    (integerSingularChains_isPushout_subspaces
      ({p}ᶜ : Set SphereTwo) {q}ᶜ).shortComplex.ShortExact :=
  integerSingularChains_mayerVietoris_shortExact_subspaces _ _

end DifferentialGeometry.Topology.SphereSeparation
