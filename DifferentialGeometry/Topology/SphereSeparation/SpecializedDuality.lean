import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import DifferentialGeometry.Topology.SphereSeparation.AlexanderDuality

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits
open Simplicial
open scoped Manifold ContDiff Topology Simplicial

namespace DifferentialGeometry.Topology.SphereSeparation



noncomputable abbrev integerSingularChainComplex (X : TopCat) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X)


noncomputable def integerSingularChainMap {X Y : TopCat} (f : X ⟶ Y) :
    integerSingularChainComplex X ⟶ integerSingularChainComplex Y :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map f

@[simp]
theorem integerSingularChainMap_id (X : TopCat) :
    integerSingularChainMap (𝟙 X) = 𝟙 (integerSingularChainComplex X) :=
  by simp [integerSingularChainMap]

@[simp]
theorem integerSingularChainMap_comp {X Y Z : TopCat}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    integerSingularChainMap (f ≫ g) =
      integerSingularChainMap f ≫ integerSingularChainMap g :=
  Functor.map_comp _ f g

noncomputable abbrev relativeSingularChainComplex {A X : TopCat} (i : A ⟶ X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (integerSingularChainMap i)

noncomputable abbrev relativeSingularHomology {A X : TopCat} (i : A ⟶ X)
    (n : ℕ) : ModuleCat ℤ :=
  (relativeSingularChainComplex i).homology n


noncomputable abbrev relativeSingularChainProjection {A X : TopCat} (i : A ⟶ X) :
    integerSingularChainComplex X ⟶ relativeSingularChainComplex i :=
  cokernel.π (integerSingularChainMap i)

@[reassoc]
theorem integerSingularChainMap_comp_relativeProjection
    {A X : TopCat} (i : A ⟶ X) :
    integerSingularChainMap i ≫ relativeSingularChainProjection i = 0 :=
  cokernel.condition (integerSingularChainMap i)

noncomputable def relativeSingularChainMap
    {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j) :
    relativeSingularChainComplex i ⟶ relativeSingularChainComplex j :=
  cokernel.map
    (integerSingularChainMap i) (integerSingularChainMap j)
    (integerSingularChainMap fA) (integerSingularChainMap fX) (by
      rw [← integerSingularChainMap_comp, h, integerSingularChainMap_comp])

@[reassoc (attr := simp)]
theorem relativeSingularChainProjection_naturality
    {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j) :
    relativeSingularChainProjection i ≫
        relativeSingularChainMap i j fA fX h =
      integerSingularChainMap fX ≫ relativeSingularChainProjection j := by
  simp [relativeSingularChainMap]

@[simp]
theorem relativeSingularChainMap_id {A X : TopCat} (i : A ⟶ X) :
    relativeSingularChainMap i i (𝟙 A) (𝟙 X) (by simp) =
      𝟙 (relativeSingularChainComplex i) := by
  simp [relativeSingularChainMap]


theorem relativeSingularChainMap_comp
    {A X B Y C Z : TopCat}
    (i : A ⟶ X) (j : B ⟶ Y) (k : C ⟶ Z)
    (fA : A ⟶ B) (fX : X ⟶ Y) (hf : i ≫ fX = fA ≫ j)
    (gA : B ⟶ C) (gX : Y ⟶ Z) (hg : j ≫ gX = gA ≫ k) :
    relativeSingularChainMap i j fA fX hf ≫
        relativeSingularChainMap j k gA gX hg =
      relativeSingularChainMap i k (fA ≫ gA) (fX ≫ gX) (by
        rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc]) := by
  apply (cancel_epi (relativeSingularChainProjection i)).1
  simp [Category.assoc]

theorem isIso_relativeSingularChainMap
    {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j)
    [IsIso fA] [IsIso fX] :
    IsIso (relativeSingularChainMap i j fA fX h) := by
  have h_inv : j ≫ inv fX = inv fA ≫ i := by
    apply (cancel_mono fX).1
    simp [Category.assoc, h]
  refine ⟨⟨relativeSingularChainMap j i (inv fA) (inv fX) h_inv, ?_, ?_⟩⟩
  · rw [relativeSingularChainMap_comp]
    simp
  · rw [relativeSingularChainMap_comp]
    simp

theorem isIso_relativeSingularHomologyMap
    {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j)
    [IsIso fA] [IsIso fX] (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularChainMap i j fA fX h) n) := by
  let _ : IsIso (relativeSingularChainMap i j fA fX h) :=
    isIso_relativeSingularChainMap i j fA fX h
  exact (HomologicalComplex.homologyMapIso
    (asIso (relativeSingularChainMap i j fA fX h)) n).isIso_hom


def topologicalSubspaceInclusion
    {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩


noncomputable abbrev relativeSingularHomologyOfSubspace
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) : ModuleCat ℤ :=
  relativeSingularHomology (topologicalSubspaceInclusion A) n

def topologicalSubspaceMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨f x, h x x.2⟩,
      continuous_induced_rng.2 (f.continuous.comp continuous_subtype_val)⟩

@[reassoc]
theorem topologicalSubspaceMap_comm
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B) :
    topologicalSubspaceInclusion A ≫ TopCat.ofHom f =
      topologicalSubspaceMap f A B h ≫ topologicalSubspaceInclusion B := by
  rfl

noncomputable def relativeSingularChainMapOfSubspaces
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B) :
    relativeSingularChainComplex (topologicalSubspaceInclusion A) ⟶
      relativeSingularChainComplex (topologicalSubspaceInclusion B) :=
  relativeSingularChainMap
    (topologicalSubspaceInclusion A) (topologicalSubspaceInclusion B)
    (topologicalSubspaceMap f A B h) (TopCat.ofHom f)
    (topologicalSubspaceMap_comm f A B h)


noncomputable def relativeSingularHomologyMapOfSubspaces
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ) :
    relativeSingularHomologyOfSubspace A n ⟶
      relativeSingularHomologyOfSubspace B n :=
  HomologicalComplex.homologyMap
    (relativeSingularChainMapOfSubspaces f A B h) n

theorem isIso_relativeSingularHomologyMapOfSubspaces
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B)
    (hf : IsHomeomorph f)
    (hsub : IsHomeomorph (topologicalSubspaceMap f A B h))
    (n : ℕ) : IsIso (relativeSingularHomologyMapOfSubspaces f A B h n) := by
  let _ : IsIso (TopCat.ofHom f) :=
    (TopCat.isIso_iff_isHomeomorph (TopCat.ofHom f)).2 hf
  let _ : IsIso (topologicalSubspaceMap f A B h) :=
    (TopCat.isIso_iff_isHomeomorph (topologicalSubspaceMap f A B h)).2 hsub
  exact isIso_relativeSingularHomologyMap
    (topologicalSubspaceInclusion A) (topologicalSubspaceInclusion B)
    (topologicalSubspaceMap f A B h) (TopCat.ofHom f)
    (topologicalSubspaceMap_comm f A B h) n


def subspaceOutside
    {X : Type} (A U : Set X) : Set (Uᶜ : Set X) :=
  {x | x.1 ∈ A}

def subspaceOutsideHomeomorphDiff
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    subspaceOutside A U ≃ₜ (A \ U : Set X) where
  toFun x := ⟨x.1.1, x.2, x.1.2⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def excisionRelativeSingularChainMap
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainComplex
        (topologicalSubspaceInclusion (subspaceOutside A U)) ⟶
      relativeSingularChainComplex (topologicalSubspaceInclusion A) :=
    relativeSingularChainMapOfSubspaces
    ⟨(Subtype.val : (Uᶜ : Set X) → X), continuous_subtype_val⟩
    (subspaceOutside A U) A (fun _ hx ↦ hx)


noncomputable def excisionRelativeSingularHomologyMap
    {X : Type} [TopologicalSpace X] (A U : Set X) (n : ℕ) :
    relativeSingularHomologyOfSubspace (subspaceOutside A U) n ⟶
      relativeSingularHomologyOfSubspace A n :=
  HomologicalComplex.homologyMap (excisionRelativeSingularChainMap A U) n

def SingularExcisionFor
    {X : Type} [TopologicalSpace X] (A U : Set X) : Prop :=
  closure U ⊆ interior A →
    ∀ n : ℕ, IsIso (excisionRelativeSingularHomologyMap A U n)

def excisionCoverNear
    {X : Type} [TopologicalSpace X] (A : Set X) : Set X :=
  interior A

def excisionCoverFar
    {X : Type} [TopologicalSpace X] (U : Set X) : Set X :=
  (closure U)ᶜ

theorem isOpen_excisionCoverNear
    {X : Type} [TopologicalSpace X] (A : Set X) :
    IsOpen (excisionCoverNear A) :=
  isOpen_interior

theorem isOpen_excisionCoverFar
    {X : Type} [TopologicalSpace X] (U : Set X) :
    IsOpen (excisionCoverFar U) :=
  isClosed_closure.isOpen_compl

theorem excisionCoverNear_subset
    {X : Type} [TopologicalSpace X] (A : Set X) :
    excisionCoverNear A ⊆ A :=
  interior_subset

theorem excisionCoverFar_subset
    {X : Type} [TopologicalSpace X] (U : Set X) :
    excisionCoverFar U ⊆ Uᶜ :=
  Set.compl_subset_compl.mpr subset_closure

theorem excisionCover_union
    {X : Type} [TopologicalSpace X] {A U : Set X}
    (h : closure U ⊆ interior A) :
    excisionCoverNear A ∪ excisionCoverFar U = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ closure U
  · exact Or.inl (h hx)
  · exact Or.inr hx

abbrev TopologicalSingularSimplex
    (X : Type) [TopologicalSpace X] (n : ℕ) :=
  C(stdSimplex ℝ (Fin (n + 1)), X)

def SingularSimplexSmallFor
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (V W : Set X) (s : TopologicalSingularSimplex X n) : Prop :=
  Set.range s ⊆ V ∨ Set.range s ⊆ W

theorem singularZeroSimplex_smallFor_twoSetCover
    {X : Type} [TopologicalSpace X] {V W : Set X}
    (hcover : V ∪ W = Set.univ)
    (s : TopologicalSingularSimplex X 0) :
    SingularSimplexSmallFor V W s := by
  have hx : s default ∈ V ∪ W := by
    rw [hcover]
    exact Set.mem_univ _
  rcases hx with hx | hx
  · left
    rintro y ⟨z, rfl⟩
    simpa only [Subsingleton.elim z default] using hx
  · right
    rintro y ⟨z, rfl⟩
    simpa only [Subsingleton.elim z default] using hx

theorem singularZeroSimplex_smallFor_excisionCover
    {X : Type} [TopologicalSpace X] {A U : Set X}
    (h : closure U ⊆ interior A)
    (s : TopologicalSingularSimplex X 0) :
    SingularSimplexSmallFor (excisionCoverNear A) (excisionCoverFar U) s :=
  singularZeroSimplex_smallFor_twoSetCover (excisionCover_union h) s


def singularSimplexExcisionPullbackCover
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (A U : Set X) (s : TopologicalSingularSimplex X n) :
    Set (Set (stdSimplex ℝ (Fin (n + 1)))) :=
  {s ⁻¹' excisionCoverNear A, s ⁻¹' excisionCoverFar U}

theorem singularSimplex_excisionLebesgueNumber
    {X : Type} [TopologicalSpace X] {n : ℕ} {A U : Set X}
    (h : closure U ⊆ interior A)
    (s : TopologicalSingularSimplex X n) :
    ∃ δ > 0, ∀ x : stdSimplex ℝ (Fin (n + 1)),
      ∃ V ∈ singularSimplexExcisionPullbackCover A U s,
        Metric.ball x δ ⊆ V := by
  have hopen : ∀ V ∈ singularSimplexExcisionPullbackCover A U s, IsOpen V := by
    intro V hV
    rcases hV with (rfl | rfl)
    · exact (isOpen_excisionCoverNear A).preimage s.continuous
    · exact (isOpen_excisionCoverFar U).preimage s.continuous
  have hcover : Set.univ ⊆ ⋃₀ singularSimplexExcisionPullbackCover A U s := by
    intro x _
    have hx : s x ∈ excisionCoverNear A ∪ excisionCoverFar U := by
      rw [excisionCover_union h]
      exact Set.mem_univ _
    rcases hx with hx | hx
    · exact Set.mem_sUnion_of_mem
        (t := s ⁻¹' excisionCoverNear A) hx
        (by simp [singularSimplexExcisionPullbackCover])
    · exact Set.mem_sUnion_of_mem
        (t := s ⁻¹' excisionCoverFar U) hx
        (by simp [singularSimplexExcisionPullbackCover])
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric_sUnion isCompact_univ hopen hcover
  exact ⟨δ, hδ, fun x ↦ hball x (Set.mem_univ x)⟩

def topologicalSingularSimplexLift
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (s : TopologicalSingularSimplex X n) (A : Set X)
    (h : Set.range s ⊆ A) : TopologicalSingularSimplex A n :=
  ⟨fun x ↦ ⟨s x, h ⟨x, rfl⟩⟩, by fun_prop⟩

@[simp]
theorem topologicalSingularSimplexLift_coe
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (s : TopologicalSingularSimplex X n) (A : Set X)
    (h : Set.range s ⊆ A)
    (x : stdSimplex ℝ (Fin (n + 1))) :
    (topologicalSingularSimplexLift s A h x : X) = s x :=
  rfl

theorem singularSimplexSmallFor_excisionCover_factor
    {X : Type} [TopologicalSpace X] {n : ℕ} {A U : Set X}
    {s : TopologicalSingularSimplex X n}
    (hs : SingularSimplexSmallFor
      (excisionCoverNear A) (excisionCoverFar U) s) :
    (∃ t : TopologicalSingularSimplex A n,
        ∀ x, (t x : X) = s x) ∨
      (∃ t : TopologicalSingularSimplex (Uᶜ : Set X) n,
        ∀ x, (t x : X) = s x) := by
  rcases hs with hs | hs
  · left
    let hA : Set.range s ⊆ A :=
      hs.trans (excisionCoverNear_subset A)
    exact ⟨topologicalSingularSimplexLift s A hA, fun _ ↦ rfl⟩
  · right
    let hU : Set.range s ⊆ Uᶜ :=
      hs.trans (excisionCoverFar_subset U)
    exact ⟨topologicalSingularSimplexLift s Uᶜ hU, fun _ ↦ rfl⟩



noncomputable def smallSingularSubcomplex
    (X : TopCat) (V W : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubspaceInclusion V)) ⊔
    SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubspaceInclusion W))

@[simp]
theorem toSSetObjZeroEquiv_map
    {X Y : TopCat} (f : X ⟶ Y)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    TopCat.toSSetObj₀Equiv
        ((TopCat.toSSet.map f).app _ x) =
      f (TopCat.toSSetObj₀Equiv x) :=
  rfl

theorem smallSingularSubcomplex_obj_zero_eq_univ
    (X : TopCat) (V W : Set X) (hcover : V ∪ W = Set.univ) :
    (smallSingularSubcomplex X V W).obj
      (Opposite.op (SimplexCategory.mk 0)) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  have hx : TopCat.toSSetObj₀Equiv x ∈ V ∪ W := by
    rw [hcover]
    exact Set.mem_univ _
  rcases hx with hx | hx
  · apply Or.inl
    refine ⟨TopCat.toSSetObj₀Equiv.symm
      ⟨TopCat.toSSetObj₀Equiv x, hx⟩, ?_⟩
    apply TopCat.toSSetObj₀Equiv.injective
    simp [topologicalSubspaceInclusion]
  · apply Or.inr
    refine ⟨TopCat.toSSetObj₀Equiv.symm
      ⟨TopCat.toSSetObj₀Equiv x, hx⟩, ?_⟩
    apply TopCat.toSSetObj₀Equiv.injective
    simp [topologicalSubspaceInclusion]

theorem isIso_smallSingularSubcomplex_inclusion_app_zero
    (X : TopCat) (V W : Set X) (hcover : V ∪ W = Set.univ) :
    IsIso ((smallSingularSubcomplex X V W).ι.app
      (Opposite.op (SimplexCategory.mk 0))) := by
  apply (isIso_iff_bijective _).2
  constructor
  · exact Subtype.val_injective
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [smallSingularSubcomplex_obj_zero_eq_univ X V W hcover]
    exact Set.mem_univ x


noncomputable abbrev smallSingularChainComplex
    (X : TopCat) (V W : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  (smallSingularSubcomplex X V W : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)


noncomputable def smallSingularChainInclusion
    (X : TopCat) (V W : Set X) :
    smallSingularChainComplex X V W ⟶ integerSingularChainComplex X :=
  SSet.chainComplexMap (smallSingularSubcomplex X V W).ι
    (ModuleCat.of ℤ ℤ)


theorem mono_smallSingularChainInclusion
    (X : TopCat) (V W : Set X) :
    Mono (smallSingularChainInclusion X V W) := by
  dsimp [smallSingularChainInclusion, integerSingularChainComplex,
    smallSingularChainComplex, AlgebraicTopology.singularChainComplexFunctor,
    SSet.chainComplexMap, SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
  infer_instance

theorem isIso_smallSingularChainInclusion_f_zero
    (X : TopCat) (V W : Set X) (hcover : V ∪ W = Set.univ) :
    IsIso ((smallSingularChainInclusion X V W).f 0) := by
  let i₀ := (smallSingularSubcomplex X V W).ι.app
    (Opposite.op (SimplexCategory.mk 0))
  let _ : IsIso i₀ :=
    isIso_smallSingularSubcomplex_inclusion_app_zero X V W hcover
  let e : (smallSingularSubcomplex X V W : SSet).obj
        (Opposite.op (SimplexCategory.mk 0)) ≃
      (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)) :=
    Equiv.ofBijective i₀ ((isIso_iff_bijective i₀).1 inferInstance)
  dsimp [smallSingularChainInclusion, integerSingularChainComplex,
    smallSingularChainComplex, AlgebraicTopology.singularChainComplexFunctor,
    SSet.chainComplexMap, SSet.chainComplexFunctor,
    AlgebraicTopology.alternatingFaceMapComplex,
    SimplicialObject.whiskering, SimplicialObject]
  change IsIso (Sigma.map'
    (f := fun _ : (smallSingularSubcomplex X V W : SSet).obj
        (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ)
    (g := fun _ : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ)
    (fun x : (smallSingularSubcomplex X V W : SSet).obj
        (Opposite.op (SimplexCategory.mk 0)) ↦
      (x : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk 0))))
    (fun _ ↦ 𝟙 (ModuleCat.of ℤ ℤ)))
  simpa [e, i₀] using
    (Sigma.whiskerEquiv
      (C := ModuleCat ℤ)
      (f := fun _ : (smallSingularSubcomplex X V W : SSet).obj
          (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ)
      (g := fun _ : (TopCat.toSSet.obj X).obj
          (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ)
      e (fun _ ↦ Iso.refl (ModuleCat.of ℤ ℤ))).isIso_hom

def SmallChainsSubdivisionFor
    (X : TopCat) (V W : Set X) : Prop :=
  IsOpen V ∧ IsOpen W ∧ V ∪ W = Set.univ ∧
    ∀ n : ℕ, IsIso (HomologicalComplex.homologyMap
      (smallSingularChainInclusion X V W) n)

def complEmptyHomeomorph
    (X : Type) [TopologicalSpace X] :
    ((∅ : Set X)ᶜ : Set X) ≃ₜ X where
  toFun := Subtype.val
  invFun x := ⟨x, by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := by fun_prop

def subspaceOutsideEmptyHomeomorph
    {X : Type} [TopologicalSpace X] (A : Set X) :
    subspaceOutside A (∅ : Set X) ≃ₜ A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, by simp⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem isIso_excisionRelativeSingularHomologyMap_empty
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    IsIso (excisionRelativeSingularHomologyMap A (∅ : Set X) n) := by
  change IsIso (relativeSingularHomologyMapOfSubspaces
    ⟨(Subtype.val : ((∅ : Set X)ᶜ : Set X) → X), continuous_subtype_val⟩
    (subspaceOutside A (∅ : Set X)) A (fun _ hx ↦ hx) n)
  apply isIso_relativeSingularHomologyMapOfSubspaces
  · exact (complEmptyHomeomorph X).isHomeomorph
  · exact (subspaceOutsideEmptyHomeomorph A).isHomeomorph

theorem mono_integerSingularChainMap_subspace
    {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (integerSingularChainMap (topologicalSubspaceInclusion A)) := by
  let i := topologicalSubspaceInclusion A
  let _ : Mono i := (TopCat.mono_iff_injective i).2 Subtype.val_injective
  change Mono
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map i)
  infer_instance


noncomputable abbrev relativeSingularChainSequenceOfMap
    {A X : TopCat} (i : A ⟶ X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (integerSingularChainMap i)
    (relativeSingularChainProjection i)
    (integerSingularChainMap_comp_relativeProjection i)


noncomputable abbrev relativeSingularChainSequence
    {X : Type} [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  relativeSingularChainSequenceOfMap (topologicalSubspaceInclusion A)

theorem relativeSingularChainSequence_shortExact
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (relativeSingularChainSequence A).ShortExact := by
  change (ShortComplex.cokernelSequence
    (integerSingularChainMap (topologicalSubspaceInclusion A))).ShortExact
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.cokernelSequence_exact
      (integerSingularChainMap (topologicalSubspaceInclusion A))
  · exact mono_integerSingularChainMap_subspace A
  · infer_instance

noncomputable def relativeSingularChainSequenceMap
    {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j) :
    relativeSingularChainSequenceOfMap i ⟶
      relativeSingularChainSequenceOfMap j where
  τ₁ := integerSingularChainMap fA
  τ₂ := integerSingularChainMap fX
  τ₃ := relativeSingularChainMap i j fA fX h
  comm₁₂ := by
    change integerSingularChainMap fA ≫ integerSingularChainMap j =
      integerSingularChainMap i ≫ integerSingularChainMap fX
    rw [← integerSingularChainMap_comp, ← integerSingularChainMap_comp, h]
  comm₂₃ := by
    exact (relativeSingularChainProjection_naturality i j fA fX h).symm


noncomputable abbrev cokernelChainSequence
    {A X : ChainComplex (ModuleCat ℤ) ℕ} (i : A ⟶ X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

noncomputable def cokernelChainSequenceMap
    {A X B Y : ChainComplex (ModuleCat ℤ) ℕ}
    (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j) :
    cokernelChainSequence i ⟶ cokernelChainSequence j where
  τ₁ := fA
  τ₂ := fX
  τ₃ := cokernel.map i j fA fX h
  comm₁₂ := h.symm
  comm₂₃ := by simp

theorem quasiIso_cokernelMap
    {A X B Y : ChainComplex (ModuleCat ℤ) ℕ}
    (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j)
    [Mono i] [Mono j] (hA : QuasiIso fA) (hX : QuasiIso fX) :
    QuasiIso (cokernel.map i j fA fX h) := by
  have hi : (cokernelChainSequence i).ShortExact := by
    change (ShortComplex.cokernelSequence i).ShortExact
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.cokernelSequence_exact i
    · change Mono i
      infer_instance
    · infer_instance
  have hj : (cokernelChainSequence j).ShortExact := by
    change (ShortComplex.cokernelSequence j).ShortExact
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.cokernelSequence_exact j
    · change Mono j
      infer_instance
    · infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (cokernelChainSequenceMap i j fA fX h) hi hj hA hX


theorem isIso_homologyMap_cokernelMap
    {A X B Y : ChainComplex (ModuleCat ℤ) ℕ}
    (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j)
    [Mono i] [Mono j] (hA : QuasiIso fA) (hX : QuasiIso fX)
    (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (cokernel.map i j fA fX h) n) := by
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  let _ : QuasiIso (cokernel.map i j fA fX h) :=
    quasiIso_cokernelMap i j fA fX h hA hX
  infer_instance

theorem quasiIso_relativeSingularChainMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B)
    (hA : QuasiIso
      (integerSingularChainMap (topologicalSubspaceMap f A B h)))
    (hX : QuasiIso
      (integerSingularChainMap (TopCat.ofHom f))) :
    QuasiIso
      (relativeSingularChainMapOfSubspaces f A B h) := by
  let φ := relativeSingularChainSequenceMap
    (topologicalSubspaceInclusion A) (topologicalSubspaceInclusion B)
    (topologicalSubspaceMap f A B h) (TopCat.ofHom f)
    (topologicalSubspaceMap_comm f A B h)
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (relativeSingularChainSequence_shortExact A)
    (relativeSingularChainSequence_shortExact B) hA hX


theorem isIso_relativeSingularHomologyMapOfSubspaces_of_quasiIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B)
    (hA : QuasiIso
      (integerSingularChainMap (topologicalSubspaceMap f A B h)))
    (hX : QuasiIso
      (integerSingularChainMap (TopCat.ofHom f)))
    (n : ℕ) :
    IsIso (relativeSingularHomologyMapOfSubspaces f A B h n) := by
  change IsIso (HomologicalComplex.homologyMap
    (relativeSingularChainMapOfSubspaces f A B h) n)
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  let _ : QuasiIso (relativeSingularChainMapOfSubspaces f A B h) :=
    quasiIso_relativeSingularChainMap f A B h hA hX
  infer_instance

noncomputable abbrev integerSingularHomology (X : TopCat) (n : ℕ) :
    ModuleCat ℤ :=
  (integerSingularChainComplex X).homology n


noncomputable def subspaceSingularHomologyMap
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    integerSingularHomology (TopCat.of A) n ⟶
      integerSingularHomology (TopCat.of X) n :=
  HomologicalComplex.homologyMap
    (integerSingularChainMap (topologicalSubspaceInclusion A)) n


noncomputable def absoluteToRelativeSingularHomology
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    integerSingularHomology (TopCat.of X) n ⟶
      relativeSingularHomologyOfSubspace A n :=
  HomologicalComplex.homologyMap
    (relativeSingularChainProjection (topologicalSubspaceInclusion A)) n

noncomputable def relativeSingularBoundary
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    relativeSingularHomologyOfSubspace A (n + 1) ⟶
      integerSingularHomology (TopCat.of A) n :=
  (relativeSingularChainSequence_shortExact A).δ (n + 1) n (by simp)

theorem relativeSingularBoundary_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ) :
    relativeSingularHomologyMapOfSubspaces f A B h (n + 1) ≫
        relativeSingularBoundary B n =
      relativeSingularBoundary A n ≫
        HomologicalComplex.homologyMap
          (integerSingularChainMap (topologicalSubspaceMap f A B h)) n := by
  let φ := relativeSingularChainSequenceMap
    (topologicalSubspaceInclusion A) (topologicalSubspaceInclusion B)
    (topologicalSubspaceMap f A B h) (TopCat.ofHom f)
    (topologicalSubspaceMap_comm f A B h)
  exact (HomologicalComplex.HomologySequence.δ_naturality φ
    (relativeSingularChainSequence_shortExact A)
    (relativeSingularChainSequence_shortExact B) (n + 1) n (by simp)).symm


theorem relativeSingularHomology_exact_at_absolute
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk
      (subspaceSingularHomologyMap A n)
      (absoluteToRelativeSingularHomology A n)
      (by
        dsimp [subspaceSingularHomologyMap,
          absoluteToRelativeSingularHomology,
          relativeSingularChainProjection]
        rw [← HomologicalComplex.homologyMap_comp]
        simp)).Exact := by
  simpa [relativeSingularChainSequence, ShortComplex.cokernelSequence,
    subspaceSingularHomologyMap,
    absoluteToRelativeSingularHomology, relativeSingularChainProjection,
    relativeSingularHomologyOfSubspace, relativeSingularHomology,
    relativeSingularChainComplex] using
    (relativeSingularChainSequence_shortExact A).homology_exact₂ n

theorem relativeSingularHomology_exact_at_relative
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk
      (absoluteToRelativeSingularHomology A (n + 1))
      (relativeSingularBoundary A n)
      (by
        exact (relativeSingularChainSequence_shortExact A).comp_δ
          (n + 1) n (by simp))).Exact := by
  simpa [relativeSingularChainSequence, ShortComplex.cokernelSequence,
    absoluteToRelativeSingularHomology,
    relativeSingularBoundary, relativeSingularChainProjection,
    relativeSingularHomologyOfSubspace, relativeSingularHomology,
    relativeSingularChainComplex] using
    (relativeSingularChainSequence_shortExact A).homology_exact₃
      (n + 1) n (by simp)


theorem relativeSingularHomology_exact_at_subspace
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk
      (relativeSingularBoundary A n)
      (subspaceSingularHomologyMap A n)
      (by
        exact (relativeSingularChainSequence_shortExact A).δ_comp
          (n + 1) n (by simp))).Exact := by
  simpa [relativeSingularChainSequence, ShortComplex.cokernelSequence,
    subspaceSingularHomologyMap,
    relativeSingularBoundary, relativeSingularHomologyOfSubspace,
    relativeSingularHomology, relativeSingularChainComplex] using
    (relativeSingularChainSequence_shortExact A).homology_exact₁
      (n + 1) n (by simp)


def zerothHomotopyMapOfContinuousMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x ↦ ZerothHomotopy.mk (f x)) fun {_ _} p ↦
    ZerothHomotopy.sound (p.map f.continuous)

@[simp]
theorem zerothHomotopyMapOfContinuousMap_mk
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    zerothHomotopyMapOfContinuousMap f (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (f x) :=
  rfl


noncomputable def zerothHomotopyEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : ZerothHomotopy X ≃ ZerothHomotopy Y where
  toFun := zerothHomotopyMapOfContinuousMap ⟨h, h.continuous⟩
  invFun := zerothHomotopyMapOfContinuousMap ⟨h.symm, h.symm.continuous⟩
  left_inv q := by
    induction q using ZerothHomotopy.rec with
    | mk x => simp
  right_inv q := by
    induction q using ZerothHomotopy.rec with
    | mk y => simp

noncomputable def reducedSingularH0IsoOfHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) :
    reducedSingularH0 (TopCat.of X) ≅ reducedSingularH0 (TopCat.of Y) :=
  reducedSingularH0IsoAugmentedFinsuppKernel (TopCat.of X) ≪≫
    (augmentationKernelCongr
      (zerothHomotopyEquivOfHomeomorph h)).toModuleIso ≪≫
    (reducedSingularH0IsoAugmentedFinsuppKernel (TopCat.of Y)).symm

noncomputable def euclideanComplementHomeomorphCompactifiedComplement
    (e : SphereTwo → EuclideanThree) :
    ((Set.range e)ᶜ : Set EuclideanThree) ≃ₜ
      ((alexanderDualityCompactum e)ᶜ : Set (OnePoint EuclideanThree)) := by
  let f : ((Set.range e)ᶜ : Set EuclideanThree) → OnePoint EuclideanThree :=
    fun x ↦ (x.1 : OnePoint EuclideanThree)
  have hf : Topology.IsEmbedding f :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hrange :
      Set.range f =
        ((alexanderDualityCompactum e)ᶜ : Set (OnePoint EuclideanThree)) := by
    rw [compl_alexanderDualityCompactum]
    ext y
    simp [f]
  exact hf.toHomeomorph.trans (Homeomorph.setCongr hrange)

noncomputable def euclideanComplementReducedH0IsoCompactifiedComplement
    (e : SphereTwo → EuclideanThree) :
    reducedSingularH0
        (TopCat.of ((Set.range e)ᶜ : Set EuclideanThree)) ≅
      reducedSingularH0
        (TopCat.of
          ((alexanderDualityCompactum e)ᶜ : Set (OnePoint EuclideanThree))) :=
  reducedSingularH0IsoOfHomeomorph
    (euclideanComplementHomeomorphCompactifiedComplement e)

def SpecializedAlexanderDuality
    (e : SphereTwo → EuclideanThree) : Prop :=
  Nonempty
    (reducedSingularH0
        (TopCat.of ((Set.range e)ᶜ : Set EuclideanThree)) ≅
      singularCohomology (TopCat.of (alexanderDualityCompactum e)) 2)

def CompactifiedSpecializedAlexanderDuality
    (e : SphereTwo → EuclideanThree) : Prop :=
  Nonempty
    (reducedSingularH0
        (TopCat.of
          ((alexanderDualityCompactum e)ᶜ : Set (OnePoint EuclideanThree))) ≅
      singularCohomology (TopCat.of (alexanderDualityCompactum e)) 2)

theorem specializedAlexanderDuality_iff_compactified
    (e : SphereTwo → EuclideanThree) :
    SpecializedAlexanderDuality e ↔
      CompactifiedSpecializedAlexanderDuality e := by
  constructor
  · rintro ⟨h⟩
    exact ⟨
      (euclideanComplementReducedH0IsoCompactifiedComplement e).symm ≪≫ h⟩
  · rintro ⟨h⟩
    exact ⟨euclideanComplementReducedH0IsoCompactifiedComplement e ≪≫ h⟩

def SphereTwoSumPUnitH2IsInt : Prop :=
  Nonempty
    (singularCohomology (TopCat.of (SphereTwo ⊕ PUnit)) 2 ≅
      ModuleCat.of ℤ ℤ)

noncomputable def specializedAlexanderDualityIsoOfComponentCount
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hcomponents :
      ConnectedComponents ((Set.range e)ᶜ : Set EuclideanThree) ≃ Fin 2)
    (hsphere :
      singularCohomology (TopCat.of (SphereTwo ⊕ PUnit)) 2 ≅
        ModuleCat.of ℤ ℤ) :
    reducedSingularH0
        (TopCat.of ((Set.range e)ᶜ : Set EuclideanThree)) ≅
      singularCohomology (TopCat.of (alexanderDualityCompactum e)) 2 := by
  let X := ((Set.range e)ᶜ : Set EuclideanThree)
  let _ : LocallyPathConnectedSpace X :=
    (isCompact_range he.contMDiff.continuous).isClosed.isOpen_compl.locallyPathConnectedSpace
  exact
    reducedSingularH0IsoIntOfZerothHomotopyEquiv (TopCat.of X)
        (connectedComponentsEquivZerothHomotopy.symm.trans hcomponents) ≪≫
      hsphere.symm ≪≫
      (alexanderDualityCompactumCohomologyIsoSphereTwoSumPUnit e he).symm

theorem specializedAlexanderDuality_of_componentCount
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hcomponents : HasTwoComplementComponents e)
    (hsphere : SphereTwoSumPUnitH2IsInt) :
    SpecializedAlexanderDuality e := by
  obtain ⟨components⟩ := hcomponents
  obtain ⟨sphere⟩ := hsphere
  exact ⟨specializedAlexanderDualityIsoOfComponentCount e he components sphere⟩

theorem hasAlexanderDualityH0Certificate_of_specializedDuality
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hduality : SpecializedAlexanderDuality e)
    (hsphere : SphereTwoSumPUnitH2IsInt) :
    HasAlexanderDualityH0Certificate e :=
  hasAlexanderDualityH0Certificate_of_duality_and_sphereCohomology
    e he hduality hsphere

theorem specializedAlexanderDuality_iff_twoComponents
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hsphere : SphereTwoSumPUnitH2IsInt) :
    SpecializedAlexanderDuality e ↔ HasTwoComplementComponents e := by
  constructor
  · intro hduality
    exact hasTwoComplementComponents_of_alexanderDualityH0Certificate e he
      (hasAlexanderDualityH0Certificate_of_specializedDuality e he hduality hsphere)
  · intro hcomponents
    exact specializedAlexanderDuality_of_componentCount e he hcomponents hsphere

end DifferentialGeometry.Topology.SphereSeparation
