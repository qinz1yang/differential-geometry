import DifferentialGeometry.Topology.SimplicialSet.RealizationHomology
import DifferentialGeometry.Topology.SimplicialSet.ChainColimits
import DifferentialGeometry.Topology.Homology.Relative.Map
import DifferentialGeometry.Topology.Homology.Algebra.CokernelQuasiIso
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology

universe u

namespace DifferentialGeometry.SSet

variable {A B X Y : _root_.SSet.{u}}


def realizationToRange (f : A ⟶ X) :
    _root_.SSet.toTop.obj A ⟶ TopCat.of (Set.range (_root_.SSet.toTop.map f)) :=
  TopCat.ofHom ⟨fun a ↦ ⟨(_root_.SSet.toTop.map f) a, ⟨a, rfl⟩⟩,
    (_root_.SSet.toTop.map f).hom.continuous.subtype_mk _⟩


@[reassoc (attr := simp)]
theorem realizationToRange_inclusion (f : A ⟶ X) :
    realizationToRange f ≫
      TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C(Set.range (_root_.SSet.toTop.map f), _root_.SSet.toTop.obj X)) =
      _root_.SSet.toTop.map f := rfl


theorem isIso_realizationToRange (f : A ⟶ X) (hf : IsEmbedding (_root_.SSet.toTop.map f)) :
    IsIso (realizationToRange f) := by
  let e : _root_.SSet.toTop.obj A ≅ TopCat.of (Set.range (_root_.SSet.toTop.map f)) :=
    TopCat.isoOfHomeo hf.toHomeomorph
  change IsIso e.hom
  infer_instance

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem relativeRealizationSquare (f : A ⟶ X) :
    _root_.SSet.chainComplexMap f R ≫ realizationChainMap X R =
      (realizationChainMap A R ≫
        ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (realizationToRange f)) ≫
      DifferentialGeometry.Homology.relativeInclusion (_root_.SSet.toTop.obj X)
        (Set.range (_root_.SSet.toTop.map f)) R := by
  rw [realizationChainMap_naturality]
  unfold DifferentialGeometry.Homology.relativeInclusion
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, realizationToRange_inclusion]

def relativeRealizationChainMap (f : A ⟶ X) :
    cokernel (_root_.SSet.chainComplexMap f R) ⟶
      DifferentialGeometry.Homology.relativeChainComplex (_root_.SSet.toTop.obj X)
        (Set.range (_root_.SSet.toTop.map f)) R :=
  cokernel.map (_root_.SSet.chainComplexMap f R)
    (DifferentialGeometry.Homology.relativeInclusion (_root_.SSet.toTop.obj X)
      (Set.range (_root_.SSet.toTop.map f)) R)
    (realizationChainMap A R ≫
      ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (realizationToRange f))
    (realizationChainMap X R) (relativeRealizationSquare R f)

@[reassoc (attr := simp)]
theorem relativeRealizationProjection (f : A ⟶ X) :
    cokernel.π (_root_.SSet.chainComplexMap f R) ≫ relativeRealizationChainMap R f =
      realizationChainMap X R ≫ DifferentialGeometry.Homology.relativeProjection (_root_.SSet.toTop.obj X)
        (Set.range (_root_.SSet.toTop.map f)) R :=
  cokernel.π_desc _ _ _

theorem quasiIso_relativeRealizationChainMap (f : A ⟶ X) [Mono f]
    (hf : IsEmbedding (_root_.SSet.toTop.map f))
    (hA : QuasiIso (realizationChainMap A R)) (hX : QuasiIso (realizationChainMap X R)) :
    QuasiIso (relativeRealizationChainMap R f) := by
  have : Mono (_root_.SSet.chainComplexMap f R) := by
    unfold _root_.SSet.chainComplexMap
    infer_instance
  have : IsIso (realizationToRange f) := isIso_realizationToRange f hf
  have : QuasiIso (realizationChainMap A R) := hA
  unfold relativeRealizationChainMap
  exact DifferentialGeometry.HomologicalComplex.quasiIso_cokernel_map _ _ _ _ _
    (quasiIso_comp (realizationChainMap A R)
      (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (realizationToRange f))) hX

def relativeRealizationShortComplexMap (f : A ⟶ X) :
    DifferentialGeometry.HomologicalComplex.cokernelSequence (_root_.SSet.chainComplexMap f R) ⟶
      DifferentialGeometry.Homology.relativeShortComplex (_root_.SSet.toTop.obj X)
        (Set.range (_root_.SSet.toTop.map f)) R where
  τ₁ := realizationChainMap A R ≫
    ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map (realizationToRange f)
  τ₂ := realizationChainMap X R
  τ₃ := relativeRealizationChainMap R f
  comm₁₂ := (relativeRealizationSquare R f).symm
  comm₂₃ := (relativeRealizationProjection R f).symm

variable {f : A ⟶ X} {g : B ⟶ Y} {a : A ⟶ B} {b : X ⟶ Y}
  (w : f ≫ b = a ≫ g)

include w


theorem simplicialChainSquare :
    _root_.SSet.chainComplexMap f R ≫ _root_.SSet.chainComplexMap b R =
      _root_.SSet.chainComplexMap a R ≫ _root_.SSet.chainComplexMap g R := by
  change (((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map f) ≫
      (((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map b) =
    (((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map a) ≫
      (((_root_.SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).map g)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, w]


def relativeSimplicialChainMap :
    cokernel (_root_.SSet.chainComplexMap f R) ⟶ cokernel (_root_.SSet.chainComplexMap g R) :=
  cokernel.map _ _ (_root_.SSet.chainComplexMap a R) (_root_.SSet.chainComplexMap b R)
    (simplicialChainSquare R w)


@[reassoc (attr := simp)]
theorem relativeSimplicialProjection :
    cokernel.π (_root_.SSet.chainComplexMap f R) ≫ relativeSimplicialChainMap R w =
      _root_.SSet.chainComplexMap b R ≫ cokernel.π (_root_.SSet.chainComplexMap g R) :=
  cokernel.π_desc _ _ _


theorem realizationRange_mapsTo :
    Set.MapsTo (_root_.SSet.toTop.map b) (Set.range (_root_.SSet.toTop.map f))
      (Set.range (_root_.SSet.toTop.map g)) := by
  rintro x ⟨z, rfl⟩
  have hw := congrArg (fun v ↦ _root_.SSet.toTop.map v) w
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hw
  exact ⟨(_root_.SSet.toTop.map a) z, (ConcreteCategory.congr_hom hw z).symm⟩

theorem relativeRealizationChainMap_naturality :
    relativeSimplicialChainMap R w ≫ relativeRealizationChainMap R g =
      relativeRealizationChainMap R f ≫
        DifferentialGeometry.Homology.relativeChainMap R (_root_.SSet.toTop.map b)
          (realizationRange_mapsTo w) := by
  apply (cancel_epi (cokernel.π (_root_.SSet.chainComplexMap f R))).mp
  simp only [relativeSimplicialProjection_assoc, relativeRealizationProjection,
    relativeRealizationProjection_assoc,
    DifferentialGeometry.Homology.relativeProjection_chainMap]
  exact congrArg (fun v ↦ v ≫ DifferentialGeometry.Homology.relativeProjection (_root_.SSet.toTop.obj Y)
      (Set.range (_root_.SSet.toTop.map g)) R) (realizationChainMap_naturality b R)

end DifferentialGeometry.SSet
