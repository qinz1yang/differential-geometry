import DifferentialGeometry.Topology.Homology.Relative.Basic
import Mathlib.Algebra.Homology.HomologySequenceLemmas



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap

universe u

namespace DifferentialGeometry.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]


theorem integralSingularChainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    integralSingularChainMap (g.comp f) = integralSingularChainMap f ≫ integralSingularChainMap g :=
  ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map_comp
    (TopCat.ofHom f) (TopCat.ofHom g)


def singularPairRestriction (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) : C(A, B) :=
  ⟨fun x => ⟨f x.val, hf x.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩


theorem integralSingularChainMap_pair_square (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralSingularChainMap (singularSubspaceInclusion A) ≫ integralSingularChainMap f =
      integralSingularChainMap (singularPairRestriction f hf) ≫
        integralSingularChainMap (singularSubspaceInclusion B) := by
  rw [← integralSingularChainMap_comp, ← integralSingularChainMap_comp]
  rfl


def integralRelativeChainMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeChains A ⟶ integralRelativeChains B :=
  cokernel.map _ _ (integralSingularChainMap (singularPairRestriction f hf))
    (integralSingularChainMap f) (integralSingularChainMap_pair_square f hf)


def integralRelativeSequenceMap (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeChainSequence A ⟶ integralRelativeChainSequence B where
  τ₁ := integralSingularChainMap (singularPairRestriction f hf)
  τ₂ := integralSingularChainMap f
  τ₃ := integralRelativeChainMap f hf
  comm₁₂ := (integralSingularChainMap_pair_square f hf).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm


def integralRelativeHomologyMap (n : ℕ) (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    integralRelativeHomology n A →ₗ[ℤ] integralRelativeHomology n B :=
  (HomologicalComplex.homologyMap (integralRelativeChainMap f hf) n).hom


theorem integralAbsoluteToRelative_natural (n : ℕ) (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    (integralAbsoluteToRelative n B).comp (integralSingularHomologyMap n f) =
      (integralRelativeHomologyMap n f hf).comp (integralAbsoluteToRelative n A) := by
  have h := congrArg (fun k => HomologicalComplex.homologyMap k n)
    (integralRelativeSequenceMap f hf).comm₂₃
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact congrArg ModuleCat.Hom.hom h



theorem integralRelativeConnecting_natural (n : ℕ) (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    (integralSingularHomologyMap n (singularPairRestriction f hf)).comp (integralRelativeConnecting n A) =
      (integralRelativeConnecting n B).comp (integralRelativeHomologyMap (n + 1) f hf) := by
  exact congrArg ModuleCat.Hom.hom
    (HomologicalComplex.HomologySequence.δ_naturality (integralRelativeSequenceMap f hf)
      (integralRelativeChainSequence_shortExact A) (integralRelativeChainSequence_shortExact B)
        (n + 1) n (by simp))

end DifferentialGeometry.Topology
