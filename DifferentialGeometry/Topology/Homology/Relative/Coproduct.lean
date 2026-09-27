import DifferentialGeometry.Topology.Homology.Algebra.CokernelCoproduct
import DifferentialGeometry.Topology.Homology.Coproduct
import DifferentialGeometry.Topology.Homology.Relative.Map

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set Topology
namespace DifferentialGeometry.Homology
universe u
variable {ι : Type u} (X : ι → TopCat.{u}) (s : ∀ i, Set (X i))
private def sigmaSubspaceHomeomorph : (Σ i, s i) ≃ₜ {x : Σ i, X i // x.2 ∈ s x.1} where
  toFun x := ⟨⟨x.1,x.2.val⟩,x.2.property⟩
  invFun x := ⟨x.1.1,⟨x.1.2,x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_sigma_iff.mpr
    intro i
    change Continuous (fun x : s i => (⟨i, x.val⟩ : Σ i, X i))
    exact continuous_sigmaMk.comp continuous_subtype_val
  continuous_invFun := by
    have h : IsEmbedding (@Sigma.map ι ι (fun i => ↥(s i)) (fun i => ↥(X i)) id (fun i => Subtype.val)) :=
      (isEmbedding_sigmaMap (σ := fun i => ↥(s i)) (τ := fun i => ↥(X i)) (f₁ := (id : ι → ι)) (f₂ := fun i => (Subtype.val : s i → X i)) Function.injective_id).mpr (fun _ => IsEmbedding.subtypeVal)
    exact h.continuous_iff.mpr continuous_subtype_val

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
private def subspaceSigmaCofan : Cofan (fun i =>
    ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj (TopCat.of (s i))) :=
  Cofan.mk (((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj
    (TopCat.of {x : Σ i, X i | x.2 ∈ s x.1}))
    (fun i => ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map
      (relativeSubspaceMap (X := X i) (Y := TopCat.of (Σ i, X i)) (TopCat.sigmaι X i) (s := s i)
        (t := {x : Σ i, X i | x.2 ∈ s x.1}) (fun _ hx => hx)))

private def subspaceSigmaCofanIsColimit : IsColimit (subspaceSigmaCofan X s R) := by
  let e := ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (Σ i, s i)) (Y := TopCat.of {x : Σ i, X i | x.2 ∈ s x.1}) (sigmaSubspaceHomeomorph X s))
  apply IsColimit.ofIsoColimit (singularChainSigmaCofanIsColimit (fun i => TopCat.of (s i)) R)
    (Cocone.ext (c := singularChainSigmaCofan (fun i => TopCat.of (s i)) R)
      (c' := subspaceSigmaCofan X s R) e ?_)
  rintro ⟨i⟩
  change ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map _ ≫
    ((singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map _ = _
  rw [← Functor.map_comp]
  rfl


def relativeChainSigmaCofan : Cofan (fun i => relativeChainComplex (X i) (s i) R) :=
  Cofan.mk (relativeChainComplex (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ s x.1} R)
    (fun i => relativeChainMap (X := X i) (Y := TopCat.of (Σ i, X i)) R (TopCat.sigmaι X i)
      (s := s i) (t := {x : Σ i, X i | x.2 ∈ s x.1}) (fun _ hx => hx))


def relativeChainSigmaCofanIsColimit : IsColimit (relativeChainSigmaCofan X s R) := by
  let f := fun i => relativeInclusion (X i) (s i) R
  let a := subspaceSigmaCofan X s R
  let b := singularChainSigmaCofan X R
  let F := relativeInclusion (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ s x.1} R
  have hF (i : ι) : a.inj i ≫ F = f i ≫ b.inj i :=
    (relativeInclusion_naturality (X := X i) (Y := TopCat.of (Σ i, X i)) (s := s i) (t := {x : Σ i, X i | x.2 ∈ s x.1}) R (TopCat.sigmaι X i) (fun _ hx => hx)).symm
  exact DifferentialGeometry.CategoryTheory.cokernelCofanIsColimit f a b F hF
    (subspaceSigmaCofanIsColimit X s R) (singularChainSigmaCofanIsColimit X R)


def relativeHomologySigmaCofan (n : ℕ) : Cofan (fun i => relativeHomology (X i) (s i) R n) :=
  Cofan.mk (relativeHomology (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ s x.1} R n)
    (fun i => relativeHomologyMap (X := X i) (Y := TopCat.of (Σ i, X i)) R
      (TopCat.sigmaι X i) (s := s i) (t := {x : Σ i, X i | x.2 ∈ s x.1}) (fun _ hx => hx) n)


def relativeHomologySigmaCofanIsColimit [Finite ι] (n : ℕ) :
    IsColimit (relativeHomologySigmaCofan X s R n) :=
  (Cofan.isColimitMapCoconeEquiv (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) n)
    _ (relativeChainSigmaCofan X s R)) (isColimitOfPreserves _ (relativeChainSigmaCofanIsColimit X s R))


def relativeHomologySigmaIso [Finite ι] (n : ℕ) :
    (∐ fun i => relativeHomology (X i) (s i) R n) ≅
      relativeHomology (TopCat.of (Σ i, X i)) {x : Σ i, X i | x.2 ∈ s x.1} R n :=
  (coproductIsCoproduct _).coconePointUniqueUpToIso (relativeHomologySigmaCofanIsColimit X s R n)


@[reassoc (attr := simp)]
theorem relativeHomologySigmaIso_ι_hom [Finite ι] (n : ℕ) (i : ι) :
    Sigma.ι (fun i => relativeHomology (X i) (s i) R n) i ≫ (relativeHomologySigmaIso X s R n).hom =
      relativeHomologyMap (X := X i) (Y := TopCat.of (Σ i, X i)) R (TopCat.sigmaι X i)
        (s := s i) (t := {x : Σ i, X i | x.2 ∈ s x.1}) (fun _ hx => hx) n :=
  (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom (relativeHomologySigmaCofanIsColimit X s R n) ⟨i⟩

end DifferentialGeometry.Homology
