import DifferentialGeometry.Topology.Homology.Relative.Reduced
import DifferentialGeometry.Topology.Homology.Relative.Map
import DifferentialGeometry.Topology.Homology.Algebra.AugmentHomology

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped ZeroObject
namespace Poincare.Homology
universe u
variable {X Y : TopCat.{u}} {s : Set X} {t : Set Y}
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

def augmentedRelativeChainMap (f : X ⟶ Y) (hf : Set.MapsTo f s t) :
    augmentedRelativeChainComplex X s R ⟶ augmentedRelativeChainComplex Y t R :=
  Poincare.ChainComplex.augmentMap (by simp) (by simp) (relativeChainMap R f hf)
    (0 : (0 : ModuleCat.{u} k) ⟶ 0) (by simp)


def augmentedRelativeShortComplexMap (f : X ⟶ Y) (hf : Set.MapsTo f s t) :
    augmentedRelativeShortComplex X s R ⟶ augmentedRelativeShortComplex Y t R where
  τ₁ := augmentedSingularChainMap R (relativeSubspaceMap f hf)
  τ₂ := augmentedSingularChainMap R f
  τ₃ := augmentedRelativeChainMap R f hf
  comm₁₂ := by
    apply _root_.HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => change 𝟙 R ≫ 𝟙 R = 𝟙 R ≫ 𝟙 R; rfl
    | succ n => exact congrArg (fun g => g.f n) (relativeInclusion_naturality R f hf).symm
  comm₂₃ := by
    apply _root_.HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero => change 𝟙 R ≫ (0 : R ⟶ 0) = (0 : R ⟶ 0) ≫ 0; simp
    | succ n => exact congrArg (fun g => g.f n) (relativeProjection_chainMap R f hf).symm


@[reassoc]
theorem augmentedRelativeHomologySuccIso_naturality (f : X ⟶ Y) (hf : Set.MapsTo f s t)
    (n : ℕ) :
    _root_.HomologicalComplex.homologyMap (augmentedRelativeChainMap R f hf) (n + 2) ≫
      (augmentedRelativeHomologySuccIso Y t R n).hom =
    (augmentedRelativeHomologySuccIso X s R n).hom ≫ relativeHomologyMap R f hf (n + 1) :=
  Poincare.ChainComplex.augmentHomologySuccIso_naturality (by simp) (by simp)
    (relativeChainMap R f hf) (0 : (0 : ModuleCat.{u} k) ⟶ 0) (by simp) n


@[reassoc]
theorem relativeReducedConnectingIso_naturality [ContractibleSpace X] [ContractibleSpace Y]
    (f : X ⟶ Y) (hf : Set.MapsTo f s t) (n : ℕ) :
    (relativeReducedConnectingIso X s R n).hom ≫
      reducedSingularHomologyMap R (relativeSubspaceMap f hf) n =
    relativeHomologyMap R f hf (n + 1) ≫ (relativeReducedConnectingIso Y t R n).hom := by
  apply (cancel_epi (augmentedRelativeHomologySuccIso X s R n).hom).mp
  rw [augmentedRelativeHomologySuccIso_connecting_assoc,
    ← augmentedRelativeHomologySuccIso_naturality_assoc,
    augmentedRelativeHomologySuccIso_connecting]
  exact _root_.HomologicalComplex.HomologySequence.δ_naturality
    (augmentedRelativeShortComplexMap R f hf)
    (augmentedRelativeShortExact X s R) (augmentedRelativeShortExact Y t R) (n + 2) (n + 1) rfl
end Poincare.Homology
