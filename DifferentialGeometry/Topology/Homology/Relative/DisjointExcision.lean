import DifferentialGeometry.Topology.OpenCover.Disjoint
import DifferentialGeometry.Topology.Homology.Relative.Coproduct
import DifferentialGeometry.Topology.Homology.Relative.Excision

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set Function
namespace DifferentialGeometry.Homology
universe u
variable (X : TopCat.{u}) {ι : Type u} (U : ι → Set X) (t : Set X)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)

private def sigmaInclusion : TopCat.of (Σ i, U i) ⟶ X :=
  TopCat.ofHom ⟨fun q => q.2.val, continuous_sigma_iff.mpr (fun _ => continuous_subtype_val)⟩


def disjointRelativeChainMap :
    relativeChainComplex (TopCat.of (Σ i, U i)) {q : Σ i, U i | q.2.val ∈ t} R ⟶
      relativeChainComplex X t R :=
  relativeChainMap (X := TopCat.of (Σ i, U i)) (Y := X) R (sigmaInclusion X U)
    (s := {q : Σ i, U i | q.2.val ∈ t}) (t := t) (fun _ hx => hx)


theorem quasiIso_disjointRelativeChainMap (hU : ∀ i, IsOpen (U i))
    (hd : Pairwise (Disjoint on U)) (ht : IsOpen t) (hcover : (⋃ i, U i) ∪ t = univ) :
    QuasiIso (disjointRelativeChainMap X U t R) := by
  let V := ⋃ i, U i
  let h := DifferentialGeometry.Topology.disjointOpenUnionHomeomorph U hU hd
  let e := relativeChainIso (X := TopCat.of (Σ i, U i)) (Y := TopCat.of V) R h
    (s := {q : Σ i, U i | q.2.val ∈ t}) (t := {y : V | y.val ∈ t}) (fun _ => Iff.rfl)
  let j : TopCat.of V ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let J := relativeChainMap (X := TopCat.of V) (Y := X) R j (s := {y : V | y.val ∈ t}) (t := t) (fun _ hx => hx)
  have hJ : QuasiIso J := quasiIso_relativeChainMap_of_openCover X V t R (isOpen_iUnion hU) ht hcover
  have heq : disjointRelativeChainMap X U t R = e.hom ≫ J := by
    dsimp only [e, relativeChainIso, J, disjointRelativeChainMap]
    exact relativeChainMap_comp (X := TopCat.of (Σ i, U i)) (Y := TopCat.of V) (Z := X) R
      (TopCat.ofHom ⟨h, h.continuous⟩) (s := {q : Σ i, U i | q.2.val ∈ t})
      (t := {y : V | y.val ∈ t}) (v := t) (fun _ hx => hx) j (fun _ hx => hx)
  rw [heq]
  exact quasiIso_comp e.hom J


def disjointRelativeHomologyIso (hU : ∀ i, IsOpen (U i))
    (hd : Pairwise (Disjoint on U)) (ht : IsOpen t) (hcover : (⋃ i, U i) ∪ t = univ)
    [Finite ι] (n : ℕ) :
    (∐ fun i => relativeHomology (TopCat.of (U i)) {y : U i | y.val ∈ t} R n) ≅
      relativeHomology X t R n := by
  letI := quasiIso_disjointRelativeChainMap X U t R hU hd ht hcover
  exact relativeHomologySigmaIso (fun i => TopCat.of (U i)) (fun i => {y : U i | y.val ∈ t}) R n ≪≫
    isoOfQuasiIsoAt (disjointRelativeChainMap X U t R) n


@[reassoc (attr := simp)]
theorem disjointRelativeHomologyIso_ι_hom (hU : ∀ i, IsOpen (U i))
    (hd : Pairwise (Disjoint on U)) (ht : IsOpen t) (hcover : (⋃ i, U i) ∪ t = univ)
    [Finite ι] (n : ℕ) (i : ι) :
    Sigma.ι (fun i => relativeHomology (TopCat.of (U i)) {y : U i | y.val ∈ t} R n) i ≫
      (disjointRelativeHomologyIso X U t R hU hd ht hcover n).hom =
    relativeHomologyMap (X := TopCat.of (U i)) (Y := X) R
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U i,X)))
      (s := {y : U i | y.val ∈ t}) (t := t) (fun _ hx => hx) n := by
  change _ ≫ (relativeHomologySigmaIso (fun i => TopCat.of (U i)) (fun i => {y : U i | y.val ∈ t}) R n).hom ≫
    HomologicalComplex.homologyMap (disjointRelativeChainMap X U t R) n = _
  apply (relativeHomologySigmaIso_ι_hom_assoc (fun j => TopCat.of (U j))
    (fun j => {y : U j | y.val ∈ t}) R n i
    (HomologicalComplex.homologyMap (disjointRelativeChainMap X U t R) n)).trans
  exact (relativeHomologyMap_comp (X := TopCat.of (U i)) (Y := TopCat.of (Σ j, U j)) (Z := X) R
    (TopCat.sigmaι (fun j => TopCat.of (U j)) i)
    (s := {y : U i | y.val ∈ t}) (t := {q : Σ j, U j | q.2.val ∈ t})
    (v := t) (fun _ hx => hx) (sigmaInclusion X U) (fun _ hx => hx) n).symm
end DifferentialGeometry.Homology
