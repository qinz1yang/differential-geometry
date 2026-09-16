import DifferentialGeometry.Topology.Homology.CoveringTransfer
import DifferentialGeometry.Tensor.LinearAlgebra.Finsupp.FiniteFibers
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

open CategoryTheory CategoryTheory.Limits Simplicial

noncomputable section

universe u v

namespace DifferentialGeometry.Homology

variable {E B : TopCat.{u}} (p : E ⟶ B)

theorem natCard_singularSimplex_lifts (hp : IsCoveringMap p) {n : ℕ}
    (σ : TopCat.toSSet.obj B _⦋n⦌) :
    Nat.card (SingularSimplexLifts p σ) =
      Nat.card (p ⁻¹' {B.toSSetObjEquiv _ σ stdSimplex.barycenter}) := by
  let D := stdSimplex ℝ (Fin (n + 1))
  let _ : ContractibleSpace D :=
    (convex_stdSimplex ℝ _).contractibleSpace ⟨stdSimplex.barycenter, stdSimplex.barycenter.prop⟩
  let _ : SimplyConnectedSpace D := SimplyConnectedSpace.ofContractible _
  let _ : LocallyPathConnectedSpace D := (convex_stdSimplex ℝ _).locallyPathConnectedSpace
  let e : SingularSimplexLifts p σ ≃
      {g : C(D, E) // p ∘ g = B.toSSetObjEquiv _ σ} :=
    Equiv.subtypeEquiv (E.toSSetObjEquiv _) (fun τ => by
      constructor
      · intro h
        rw [← h]
        rfl
      · intro h
        apply (B.toSSetObjEquiv _).injective
        exact ContinuousMap.ext (congrFun h))
  exact Nat.card_congr (e.trans (Topology.Covering.continuousMapLiftsEquivFiber hp
    (B.toSSetObjEquiv _ σ) stdSimplex.barycenter))

private def chainFinsuppIso {R : Type v} [CommRing R] (K : SSet.{u})
    (A : ModuleCat.{u} R) (n : ℕ) :
    (K.chainComplex A).X n ≅ ModuleCat.of R (K _⦋n⦌ →₀ A) :=
  (K.isColimitChainComplexXCofan A n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit R A (K _⦋n⦌))

private theorem ι_chainFinsuppIso {R : Type v} [CommRing R] (K : SSet.{u})
    (A : ModuleCat.{u} R) {n : ℕ} (σ : K _⦋n⦌) :
    K.ιChainComplex σ ≫ (chainFinsuppIso K A n).hom =
      ModuleCat.ofHom (Finsupp.lsingle σ) := by
  exact (K.isColimitChainComplexXCofan A n).comp_coconePointUniqueUpToIso_hom
    (ModuleCat.finsuppCoconeIsColimit R A (K _⦋n⦌)) ⟨σ⟩

private theorem chainComplexMap_f_chainFinsuppIso {R : Type v} [CommRing R]
    {K L : SSet.{u}} (f : K ⟶ L) (A : ModuleCat.{u} R) (n : ℕ) :
    (SSet.chainComplexMap f A).f n ≫ (chainFinsuppIso L A n).hom =
      (chainFinsuppIso K A n).hom ≫ ModuleCat.ofHom (Finsupp.lmapDomain A R (f.app _)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, ι_chainFinsuppIso,
    ← Category.assoc, ι_chainFinsuppIso]
  ext m τ
  simp

private theorem finite_simplex_fiber (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) (n : ℕ) :
    ∀ σ, ((TopCat.toSSet.map p).app (Opposite.op ⦋n⦌) ⁻¹' {σ}).Finite := by
  intro σ
  exact @Set.toFinite _ _ (finite_singularSimplex_lifts p hp hfin σ)

private theorem singularTransferMap_chainFinsuppIso {R : Type v} [CommRing R]
    (hp : IsCoveringMap p) (hfin : ∀ b : B, (p ⁻¹' {b}).Finite)
    (A : ModuleCat.{u} R) (n : ℕ) :
    singularTransferMap p hp hfin A n ≫ (chainFinsuppIso (TopCat.toSSet.obj E) A n).hom =
      (chainFinsuppIso (TopCat.toSSet.obj B) A n).hom ≫
        ModuleCat.ofHom (Finsupp.lcomapDomainOfFiniteFibers
          ((TopCat.toSSet.map p).app (Opposite.op ⦋n⦌)) (finite_simplex_fiber p hp hfin n)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  let _ := finite_singularSimplex_lifts p hp hfin σ
  let _ : Fintype (SingularSimplexLifts p σ) := Fintype.ofFinite _
  rw [← Category.assoc, ι_singularTransferMap, finsum_eq_sum_of_fintype,
    Preadditive.sum_comp]
  simp only [ι_chainFinsuppIso]
  rw [← Category.assoc, ι_chainFinsuppIso]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  change (∑ t : SingularSimplexLifts p σ, Finsupp.single t.val m) =
    Finsupp.lcomapDomainOfFiniteFibers (R := R) ((TopCat.toSSet.map p).app (Opposite.op ⦋n⦌))
      (finite_simplex_fiber p hp hfin n) (Finsupp.single σ m)
  rw [Finsupp.lcomapDomainOfFiniteFibers_single]
  exact (Finset.sum_subtype ((finite_simplex_fiber p hp hfin n σ).toFinset)
    (by intro τ; simp) (fun τ => Finsupp.single τ m)).symm

private theorem transfer_degreewise (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) (hcard : ∀ b : B, Nat.card (p ⁻¹' {b}) = 2)
    (A : ModuleCat.{u} (ZMod 2)) (n : ℕ) :
    Function.Injective (singularTransferMap p hp hfin A n) ∧
      Function.Exact (singularTransferMap p hp hfin A n)
        ((SSet.chainComplexMap (TopCat.toSSet.map p) A).f n) ∧
      Function.Surjective ((SSet.chainComplexMap (TopCat.toSSet.map p) A).f n) := by
  let f := (TopCat.toSSet.map p).app (Opposite.op ⦋n⦌)
  let T := Finsupp.lcomapDomainOfFiniteFibers (R := ZMod 2) (M := A) f
    (finite_simplex_fiber p hp hfin n)
  let P := Finsupp.lmapDomain A (ZMod 2) f
  let eE := (chainFinsuppIso (TopCat.toSSet.obj E) A n).toLinearEquiv
  let eB := (chainFinsuppIso (TopCat.toSSet.obj B) A n).toLinearEquiv
  have hfcard : ∀ σ, Nat.card (f ⁻¹' {σ}) = 2 := by
    intro σ
    exact (natCard_singularSimplex_lifts p hp σ).trans (hcard _)
  have hfsurj : Function.Surjective f := by
    intro σ
    obtain ⟨τ, _, _, _⟩ := Nat.card_eq_two_iff.mp (hfcard σ)
    exact ⟨τ.val, τ.property⟩
  have ht (x) : eE (singularTransferMap p hp hfin A n x) = T (eB x) :=
    ConcreteCategory.congr_hom (singularTransferMap_chainFinsuppIso p hp hfin A n) x
  have hP (x) : eB ((SSet.chainComplexMap (TopCat.toSSet.map p) A).f n x) = P (eE x) :=
    ConcreteCategory.congr_hom (chainComplexMap_f_chainFinsuppIso (TopCat.toSSet.map p) A n) x
  have hTinj : Function.Injective T :=
    Finsupp.lcomapDomainOfFiniteFibers_injective f _ hfsurj
  have hPsurj : Function.Surjective P := Finsupp.mapDomain_surjective hfsurj
  have hex : Function.Exact T P :=
    Finsupp.exact_lcomapDomainOfFiniteFibers_lmapDomain_of_card_fiber_eq_two f _ hfcard
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply eB.injective
    apply hTinj
    rw [← ht, ← ht, hxy]
  · intro x
    constructor
    · intro hx
      have hx' : P (eE x) = 0 := by rw [← hP, hx, map_zero]
      obtain ⟨w, hw⟩ := (hex (eE x)).mp hx'
      refine ⟨eB.symm w, ?_⟩
      apply eE.injective
      rw [ht, eB.apply_symm_apply, hw]
    · rintro ⟨w, rfl⟩
      apply eB.injective
      rw [hP, ht, map_zero]
      exact hex.apply_apply_eq_zero _
  · intro x
    obtain ⟨w, hw⟩ := hPsurj (eB x)
    refine ⟨eE.symm w, ?_⟩
    apply eB.injective
    rw [hP, eE.apply_symm_apply, hw]

theorem singularTransfer_comp_chainComplexMap_eq_zero (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) (hcard : ∀ b : B, Nat.card (p ⁻¹' {b}) = 2)
    (A : ModuleCat.{u} (ZMod 2)) :
    singularTransfer p hp hfin A ≫ SSet.chainComplexMap (TopCat.toSSet.map p) A = 0 := by
  ext n x
  exact (transfer_degreewise p hp hfin hcard A n).2.1.apply_apply_eq_zero x

def singularTransferShortComplex (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) (hcard : ∀ b : B, Nat.card (p ⁻¹' {b}) = 2)
    (A : ModuleCat.{u} (ZMod 2)) :
    ShortComplex (ChainComplex (ModuleCat.{u} (ZMod 2)) ℕ) :=
  ShortComplex.mk (singularTransfer p hp hfin A)
    (SSet.chainComplexMap (TopCat.toSSet.map p) A)
    (singularTransfer_comp_chainComplexMap_eq_zero p hp hfin hcard A)

theorem singularTransferShortComplex_shortExact (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) (hcard : ∀ b : B, Nat.card (p ⁻¹' {b}) = 2)
    (A : ModuleCat.{u} (ZMod 2)) :
    (singularTransferShortComplex p hp hfin hcard A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  obtain ⟨hinj, hex, hsurj⟩ := transfer_degreewise p hp hfin hcard A n
  exact ModuleCat.shortComplex_shortExact _ hex hinj hsurj

end DifferentialGeometry.Homology
