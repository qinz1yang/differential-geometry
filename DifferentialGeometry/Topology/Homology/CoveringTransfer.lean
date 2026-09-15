import DifferentialGeometry.Topology.Covering.LiftEnumeration
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Algebra.BigOperators.Finprod

open CategoryTheory CategoryTheory.Limits Simplicial

noncomputable section

universe u v w

namespace DifferentialGeometry.Homology

variable {E B : TopCat.{u}} (p : E ⟶ B)

abbrev SingularSimplexLifts {n : ℕ} (σ : TopCat.toSSet.obj B _⦋n⦌) :=
  {τ : TopCat.toSSet.obj E _⦋n⦌ // (TopCat.toSSet.map p).app _ τ = σ}

private def singularSimplexLiftsEquivContinuous {n : ℕ} (σ : TopCat.toSSet.obj B _⦋n⦌) :
    SingularSimplexLifts p σ ≃
      {g : C(stdSimplex ℝ (Fin (n + 1)), E) // p ∘ g = B.toSSetObjEquiv _ σ} :=
  Equiv.subtypeEquiv (E.toSSetObjEquiv _) (fun τ => by
    constructor
    · intro h
      rw [← h]
      rfl
    · intro h
      apply (B.toSSetObjEquiv _).injective
      exact ContinuousMap.ext (congrFun h))

private theorem simplex_contractible (n : ℕ) :
    ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
  (convex_stdSimplex ℝ _).contractibleSpace ⟨stdSimplex.barycenter, stdSimplex.barycenter.prop⟩

theorem finite_singularSimplex_lifts (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) {n : ℕ} (σ : TopCat.toSSet.obj B _⦋n⦌) :
    Finite (SingularSimplexLifts p σ) := by
  let _ := simplex_contractible n
  let _ : SimplyConnectedSpace (stdSimplex ℝ (Fin (n + 1))) :=
    SimplyConnectedSpace.ofContractible _
  let _ := (convex_stdSimplex ℝ (Fin (n + 1))).locallyPathConnectedSpace
  let e := (singularSimplexLiftsEquivContinuous p σ).trans
    (Topology.Covering.continuousMapLiftsEquivFiber hp (B.toSSetObjEquiv _ σ)
      stdSimplex.barycenter)
  let _ := (hfin (B.toSSetObjEquiv _ σ stdSimplex.barycenter)).fintype
  exact Finite.of_equiv _ e.symm

def singularSimplexLiftFace {n : ℕ} (σ : TopCat.toSSet.obj B _⦋n + 1⦌)
    (i : Fin (n + 2)) :
    SingularSimplexLifts p σ → SingularSimplexLifts p ((TopCat.toSSet.obj B).δ i σ) :=
  fun τ => ⟨(TopCat.toSSet.obj E).δ i τ.val, by
    rw [SSet.δ_naturality_apply, τ.property]⟩

theorem singularSimplexLiftFace_bijective (hp : IsCoveringMap p) {n : ℕ}
    (σ : TopCat.toSSet.obj B _⦋n + 1⦌) (i : Fin (n + 2)) :
    Function.Bijective (singularSimplexLiftFace p σ i) := by
  let _ := simplex_contractible (n + 1)
  let _ := simplex_contractible n
  let _ : SimplyConnectedSpace (stdSimplex ℝ (Fin (n + 2))) :=
    SimplyConnectedSpace.ofContractible _
  let _ := (convex_stdSimplex ℝ (Fin (n + 2))).locallyPathConnectedSpace
  let e := ((singularSimplexLiftsEquivContinuous p σ).trans
    (Topology.Covering.liftPrecompEquiv hp (B.toSSetObjEquiv _ σ)
      ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map _⟩)).trans
        (singularSimplexLiftsEquivContinuous p ((TopCat.toSSet.obj B).δ i σ)).symm
  have he : (e : _ → _) = singularSimplexLiftFace p σ i := by
    funext τ
    apply Subtype.ext
    apply (E.toSSetObjEquiv _).injective
    rfl
  rw [← he]
  exact e.bijective

variable {C : Type w} [Category.{v} C] [Preadditive C] [HasCoproducts.{u} C]

def singularTransferMap (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) (A : C) (n : ℕ) :
    ((TopCat.toSSet.obj B).chainComplex A).X n ⟶
      ((TopCat.toSSet.obj E).chainComplex A).X n := by
  let _ (σ : TopCat.toSSet.obj B _⦋n⦌) := finite_singularSimplex_lifts p hp hfin σ
  let _ (σ : TopCat.toSSet.obj B _⦋n⦌) : Fintype (SingularSimplexLifts p σ) := Fintype.ofFinite _
  exact Sigma.desc (fun σ => ∑ τ : SingularSimplexLifts p σ,
    (TopCat.toSSet.obj E).ιChainComplex τ.val)

theorem ι_singularTransferMap (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) (A : C) {n : ℕ}
    (σ : TopCat.toSSet.obj B _⦋n⦌) :
    (TopCat.toSSet.obj B).ιChainComplex σ ≫ singularTransferMap p hp hfin A n =
      ∑ᶠ τ : SingularSimplexLifts p σ, (TopCat.toSSet.obj E).ιChainComplex (R := A) τ.val := by
  let _ (τ : TopCat.toSSet.obj B _⦋n⦌) := finite_singularSimplex_lifts p hp hfin τ
  let _ (τ : TopCat.toSSet.obj B _⦋n⦌) : Fintype (SingularSimplexLifts p τ) := Fintype.ofFinite _
  exact (Sigma.ι_desc (fun τ : TopCat.toSSet.obj B _⦋n⦌ =>
    ∑ lift : SingularSimplexLifts p τ, (TopCat.toSSet.obj E).ιChainComplex (R := A) lift.val) σ).trans
      (finsum_eq_sum_of_fintype _).symm

theorem singularTransferMap_comm (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) (A : C) (n : ℕ) :
    singularTransferMap p hp hfin A (n + 1) ≫ ((TopCat.toSSet.obj E).chainComplex A).d (n + 1) n =
      ((TopCat.toSSet.obj B).chainComplex A).d (n + 1) n ≫ singularTransferMap p hp hfin A n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  let _ := finite_singularSimplex_lifts p hp hfin σ
  let _ : Fintype (SingularSimplexLifts p σ) := Fintype.ofFinite _
  let _ (i : Fin (n + 2)) :=
    finite_singularSimplex_lifts p hp hfin ((TopCat.toSSet.obj B).δ i σ)
  let _ (i : Fin (n + 2)) : Fintype (SingularSimplexLifts p ((TopCat.toSSet.obj B).δ i σ)) :=
    Fintype.ofFinite _
  calc
    (TopCat.toSSet.obj B).ιChainComplex σ ≫ singularTransferMap p hp hfin A (n + 1) ≫
        ((TopCat.toSSet.obj E).chainComplex A).d (n + 1) n =
        (∑ τ : SingularSimplexLifts p σ, (TopCat.toSSet.obj E).ιChainComplex τ.val) ≫
          ((TopCat.toSSet.obj E).chainComplex A).d (n + 1) n := by
      rw [← Category.assoc, ι_singularTransferMap, finsum_eq_sum_of_fintype]
    _ = ∑ τ : SingularSimplexLifts p σ, ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ i.val • (TopCat.toSSet.obj E).ιChainComplex ((TopCat.toSSet.obj E).δ i τ.val) := by
      simp only [Preadditive.sum_comp, SSet.ιChainComplex_d]
    _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ∑ τ : SingularSimplexLifts p σ,
          (TopCat.toSSet.obj E).ιChainComplex ((TopCat.toSSet.obj E).δ i τ.val) := by
      rw [Finset.sum_comm]
      simp only [Finset.smul_sum]
    _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ∑ᶠ τ : SingularSimplexLifts p ((TopCat.toSSet.obj B).δ i σ),
          (TopCat.toSSet.obj E).ιChainComplex τ.val := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [finsum_eq_sum_of_fintype]
      exact (singularSimplexLiftFace_bijective p hp σ i).sum_comp
        (fun τ => (TopCat.toSSet.obj E).ιChainComplex (R := A) τ.val)
    _ = (TopCat.toSSet.obj B).ιChainComplex σ ≫
        ((TopCat.toSSet.obj B).chainComplex A).d (n + 1) n ≫ singularTransferMap p hp hfin A n := by
      rw [← Category.assoc, SSet.ιChainComplex_d]
      simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, ι_singularTransferMap]

def singularTransfer (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) (A : C) :
    (TopCat.toSSet.obj B).chainComplex A ⟶ (TopCat.toSSet.obj E).chainComplex A where
  f := singularTransferMap p hp hfin A
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact singularTransferMap_comm p hp hfin A j

@[simp]
theorem singularTransfer_f (hp : IsCoveringMap p)
    (hfin : ∀ b : B, (p ⁻¹' {b}).Finite) (A : C) (n : ℕ) :
    (singularTransfer p hp hfin A).f n = singularTransferMap p hp hfin A n := rfl

end DifferentialGeometry.Homology
