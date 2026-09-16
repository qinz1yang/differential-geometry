import DifferentialGeometry.Topology.Homology.CoveringTransfer

open CategoryTheory CategoryTheory.Limits Simplicial

noncomputable section

universe u v w

namespace DifferentialGeometry.Homology

variable {E E' B B' : TopCat.{u}} (p : E ⟶ B) (q : E' ⟶ B')
  (g : E ⟶ E') (f : B ⟶ B') (hsq : g ≫ q = p ≫ f)

def singularSimplexLiftMap {n : ℕ} (σ : TopCat.toSSet.obj B _⦋n⦌) :
    SingularSimplexLifts p σ →
      SingularSimplexLifts q ((TopCat.toSSet.map f).app _ σ) :=
  fun τ => ⟨(TopCat.toSSet.map g).app _ τ.val, by
    change (TopCat.toSSet.map (g ≫ q)).app _ τ.val = _
    rw [hsq, Functor.map_comp]
    change (TopCat.toSSet.map f).app _ ((TopCat.toSSet.map p).app _ τ.val) = _
    rw [τ.property]⟩

variable (hbij : ∀ b : B, Function.Bijective
  (fun e : p ⁻¹' {b} =>
    (⟨g e, by
      change q (g e.val) = f b
      exact (ConcreteCategory.congr_hom hsq e.val).trans
        (congrArg f (show p e.val = b from e.property))⟩ : q ⁻¹' {f b})))

include hbij

theorem singularSimplexLiftMap_bijective (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    {n : ℕ} (σ : TopCat.toSSet.obj B _⦋n⦌) :
    Function.Bijective (singularSimplexLiftMap p q g f hsq σ) := by
  let D := stdSimplex ℝ (Fin (n + 1))
  let _ : ContractibleSpace D :=
    (convex_stdSimplex ℝ _).contractibleSpace ⟨stdSimplex.barycenter, stdSimplex.barycenter.prop⟩
  let _ : SimplyConnectedSpace D := SimplyConnectedSpace.ofContractible _
  let _ : LocallyPathConnectedSpace D := (convex_stdSimplex ℝ _).locallyPathConnectedSpace
  let z₀ : D := stdSimplex.barycenter
  let s := B.toSSetObjEquiv _ σ
  have hproj (t : SingularSimplexLifts p σ) : p ∘ E.toSSetObjEquiv _ t.val = s :=
    congrArg (fun z => (B.toSSetObjEquiv _ z : D → B)) t.property
  constructor
  · intro τ υ hτυ
    apply Subtype.ext
    apply (E.toSSetObjEquiv _).injective
    apply Topology.Covering.lifts_unique hp
      (f := E.toSSetObjEquiv _ τ.val) (g := E.toSSetObjEquiv _ υ.val)
      (x := z₀)
    · exact (hproj τ).trans (hproj υ).symm
    · have ht := congrFun (hproj τ) z₀
      have hu := congrFun (hproj υ) z₀
      exact congrArg Subtype.val ((hbij (s z₀)).injective
        (a₁ := ⟨E.toSSetObjEquiv _ τ.val z₀, ht⟩)
        (a₂ := ⟨E.toSSetObjEquiv _ υ.val z₀, hu⟩)
        (Subtype.ext (congrArg (fun t => E'.toSSetObjEquiv _ t.val z₀) hτυ)))
  · intro υ
    have hu : q (E'.toSSetObjEquiv _ υ.val z₀) = f (s z₀) := by
      change B'.toSSetObjEquiv _ ((TopCat.toSSet.map q).app _ υ.val) z₀ =
        B'.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ σ) z₀
      rw [υ.property]
    obtain ⟨e, he⟩ := (hbij (s z₀)).surjective ⟨E'.toSSetObjEquiv _ υ.val z₀, hu⟩
    let L := Topology.Covering.continuousMapLiftsEquivFiber hp s z₀
    let τ := L.symm e
    have ht : τ.val z₀ = e.val := congrArg Subtype.val (L.apply_symm_apply e)
    let t : SingularSimplexLifts p σ := ⟨(E.toSSetObjEquiv _).symm τ.val, by
      apply (B.toSSetObjEquiv _).injective
      exact ContinuousMap.ext (congrFun τ.property)⟩
    refine ⟨t, Subtype.ext ?_⟩
    apply (E'.toSSetObjEquiv _).injective
    apply Topology.Covering.lifts_unique hq
      (f := E'.toSSetObjEquiv _ (singularSimplexLiftMap p q g f hsq σ t).val)
      (g := E'.toSSetObjEquiv _ υ.val)
      (x := z₀)
    · have hproj' (t' : SingularSimplexLifts q ((TopCat.toSSet.map f).app _ σ)) :
          q ∘ E'.toSSetObjEquiv _ t'.val = B'.toSSetObjEquiv _ ((TopCat.toSSet.map f).app _ σ) := by
        exact congrArg (fun z => (B'.toSSetObjEquiv _ z : D → B')) t'.property
      exact (hproj' _).trans (hproj' υ).symm
    · exact (congrArg g ht).trans (congrArg Subtype.val he)

variable {C : Type w} [Category.{v} C] [Preadditive C] [HasCoproducts.{u} C]

theorem singularTransferMap_naturality (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (hfinP : ∀ b : B, (p ⁻¹' {b}).Finite) (hfinQ : ∀ b : B', (q ⁻¹' {b}).Finite)
    (A : C) (n : ℕ) :
    singularTransferMap p hp hfinP A n ≫ (SSet.chainComplexMap (TopCat.toSSet.map g) A).f n =
      (SSet.chainComplexMap (TopCat.toSSet.map f) A).f n ≫ singularTransferMap q hq hfinQ A n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  let _ := finite_singularSimplex_lifts p hp hfinP σ
  let _ : Fintype (SingularSimplexLifts p σ) := Fintype.ofFinite _
  let _ := finite_singularSimplex_lifts q hq hfinQ ((TopCat.toSSet.map f).app _ σ)
  let _ : Fintype (SingularSimplexLifts q ((TopCat.toSSet.map f).app _ σ)) := Fintype.ofFinite _
  calc
    (TopCat.toSSet.obj B).ιChainComplex σ ≫ singularTransferMap p hp hfinP A n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map g) A).f n =
        ∑ τ : SingularSimplexLifts p σ, (TopCat.toSSet.obj E).ιChainComplex τ.val ≫
          (SSet.chainComplexMap (TopCat.toSSet.map g) A).f n := by
      rw [← Category.assoc, ι_singularTransferMap, finsum_eq_sum_of_fintype, Preadditive.sum_comp]
    _ = ∑ τ : SingularSimplexLifts p σ,
        (TopCat.toSSet.obj E').ιChainComplex ((TopCat.toSSet.map g).app _ τ.val) := by
      simp only [SSet.ι_chainComplexMap_f]
    _ = ∑ υ : SingularSimplexLifts q ((TopCat.toSSet.map f).app _ σ),
        (TopCat.toSSet.obj E').ιChainComplex υ.val :=
      (singularSimplexLiftMap_bijective p q g f hsq hbij hp hq σ).sum_comp
        (fun υ => (TopCat.toSSet.obj E').ιChainComplex (R := A) υ.val)
    _ = (TopCat.toSSet.obj B).ιChainComplex σ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) A).f n ≫ singularTransferMap q hq hfinQ A n := by
      rw [← Category.assoc, SSet.ι_chainComplexMap_f, ι_singularTransferMap, finsum_eq_sum_of_fintype]

theorem singularTransfer_naturality (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (hfinP : ∀ b : B, (p ⁻¹' {b}).Finite) (hfinQ : ∀ b : B', (q ⁻¹' {b}).Finite) (A : C) :
    singularTransfer p hp hfinP A ≫ SSet.chainComplexMap (TopCat.toSSet.map g) A =
      SSet.chainComplexMap (TopCat.toSSet.map f) A ≫ singularTransfer q hq hfinQ A := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact singularTransferMap_naturality p q g f hsq hbij hp hq hfinP hfinQ A n

end DifferentialGeometry.Homology
