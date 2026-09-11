import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
noncomputable section
open CategoryTheory Simplicial Opposite
namespace DifferentialGeometry.Topology.SimplicialComplex
universe u
variable {ι : Type u} [LinearOrder ι] (K : PreAbstractSimplicialComplex ι)


def orderedNerveSubcomplex : (nerve ι).Subcomplex where
  obj n := {x | Finset.univ.image x.obj ∈ K}
  map {m n} f x hx := by
    apply (K.isRelLowerSet_faces hx).2
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨f.unop.toOrderHom i, Finset.mem_univ _, rfl⟩
    · exact Finset.image_nonempty.mpr Finset.univ_nonempty

def orderedSimplicialSet : SSet.{u} := orderedNerveSubcomplex K


theorem mem_orderedNerveSubcomplex_iff {n : SimplexCategoryᵒᵖ} (x : (nerve ι).obj n) :
    x ∈ (orderedNerveSubcomplex K).obj n ↔ Finset.univ.image x.obj ∈ K := Iff.rfl


theorem orderedSimplicialSet_mem_nonDegenerate_iff {n : ℕ}
    (x : (orderedSimplicialSet K) _⦋n⦌) :
    x ∈ (orderedSimplicialSet K).nonDegenerate n ↔ StrictMono x.val.obj := by
  exact ((orderedNerveSubcomplex K).mem_nonDegenerate_iff x).trans
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono x.val)


theorem card_vertices_nondegenerate {n : ℕ}
    (x : (orderedSimplicialSet K).nonDegenerate n) :
    (Finset.univ.image x.val.val.obj).card = n + 1 := by
  rw [Finset.card_image_of_injective _
    ((orderedSimplicialSet_mem_nonDegenerate_iff K x.val).mp x.prop).injective]
  exact Fintype.card_fin _

def orderedSimplexOfFace {n : ℕ} (s : Finset ι) (hs : s ∈ K) (hn : s.card = n + 1) :
    (orderedSimplicialSet K).nonDegenerate n := by
  let x : ComposableArrows ι n := (s.orderEmbOfFin hn).monotone.functor
  have hx : Finset.univ.image x.obj ∈ K := by
    change Finset.univ.image (s.orderEmbOfFin hn) ∈ K
    rw [Finset.image_orderEmbOfFin_univ]
    exact hs
  refine ⟨⟨x, hx⟩, (orderedSimplicialSet_mem_nonDegenerate_iff K _).mpr ?_⟩
  exact (s.orderEmbOfFin hn).strictMono


@[simp]
theorem vertices_orderedSimplexOfFace {n : ℕ} (s : Finset ι) (hs : s ∈ K)
    (hn : s.card = n + 1) :
    Finset.univ.image (orderedSimplexOfFace K s hs hn).val.val.obj = s :=
  Finset.image_orderEmbOfFin_univ s hn

def orderedNondegenerateFaceEquiv (n : ℕ) :
    (orderedSimplicialSet K).nonDegenerate n ≃ {s : Finset ι // s ∈ K ∧ s.card = n + 1} where
  toFun x := ⟨Finset.univ.image x.val.val.obj, x.val.prop, card_vertices_nondegenerate K x⟩
  invFun s := orderedSimplexOfFace K s.val s.prop.1 s.prop.2
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply nerve.ext_of_isThin
    exact (Finset.orderEmbOfFin_unique (card_vertices_nondegenerate K x)
      (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      ((orderedSimplicialSet_mem_nonDegenerate_iff K x.val).mp x.prop)).symm
  right_inv s := Subtype.ext (vertices_orderedSimplexOfFace K s.val s.prop.1 s.prop.2)


theorem orderedSimplicialSet_hasDimensionLT (d : ℕ) (hd : ∀ s ∈ K, s.card ≤ d) :
    (orderedSimplicialSet K).HasDimensionLT d where
  degenerate_eq_top n hn := by
    ext x
    simp only [SSet.mem_degenerate_iff_notMem_nonDegenerate, Set.top_eq_univ,
      Set.mem_univ, iff_true]
    intro hx
    have hc := card_vertices_nondegenerate K ⟨x, hx⟩
    change (Finset.univ.image x.val.obj).card = n + 1 at hc
    have hbound := hd _ x.prop
    omega

instance finite_orderedSimplicialSet [Finite K.faces] : (orderedSimplicialSet K).Finite := by
  classical
  let S := (Set.toFinite K.faces).toFinset
  let d := S.sup Finset.card
  have hd : ∀ s ∈ K, s.card ≤ d := by
    intro s hs
    exact Finset.le_sup (f := Finset.card) ((Set.toFinite K.faces).mem_toFinset.mpr hs)
  have : (orderedSimplicialSet K).HasDimensionLT d := orderedSimplicialSet_hasDimensionLT K d hd
  apply SSet.finite_of_hasDimensionLT _ d
  intro n _
  have : Finite {s : Finset ι // s ∈ K ∧ s.card = n + 1} :=
    Finite.of_injective (fun s => (⟨s.val, s.prop.1⟩ : K.faces))
      (fun _ _ h => Subtype.ext (congrArg (fun t : K.faces => t.val) h))
  exact Finite.of_equiv _ (orderedNondegenerateFaceEquiv K n).symm

end DifferentialGeometry.Topology.SimplicialComplex
