import DifferentialGeometry.Topology.Quotient.Cardinality
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Data.Set.Card

noncomputable section

open Set Function

namespace DifferentialGeometry.Topology

universe u v w z

private theorem exists_continuous_factor_of_compact
    {A : Type u} {M : Type v} {Q : Type w}
    [TopologicalSpace A] [CompactSpace A] [TopologicalSpace M] [T2Space M]
    [TopologicalSpace Q] (f : A → M) (hf : Continuous f) (hs : Surjective f)
    (g : A → Q) (hg : Continuous g)
    (hcompat : ∀ a b, f a = f b → g a = g b) :
    ∃ k : M → Q, Continuous k ∧ ∀ a, k (f a) = g a := by
  let k : M → Q := g ∘ Function.surjInv hs
  have heq (a : A) : k (f a) = g a :=
    hcompat _ a (Function.surjInv_eq hs (f a))
  refine ⟨k, ?_, heq⟩
  apply (hf.isClosedMap.isQuotientMap hf hs).continuous_iff.mpr
  exact hg.congr (fun a => (heq a).symm)

private theorem card_pair_quotient_le_card_connectedComponents_of_compact_cover
    {K : Type u} {M : Type v} {I : Type w} {B : I → Type z}
    [TopologicalSpace K] [CompactSpace K] [LocallyConnectedSpace K]
    [TopologicalSpace M] [T2Space M] [Finite (ConnectedComponents M)] [Finite I]
    [∀ i, TopologicalSpace (B i)] [∀ i, CompactSpace (B i)]
    (j : K → M) (hj : Continuous j) (hj_inj : Injective j)
    (f : ∀ i, B i → M) (hf : ∀ i, Continuous (f i))
    (ha hb : I → ConnectedComponents K)
    (hcover : Surjective (Sum.elim j (fun b : Σ i, B i => f b.1 b.2)))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (hattach : ∀ i x y, j x = f i y → ConnectedComponents.mk x = ha i ∨
      ConnectedComponents.mk x = hb i) :
    Nat.card (Quot (fun x y : ConnectedComponents K => ∃ i, x = ha i ∧ y = hb i)) ≤
      Nat.card (ConnectedComponents M) := by
  classical
  let r : ConnectedComponents K → ConnectedComponents K → Prop :=
    fun x y => ∃ i, x = ha i ∧ y = hb i
  let Q := Quot r
  let _ : TopologicalSpace Q := ⊥
  let _ : DiscreteTopology Q := ⟨rfl⟩
  let label : K ⊕ (Σ i, B i) → Q :=
    Sum.elim (fun x => Quot.mk r (ConnectedComponents.mk x))
      (fun b => Quot.mk r (ha b.1))
  have hlabel : Continuous label := by
    apply continuous_sum_dom.mpr
    constructor
    · exact (continuous_of_discreteTopology : Continuous (Quot.mk r)).comp
        ConnectedComponents.continuous_coe
    · apply continuous_sigma
      intro i
      change Continuous (fun _ : B i => Quot.mk r (ha i))
      exact continuous_const
  let cover : K ⊕ (Σ i, B i) → M :=
    Sum.elim j (fun b => f b.1 b.2)
  have hcont : Continuous cover :=
    continuous_sum_dom.mpr ⟨hj, continuous_sigma hf⟩
  have hcompat : ∀ a b, cover a = cover b → label a = label b := by
    intro a b h
    cases a with
    | inl x =>
        cases b with
        | inl y => exact congrArg (fun x => Quot.mk r (ConnectedComponents.mk x)) (hj_inj h)
        | inr b =>
            rcases hattach b.1 x b.2 h with heq | heq
            · exact congrArg (Quot.mk r) heq
            · exact (congrArg (Quot.mk r) heq).trans
                (Quot.sound (show r (ha b.1) (hb b.1) from ⟨b.1, rfl, rfl⟩)).symm
    | inr a =>
        cases b with
        | inl y =>
            rcases hattach a.1 y a.2 h.symm with heq | heq
            · exact (congrArg (Quot.mk r) heq).symm
            · exact (Quot.sound (show r (ha a.1) (hb a.1) from ⟨a.1, rfl, rfl⟩)).trans
                (congrArg (Quot.mk r) heq).symm
        | inr b =>
            have heq : a.1 = b.1 := by
              by_contra hne
              exact Set.disjoint_left.mp (hdisj hne) ⟨a.2, rfl⟩ ⟨b.2, h.symm⟩
            exact congrArg (fun i => Quot.mk r (ha i)) heq
  obtain ⟨k, hk, hkl⟩ := exists_continuous_factor_of_compact cover hcont hcover label hlabel hcompat
  have honto : Surjective hk.connectedComponentsLift := by
    intro z
    induction z using Quot.inductionOn with
    | h c =>
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
        refine ⟨ConnectedComponents.mk (j x), ?_⟩
        exact hkl (Sum.inl x)
  exact Nat.card_le_card_of_surjective hk.connectedComponentsLift honto

theorem card_connectedComponents_le_of_compact_cover
    {K : Type u} {M : Type v} {I : Type w} {B : I → Type z}
    [TopologicalSpace K] [CompactSpace K] [LocallyConnectedSpace K]
    [TopologicalSpace M] [T2Space M] [Finite (ConnectedComponents M)] [Finite I]
    [∀ i, TopologicalSpace (B i)] [∀ i, CompactSpace (B i)]
    (j : K → M) (hj : Continuous j) (hj_inj : Injective j)
    (f : ∀ i, B i → M) (hf : ∀ i, Continuous (f i))
    (ha hb : I → ConnectedComponents K)
    (hcover : Surjective (Sum.elim j (fun b : Σ i, B i => f b.1 b.2)))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (hattach : ∀ i x y, j x = f i y → ConnectedComponents.mk x = ha i ∨
      ConnectedComponents.mk x = hb i) :
    Nat.card (ConnectedComponents K) ≤ Nat.card (ConnectedComponents M) + Nat.card I := by
  have hquot := card_pair_quotient_le_card_connectedComponents_of_compact_cover
    j hj hj_inj f hf ha hb hcover hdisj hattach
  exact (Nat.card_le_card_quot_add_card ha hb).trans (Nat.add_le_add_right hquot _)

end DifferentialGeometry.Topology
