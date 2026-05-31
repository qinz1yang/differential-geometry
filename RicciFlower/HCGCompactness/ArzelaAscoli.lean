import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.UniformSpace.Real

set_option autoImplicit false

/-!
# Sequential Arzela-Ascoli For Compact Convergence

This file packages Mathlib's set-compactness form of Arzela-Ascoli into the
sequential form used in MSM135 Lemma 3.14: an equicontinuous, pointwise bounded
sequence of real-valued continuous maps on a locally compact sigma-compact
Hausdorff space has a subsequence converging uniformly on compact sets.
-/

namespace RicciFlower
namespace HCGCompactness

open Filter Set Topology
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
  [SigmaCompactSpace X] [T2Space X]

/-- Bundled compact-open version of MSM135 Lemma 3.14.

This is the sequential extraction statement before translating compact-open
convergence into uniform convergence on each compact subset. -/
theorem arzelaAscoli_subseq_tendsto
    (f : Nat -> C(X, Real))
    (hequi : Equicontinuous (fun k => (f k : X -> Real)))
    (hbdd : forall x : X, BddAbove (Set.range fun k => |f k x|)) :
    exists (phi : Nat -> Nat) (g : C(X, Real)),
      StrictMono phi ∧ Tendsto (fun n => f (phi n)) atTop (𝓝 g) := by
  classical
  haveI : WeaklyLocallyCompactSpace X := inferInstance
  haveI : CompactlyCoherentSpace X := inferInstance
  have hclosedEmbedding :
      IsClosedEmbedding
        (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
          (fun g : C(X, Real) => (g : X -> Real))) := by
    refine ⟨?_, ?_⟩
    · simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using
        (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
          (α := X) (β := Real)).isEmbedding
    · rw [show
          Set.range
              (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
                (fun g : C(X, Real) => (g : X -> Real))) =
            {g : UniformOnFun X Real {K : Set X | IsCompact K} |
              Continuous (UniformOnFun.toFun {K : Set X | IsCompact K} g)} by
          simpa [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using
            (ContinuousMap.range_toUniformOnFunIsCompact (α := X) (β := Real))]
      exact UniformOnFun.isClosed_setOf_continuous
        (β := Real) (𝔖 := {K : Set X | IsCompact K})
        CompactlyCoherentSpace.isCoherentWith
  have hEq :
      forall K : Set X, K ∈ ({K : Set X | IsCompact K}) ->
        EquicontinuousOn
          ((fun g : C(X, Real) => (g : X -> Real)) ∘
            ((↑) : {g : C(X, Real) // g ∈ Set.range f} -> C(X, Real))) K := by
    intro K _hK
    let idx : {g : C(X, Real) // g ∈ Set.range f} -> Nat :=
      fun g => Classical.choose g.2
    have hidx :
        forall g : {g : C(X, Real) // g ∈ Set.range f}, f (idx g) = g.1 :=
      fun g => Classical.choose_spec g.2
    have hglobal :
        Equicontinuous (fun g : {g : C(X, Real) // g ∈ Set.range f} =>
          (g.1 : X -> Real)) := by
      have hsub := hequi.comp idx
      have hfun :
          ((fun k : Nat => (f k : X -> Real)) ∘ idx) =
            (fun g : {g : C(X, Real) // g ∈ Set.range f} => (g.1 : X -> Real)) := by
        funext g x
        change f (idx g) x = g.1 x
        rw [hidx g]
      simpa [hfun] using hsub
    simpa [Function.comp_def] using hglobal.equicontinuousOn K
  have hPoint :
      forall K : Set X, K ∈ ({K : Set X | IsCompact K}) ->
        forall x : X, x ∈ K ->
        exists Q : Set Real, IsCompact Q ∧
          forall i : C(X, Real), i ∈ (Set.range f : Set C(X, Real)) ->
            ((fun g : C(X, Real) => (g : X -> Real)) i) x ∈ Q := by
    intro _K _hK x _hx
    rcases hbdd x with ⟨M, hM⟩
    refine ⟨Set.Icc (-M) M, isCompact_Icc, ?_⟩
    intro i hi
    rcases hi with ⟨k, rfl⟩
    have hAbs : |f k x| <= M := hM ⟨k, rfl⟩
    constructor
    · exact le_trans (neg_le_neg hAbs) (neg_abs_le (f k x))
    · exact le_trans (le_abs_self (f k x)) hAbs
  have hcompact : IsCompact (closure (Set.range f : Set C(X, Real))) := by
    exact
      ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
        (X := X) (α := Real) (ι := C(X, Real))
        (𝔖 := {K : Set X | IsCompact K})
        (F := fun g : C(X, Real) => (g : X -> Real))
        (fun K hK => hK) hclosedEmbedding
        (s := Set.range f) hEq hPoint
  have hmem : forall n : Nat, f n ∈ closure (Set.range f : Set C(X, Real)) :=
    fun n => subset_closure ⟨n, rfl⟩
  rcases hcompact.tendsto_subseq hmem with ⟨g, _hg, phi, hphi, htendsto⟩
  exact ⟨phi, g, hphi, by simpa [Function.comp_def] using htendsto⟩

/-- MSM135 Lemma 3.14, sequential Arzela-Ascoli as uniform convergence on
compact subsets. -/
theorem arzelaAscoli_subseq_tendstoUniformlyOnCompacts
    (f : Nat -> C(X, Real))
    (hequi : Equicontinuous (fun k => (f k : X -> Real)))
    (hbdd : forall x : X, BddAbove (Set.range fun k => |f k x|)) :
    exists (phi : Nat -> Nat) (g : C(X, Real)),
      StrictMono phi ∧
        forall K : Set X, IsCompact K ->
          TendstoUniformlyOn (fun n => f (phi n)) g atTop K := by
  rcases arzelaAscoli_subseq_tendsto (X := X) f hequi hbdd with
    ⟨phi, g, hphi, htendsto⟩
  exact
    ⟨phi, g, hphi,
      (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp htendsto)⟩

end HCGCompactness
end RicciFlower
