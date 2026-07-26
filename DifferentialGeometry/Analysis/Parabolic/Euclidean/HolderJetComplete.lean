import DifferentialGeometry.Analysis.Parabolic.Euclidean.HolderPath
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Sequences

/-!
# A complete finite-component parabolic Holder jet carrier

The extended gauges in `HolderPath.lean` are useful estimates, but predicates
on arbitrary functions are not themselves a complete contraction space.  This
file supplies an actual complete topology without adding a global instance.

For each member of a finite chart/component family we keep bounded continuous
fields for spatial jets of orders zero, one, and two on `[0, tau] x V`.  The
ambient topology is the product sup-norm topology.  We restrict to a closed
ball on which the second jet has uniform spatial exponent `1/2` and temporal
exponent `1/4`.  The restriction is closed, hence complete.  A later Duhamel
operator must return realized jets; at a fixed point, realization follows from
the fixed-point equality and does not require treating arbitrary independent
jets as derivatives.
-/

noncomputable section

open Set Filter
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The canonical value type of the `j`-th Fréchet jet. -/
abbrev JetValue (j : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin j => V) F

/-- Bounded continuous spatial jets through order two on a closed time slab.
The product carries its standard sup-norm metric and complete-space structure
when `F` is complete. -/
abbrev ParHolderJet (τ : ℝ) :=
  ((Set.Icc (0 : ℝ) τ × V) →ᵇ JetValue (V := V) (F := F) 0) ×
    (((Set.Icc (0 : ℝ) τ × V) →ᵇ JetValue (V := V) (F := F) 1) ×
      ((Set.Icc (0 : ℝ) τ × V) →ᵇ JetValue (V := V) (F := F) 2))

/-- A finite chart/component family of parabolic jets. -/
abbrev FinHolderJet (ι : Type*) (τ : ℝ) :=
  ι → ParHolderJet (V := V) (F := F) τ

private theorem jet2_eval_cont {τ : ℝ} {z : Set.Icc (0 : ℝ) τ × V} :
    Continuous (fun J : ParHolderJet (V := V) (F := F) τ => J.2.2 z) := by
  exact (BoundedContinuousFunction.evalCLM ℝ z).continuous.comp
    (continuous_snd.comp continuous_snd)

/-- The closed finite-component Holder ball in the product sup-norm jet
space.  `R` controls all three bounded jet fields, while `Cspace` and `Ctime`
control the two parabolic seminorms of the second jet. -/
def FinHolderSet (ι : Type*) [Fintype ι]
    (τ : ℝ) (R Cspace Ctime : ℝ≥0) :
    Set (FinHolderJet (V := V) (F := F) ι τ) :=
  {J | dist J 0 ≤ R ∧
    (∀ i t, HolderWith Cspace (1 / 2 : ℝ≥0)
      (fun x : V => (J i).2.2 (t, x))) ∧
    ∀ i x, HolderWith Ctime (1 / 4 : ℝ≥0)
      (fun t : Set.Icc (0 : ℝ) τ => (J i).2.2 (t, x))}

/-- The finite-component parabolic Holder ball is closed in the explicit
product sup-norm topology. -/
theorem finHolder_closed
    (ι : Type*) [Fintype ι] (τ : ℝ) (R Cspace Ctime : ℝ≥0) :
    IsClosed (FinHolderSet (V := V) (F := F) ι τ R Cspace Ctime) := by
  refine IsSeqClosed.isClosed ?_
  intro u J hu hlim
  have hR : dist J 0 ≤ (R : ℝ) := by
    have hdist : Tendsto (fun n => dist (u n) 0) atTop (𝒩 (dist J 0)) :=
      hlim.dist tendsto_const_nhds
    exact le_of_tendsto hdist
      (Eventually.of_forall (fun n => (hu n).1))
  refine ⟨hR, ?_, ?_⟩
  · intro i t x y
    have hx : Tendsto (fun n => (u n i).2.2 (t, x)) atTop
        (𝒩 ((J i).2.2 (t, x))) := by
      have hc : Continuous
          (fun A : FinHolderJet (V := V) (F := F) ι τ =>
            (A i).2.2 (t, x)) :=
        (jet2_eval_cont (V := V) (F := F)).comp (continuous_apply i)
      exact hc.tendsto.comp hlim
    have hy : Tendsto (fun n => (u n i).2.2 (t, y)) atTop
        (𝒩 ((J i).2.2 (t, y))) := by
      have hc : Continuous
          (fun A : FinHolderJet (V := V) (F := F) ι τ =>
            (A i).2.2 (t, y)) :=
        (jet2_eval_cont (V := V) (F := F)).comp (continuous_apply i)
      exact hc.tendsto.comp hlim
    exact le_of_tendsto (hx.edist hy)
      (Eventually.of_forall (fun n => (hu n).2.1 i t x y))
  · intro i x t s
    have ht : Tendsto (fun n => (u n i).2.2 (t, x)) atTop
        (𝒩 ((J i).2.2 (t, x))) := by
      have hc : Continuous
          (fun A : FinHolderJet (V := V) (F := F) ι τ =>
            (A i).2.2 (t, x)) :=
        (jet2_eval_cont (V := V) (F := F)).comp (continuous_apply i)
      exact hc.tendsto.comp hlim
    have hs : Tendsto (fun n => (u n i).2.2 (s, x)) atTop
        (𝒩 ((J i).2.2 (s, x))) := by
      have hc : Continuous
          (fun A : FinHolderJet (V := V) (F := F) ι τ =>
            (A i).2.2 (s, x)) :=
        (jet2_eval_cont (V := V) (F := F)).comp (continuous_apply i)
      exact hc.tendsto.comp hlim
    exact le_of_tendsto (ht.edist hs)
      (Eventually.of_forall (fun n => (hu n).2.2 i x t s))

/-- The actual contraction carrier: a subtype of the finite product of
bounded continuous jet fields. -/
abbrev FinHolderBall (ι : Type*) [Fintype ι]
    (τ : ℝ) (R Cspace Ctime : ℝ≥0) :=
  FinHolderSet (V := V) (F := F) ι τ R Cspace Ctime

/-- The Holder jet ball is complete in the inherited product sup-norm metric.
This theorem returns the structure for local installation by a fixed-point
consumer; it does not declare a new global instance. -/
theorem finHolder_complete
    [CompleteSpace F]
    (ι : Type*) [Fintype ι] (τ : ℝ) (R Cspace Ctime : ℝ≥0) :
    CompleteSpace
      (FinHolderBall (V := V) (F := F) ι τ R Cspace Ctime) := by
  exact (finHolder_closed (V := V) (F := F)
    ι τ R Cspace Ctime).isComplete.completeSpace_coe

/-- Every member of the complete ball retains the spatial `1/2` Holder bound
for its second jet. -/
theorem holderBall_space
    {ι : Type*} [Fintype ι] {τ : ℝ} {R Cspace Ctime : ℝ≥0}
    (J : FinHolderBall (V := V) (F := F) ι τ R Cspace Ctime)
    (i : ι) (t : Set.Icc (0 : ℝ) τ) :
    HolderWith Cspace (1 / 2 : ℝ≥0)
      (fun x : V => (J.1 i).2.2 (t, x)) :=
  J.2.2.1 i t

/-- Every member of the complete ball retains the temporal `1/4` Holder bound
for its second jet. -/
theorem holderBall_time
    {ι : Type*} [Fintype ι] {τ : ℝ} {R Cspace Ctime : ℝ≥0}
    (J : FinHolderBall (V := V) (F := F) ι τ R Cspace Ctime)
    (i : ι) (x : V) :
    HolderWith Ctime (1 / 4 : ℝ≥0)
      (fun t : Set.Icc (0 : ℝ) τ => (J.1 i).2.2 (t, x)) :=
  J.2.2.2 i x

/-- A finite jet family realizes actual component paths when its three fields
are their genuine iterated Fréchet derivatives and every spatial slice is
twice continuously differentiable. -/
def FinJetRealizes
    {ι : Type*} [Fintype ι] {τ : ℝ}
  (J : FinHolderJet (V := V) (F := F) ι τ)
    (u : ι → ℝ → V → F) : Prop :=
  (∀ i t, ContDiff ℝ 2 (u i t)) ∧
    (∀ i t x, (J i).1 (t, x) =
      iteratedFDeriv ℝ 0 (u i t) x) ∧
    (∀ i t x, (J i).2.1 (t, x) =
      iteratedFDeriv ℝ 1 (u i t) x) ∧
    ∀ i t x, (J i).2.2 (t, x) =
      iteratedFDeriv ℝ 2 (u i t) x

/-- If a jet-valued map always returns realized Duhamel jets, then any fixed
point of that map is realized.  Thus derivative compatibility is recovered
from the fixed-point equation, while completeness is supplied by the closed
independent-jet ball above. -/
theorem fixed_jet_realizes
    {ι : Type*} [Fintype ι] {τ : ℝ}
    (Φ : FinHolderJet (V := V) (F := F) ι τ →
      FinHolderJet (V := V) (F := F) ι τ)
    (real : FinHolderJet (V := V) (F := F) ι τ →
      ι → ℝ → V → F)
    (hreal : ∀ J, FinJetRealizes (V := V) (F := F) (Φ J) (real J))
    {J : FinHolderJet (V := V) (F := F) ι τ} (hfix : Φ J = J) :
    FinJetRealizes (V := V) (F := F) J (real J) := by
  rw [← hfix]
  exact hreal J

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
