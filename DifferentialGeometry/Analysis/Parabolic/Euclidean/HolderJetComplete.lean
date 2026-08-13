import DifferentialGeometry.Analysis.Parabolic.Euclidean.HolderPath
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Pi
noncomputable section

open Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev JetValue (j : ℕ) :=
  ContinuousMultilinearMap ℝ (fun _ : Fin j => V) F

abbrev ParHolderJet (τ : ℝ) :=
  ((Set.Icc (0 : ℝ) τ × V) →ᵇ (JetValue (V := V) (F := F) 0)) ×
    (((Set.Icc (0 : ℝ) τ × V) →ᵇ (JetValue (V := V) (F := F) 1)) ×
      ((Set.Icc (0 : ℝ) τ × V) →ᵇ (JetValue (V := V) (F := F) 2)))
abbrev FinHolderJet (ι : Type*) (τ : ℝ) :=
  ι → ParHolderJet (V := V) (F := F) τ

private theorem jet2_eval_cont {τ : ℝ} {z : Set.Icc (0 : ℝ) τ × V} :
    Continuous (fun J : ParHolderJet (V := V) (F := F) τ => J.2.2 z) := by
  exact (BoundedContinuousFunction.evalCLM ℝ z).continuous.comp
    (continuous_snd.comp continuous_snd)

def FinHolderSet (ι : Type*) [Fintype ι]
    (τ : ℝ) (R Cspace Ctime : ℝ≥0) :
    Set (FinHolderJet (V := V) (F := F) ι τ) :=
  {J | dist J 0 ≤ R ∧
    (∀ i t, HolderWith Cspace (1 / 2 : ℝ≥0)
      (fun x : V => (J i).2.2 (t, x))) ∧
    ∀ i x, HolderWith Ctime (1 / 4 : ℝ≥0)
      (fun t : Set.Icc (0 : ℝ) τ => (J i).2.2 (t, x))}

theorem finHolder_closed
    (ι : Type*) [Fintype ι] (τ : ℝ) (R Cspace Ctime : ℝ≥0) :
    IsClosed (FinHolderSet (V := V) (F := F) ι τ R Cspace Ctime) := by
  refine IsSeqClosed.isClosed ?_
  intro u J hu hlim
  have hR : dist J 0 ≤ (R : ℝ) := by
    have hdist : Tendsto (fun n => dist (u n) 0) atTop (𝓝 (dist J 0)) :=
      hlim.dist tendsto_const_nhds
    exact le_of_tendsto hdist
      (Eventually.of_forall (fun n => (hu n).1))
  refine ⟨hR, ?_, ?_⟩
  · intro i t x y
    have hx : Tendsto (fun n => (u n i).2.2 (t, x)) atTop
        (𝓝 ((J i).2.2 (t, x))) := by
      have hc : Continuous
          (fun A : FinHolderJet (V := V) (F := F) ι τ =>
            (A i).2.2 (t, x)) :=
        (jet2_eval_cont (V := V) (F := F)).comp (continuous_apply i)
      exact (hc.tendsto J).comp hlim
    have hy : Tendsto (fun n => (u n i).2.2 (t, y)) atTop
        (𝓝 ((J i).2.2 (t, y))) := by
      have hc : Continuous
          (fun A : FinHolderJet (V := V) (F := F) ι τ =>
            (A i).2.2 (t, y)) :=
        (jet2_eval_cont (V := V) (F := F)).comp (continuous_apply i)
      exact (hc.tendsto J).comp hlim
    exact le_of_tendsto (hx.edist hy)
      (Eventually.of_forall (fun n => (hu n).2.1 i t x y))
  · intro i x t s
    have ht : Tendsto (fun n => (u n i).2.2 (t, x)) atTop
        (𝓝 ((J i).2.2 (t, x))) := by
      have hc : Continuous
          (fun A : FinHolderJet (V := V) (F := F) ι τ =>
            (A i).2.2 (t, x)) :=
        (jet2_eval_cont (V := V) (F := F)).comp (continuous_apply i)
      exact (hc.tendsto J).comp hlim
    have hs : Tendsto (fun n => (u n i).2.2 (s, x)) atTop
        (𝓝 ((J i).2.2 (s, x))) := by
      have hc : Continuous
          (fun A : FinHolderJet (V := V) (F := F) ι τ =>
            (A i).2.2 (s, x)) :=
        (jet2_eval_cont (V := V) (F := F)).comp (continuous_apply i)
      exact (hc.tendsto J).comp hlim
    exact le_of_tendsto (ht.edist hs)
      (Eventually.of_forall (fun n => (hu n).2.2 i x t s))

abbrev FinHolderBall (ι : Type*) [Fintype ι]
    (τ : ℝ) (R Cspace Ctime : ℝ≥0) :=
  FinHolderSet (V := V) (F := F) ι τ R Cspace Ctime

theorem finHolder_complete
    [CompleteSpace F]
    (ι : Type*) [Fintype ι] (τ : ℝ) (R Cspace Ctime : ℝ≥0) :
    CompleteSpace
      (FinHolderBall (V := V) (F := F) ι τ R Cspace Ctime) := by
  letI : ∀ _ : ι, CompleteSpace (ParHolderJet (V := V) (F := F) τ) :=
    fun _ => inferInstance
  exact (finHolder_closed (V := V) (F := F)
    ι τ R Cspace Ctime).isComplete.completeSpace_coe

theorem holderBall_space
    {ι : Type*} [Fintype ι] {τ : ℝ} {R Cspace Ctime : ℝ≥0}
    (J : FinHolderBall (V := V) (F := F) ι τ R Cspace Ctime)
    (i : ι) (t : Set.Icc (0 : ℝ) τ) :
    HolderWith Cspace (1 / 2 : ℝ≥0)
      (fun x : V => (J.1 i).2.2 (t, x)) :=
  J.2.2.1 i t

theorem holderBall_time
    {ι : Type*} [Fintype ι] {τ : ℝ} {R Cspace Ctime : ℝ≥0}
    (J : FinHolderBall (V := V) (F := F) ι τ R Cspace Ctime)
    (i : ι) (x : V) :
    HolderWith Ctime (1 / 4 : ℝ≥0)
      (fun t : Set.Icc (0 : ℝ) τ => (J.1 i).2.2 (t, x)) :=
  J.2.2.2 i x

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

theorem fixed_jet_realizes
    {ι : Type*} [Fintype ι] {τ : ℝ}
    (Φ : FinHolderJet (V := V) (F := F) ι τ →
      FinHolderJet (V := V) (F := F) ι τ)
    (real : FinHolderJet (V := V) (F := F) ι τ →
      ι → ℝ → V → F)
    (hreal : ∀ J, FinJetRealizes (V := V) (F := F) (Φ J) (real J))
    {J : FinHolderJet (V := V) (F := F) ι τ} (hfix : Φ J = J) :
    FinJetRealizes (V := V) (F := F) J (real J) := by
  simpa only [hfix] using hreal J
end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry
