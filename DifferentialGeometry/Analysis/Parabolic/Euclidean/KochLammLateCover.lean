import DifferentialGeometry.Analysis.Parabolic.Euclidean.KochLammLatePiece

/-!
# Finite-cover late Koch--Lamm estimate

This file sums the one-piece terminal estimate over an arbitrary finite ball
cover.  The proof inductively splits the selected spatial set into the part in
one ball and its complement, so overlaps in the supplied cover never cause
double counting.  The quantitative cover itself remains a separate input.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [Nontrivial V] in
/-- Terminal product measure is additive on disjoint measurable spatial
pieces. -/
theorem klTail_union {R : ℝ} {S U : Set V} (hSU : Disjoint S U)
    (hUm : MeasurableSet U) :
    klTailMeasure (V := V) R (S ∪ U) =
      klTailMeasure (V := V) R S + klTailMeasure (V := V) R U := by
  unfold klTailMeasure
  rw [Measure.restrict_union hSU hUm, Measure.prod_add]

omit [CompleteSpace F] in
/-- The heat-kernel/source product is integrable on every selected piece
contained in one late source cylinder. -/
theorem klLatePiece_int {T R : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x c : V)
    (hR : 0 < R) (hRT : R ^ 2 ≤ T) {S : Set V}
    (hS : S ⊆ Metric.ball c R) :
    Integrable (fun z : ℝ × V ↦ klTermKernel (R ^ 2) x z • f z)
      (klTailMeasure (V := V) R S) := by
  let μ := klTailMeasure (V := V) R S
  have hk : MemLp (klTermKernel (R ^ 2) x)
      (ENNReal.ofReal (klQDual V)) μ :=
    (klTermKernel_memLp (V := V) (sq_pos_of_pos hR) x).mono_measure
      (klTailTerm_le (V := V) R S)
  have hf : MemLp f (ENNReal.ofReal (klQReal V)) μ := by
    simpa only [klQReal_ofReal] using
      (klPieceSrc_mem (V := V) h c hR hRT hS)
  letI : ENNReal.HolderConjugate
      (ENNReal.ofReal (klQDual V)) (ENNReal.ofReal (klQReal V)) :=
    (klQ_holder (V := V)).ennrealOfReal
  exact memLp_one_iff_integrable.mp (hf.smul hk)

omit [CompleteSpace F] in
/-- Integrability and norm bound supplied by any finite radius-`R` ball cover
of a measurable terminal spatial set. -/
theorem klLateCover_est {T R k : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    (s : Finset V) {S : Set V} (hSm : MeasurableSet S)
    (hcover : S ⊆ ⋃ c ∈ s, Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    Integrable (fun z : ℝ × V ↦ klTermKernel (R ^ 2) x z • f z)
        (klTailMeasure (V := V) R S) ∧
      ‖klLatePiece0 R f x S‖ ≤
        (s.card : ℝ) *
          (Real.exp (-(k ^ 2) / 4) * (klLateTailC V * (A_q : ℝ))) := by
  classical
  let D : ℝ :=
    Real.exp (-(k ^ 2) / 4) * (klLateTailC V * (A_q : ℝ))
  induction s using Finset.induction_on generalizing S with
  | empty =>
      have hS0 : S = ∅ := by
        simpa using hcover
      subst S
      constructor <;> simp [klTailMeasure, klLatePiece0]
  | @insert c s hc ih =>
      let S₀ : Set V := S ∩ Metric.ball c R
      let S₁ : Set V := S \ Metric.ball c R
      have hS₀m : MeasurableSet S₀ :=
        hSm.inter Metric.isOpen_ball.measurableSet
      have hS₁m : MeasurableSet S₁ :=
        hSm.diff Metric.isOpen_ball.measurableSet
      have hdisj : Disjoint S₀ S₁ := by
        apply Set.disjoint_left.mpr
        intro y hy₀ hy₁
        have hy₀' : y ∈ S ∧ y ∈ Metric.ball c R := by
          simpa only [S₀, Set.mem_inter_iff] using hy₀
        have hy₁' : y ∈ S ∧ y ∉ Metric.ball c R := by
          simpa only [S₁, Set.mem_diff] using hy₁
        exact hy₁'.2 hy₀'.2
      have hsplit : S₀ ∪ S₁ = S := by
        ext y
        simp only [S₀, S₁, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
        tauto
      have hS₀ball : S₀ ⊆ Metric.ball c R := by
        intro y hy
        exact hy.2
      have hfar₀ : ∀ y ∈ S₀, k * R ≤ ‖x - y‖ := by
        intro y hy
        exact hfar y hy.1
      have hcover' : S ⊆
          Metric.ball c R ∪ ⋃ d ∈ s, Metric.ball d R := by
        simpa only [Finset.set_biUnion_insert] using hcover
      have hcover₁ : S₁ ⊆ ⋃ d ∈ s, Metric.ball d R := by
        intro y hy
        have hy' : y ∈ S ∧ y ∉ Metric.ball c R := by
          simpa only [S₁, Set.mem_diff] using hy
        exact (hcover' hy'.1).resolve_left hy'.2
      have hfar₁ : ∀ y ∈ S₁, k * R ≤ ‖x - y‖ := by
        intro y hy
        have hy' : y ∈ S := by
          exact hy.1
        exact hfar y hy'
      have hint₀ := klLatePiece_int (V := V) h x c hR hRT hS₀ball
      obtain ⟨hint₁, hnorm₁⟩ := ih hS₁m hcover₁ hfar₁
      have hnorm₀ : ‖klLatePiece0 R f x S₀‖ ≤ D := by
        simpa only [D] using
          (klLatePiece_norm (V := V) h x c hR hk hRT
            hS₀m hS₀ball hfar₀)
      have hμ : klTailMeasure (V := V) R S =
          klTailMeasure (V := V) R S₀ + klTailMeasure (V := V) R S₁ := by
        rw [← hsplit]
        exact klTail_union (V := V) hdisj hS₁m
      have hint : Integrable
          (fun z : ℝ × V ↦ klTermKernel (R ^ 2) x z • f z)
          (klTailMeasure (V := V) R S) := by
        rw [hμ]
        exact hint₀.add_measure hint₁
      have hpiece : klLatePiece0 R f x S =
          klLatePiece0 R f x S₀ + klLatePiece0 R f x S₁ := by
        unfold klLatePiece0
        rw [hμ, integral_add_measure hint₀ hint₁]
      refine ⟨hint, ?_⟩
      rw [hpiece]
      calc
        ‖klLatePiece0 R f x S₀ + klLatePiece0 R f x S₁‖ ≤
            ‖klLatePiece0 R f x S₀‖ + ‖klLatePiece0 R f x S₁‖ :=
          norm_add_le _ _
        _ ≤ D + (s.card : ℝ) * D := add_le_add hnorm₀ hnorm₁
        _ = ((insert c s).card : ℝ) * D := by
          rw [Finset.card_insert_of_notMem hc]
          norm_num
          ring

omit [CompleteSpace F] in
/-- Norm-only form of the finite-cover estimate. -/
theorem klLateCover_norm {T R k : ℝ} {A₁ A_q : ℝ≥0}
    {f : ℝ × V → F} (h : KLSource0 T A₁ A_q f) (x : V)
    (hR : 0 < R) (hk : 0 ≤ k) (hRT : R ^ 2 ≤ T)
    (s : Finset V) {S : Set V} (hSm : MeasurableSet S)
    (hcover : S ⊆ ⋃ c ∈ s, Metric.ball c R)
    (hfar : ∀ y ∈ S, k * R ≤ ‖x - y‖) :
    ‖klLatePiece0 R f x S‖ ≤
      (s.card : ℝ) *
        (Real.exp (-(k ^ 2) / 4) * (klLateTailC V * (A_q : ℝ))) :=
  (klLateCover_est (V := V) h x hR hk hRT s hSm hcover hfar).2

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
